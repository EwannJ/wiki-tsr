# Sert toutes les pages du wiki (index.html, en-travaux/index.html, ...) déjà traduites : le navigateur reçoit le HTML final.
# Français = langue d'origine. Autres langues : DeepL, puis cache (mémoire de l'instance, Supabase si configuré, CDN Vercel).
# Indications dans le HTML, sur l'élément qui contient le texte (ex. <a class="nav-link" ...>Formations</a>) :
#   data-context="..."  précise à DeepL le sens de CE texte (ex. data-context="training courses for players, not train sets")
#   data-tr-de="..."    impose la traduction dans une langue (data-tr-en-us, data-tr-pt-br... ; data-tr-en vaut pour EN-US et EN-GB)
# Les textes du menu sont traduits une seule fois par langue puis repris tels quels partout où ils apparaissent (menu, tuiles...) :
# les indications posées sur une entrée du menu suffisent. Elles ne sont jamais envoyées au navigateur.
# Variables d'environnement : DEEPL_API_KEY (obligatoire pour traduire), SUPABASE_URL_TSR + SUPABASE_KEY_TSR (optionnelles, cache durable).
from concurrent.futures import ThreadPoolExecutor
from functools import lru_cache
from http.cookies import SimpleCookie
from http.server import BaseHTTPRequestHandler
from urllib.parse import parse_qs, urlparse
import hashlib
import html
import json
import os
import re
import threading
import time
import unicodedata
import urllib.error
import urllib.parse
import urllib.request

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# OPTION : False = la langue reste visible dans l'URL (?lang=de) et suit les liens internes.
#          (sans ?lang= dans l'URL : langue du navigateur)
#          True  = l'URL reste propre : si ?lang=xx est présent (menu, lien partagé), la langue est mémorisée dans le cookie "lang"
#                  puis ?lang=xx est retiré de l'URL (redirection). Sans cookies, la langue n'est alors pas conservée d'une page à l'autre.
HIDE_LANG_PARAM = True

DEEPL_API_KEY = os.environ.get("DEEPL_API_KEY", "")
# les clés gratuites finissent par ":fx"
_DEEPL_HOST = "https://api-free.deepl.com" if DEEPL_API_KEY.endswith(":fx") else "https://api.deepl.com"
SUPABASE_URL = (os.environ.get("SUPABASE_URL_TSR") or "").rstrip("/")
SUPABASE_KEY = os.environ.get("SUPABASE_KEY_TSR") or ""
_CONTEXT = (
    "Wiki of a French train simulation game on Roblox (Train Simulator Roblox, TSR): trains, roles, "
    "help guides and a community of players. Short texts such as menu entries, buttons and titles are labels, "
    "not sentences: translate them as labels."
)
# le contexte de DeepL n'est pas traduit et n'est pas facturé : il peut être long (limite choisie ici, en caractères)
_CONTEXT_LIMIT = 3000

# ---------------------------------------------------------------- langues

# nom de chaque langue écrit dans sa propre langue (DeepL ne renvoie que des noms en anglais)
_NATIVE = {
    "AR": "العربية", "BG": "Български", "CS": "Čeština", "DA": "Dansk", "DE": "Deutsch", "EL": "Ελληνικά",
    "EN-GB": "English (UK)", "EN-US": "English (US)", "ES": "Español", "ES-419": "Español (Latinoamérica)",
    "ET": "Eesti", "FI": "Suomi", "HE": "עברית", "HU": "Magyar", "ID": "Bahasa Indonesia", "IT": "Italiano",
    "JA": "日本語", "KO": "한국어", "LT": "Lietuvių", "LV": "Latviešu", "NB": "Norsk bokmål", "NL": "Nederlands",
    "PL": "Polski", "PT-BR": "Português (Brasil)", "PT-PT": "Português (Portugal)", "RO": "Română",
    "RU": "Русский", "SK": "Slovenčina", "SL": "Slovenščina", "SV": "Svenska", "TH": "ไทย", "TR": "Türkçe",
    "UK": "Українська", "VI": "Tiếng Việt", "ZH-HANS": "中文 (简体)", "ZH-HANT": "中文 (繁體)",
}
# codes du navigateur / de l'URL -> code DeepL
_ALIASES = {
    "EN": "EN-US", "PT": "PT-PT", "ZH": "ZH-HANS", "ZH-CN": "ZH-HANS", "ZH-SG": "ZH-HANS",
    "ZH-TW": "ZH-HANT", "ZH-HK": "ZH-HANT", "ZH-MO": "ZH-HANT", "NO": "NB", "NN": "NB",
}

_languages_cache = None  # {code: nom anglais}
_languages_failed_at = 0.0
_languages_lock = threading.Lock()


def _languages() -> dict:
    """Langues cibles de DeepL (sans le français), chargées une fois par instance ; liste fixe si DeepL ne répond pas."""
    global _languages_cache, _languages_failed_at
    with _languages_lock:
        if _languages_cache is not None:
            return _languages_cache
        if DEEPL_API_KEY and time.time() - _languages_failed_at > 60:
            req = urllib.request.Request(f"{_DEEPL_HOST}/v2/languages?type=target")
            req.add_header("Authorization", f"DeepL-Auth-Key {DEEPL_API_KEY}")
            try:
                with urllib.request.urlopen(req, timeout=5) as r:
                    rows = json.loads(r.read())
                codes = {row["language"].upper(): row["name"] for row in rows}
                # EN, PT, ZH seuls font doublon avec EN-US, PT-PT, ZH-HANS
                _languages_cache = {c: n for c, n in codes.items()
                                    if c != "FR" and not (c in _ALIASES and _ALIASES[c] in codes)}
                return _languages_cache
            except Exception as e:
                print(f"translate : error 'DeepL languages fetch failed : {e}'")
                _languages_failed_at = time.time()
        return {code: "" for code in _NATIVE}


# liste chargée dès le démarrage de l'instance, en parallèle de la première requête
threading.Thread(target=_languages, daemon=True).start()


def _norm(raw: str) -> str:
    value = (raw or "").strip().upper()
    return _ALIASES.get(value, value)


def _from_accept_language(header: str, supported) -> str:
    prefs = []
    for part in header.split(",")[:20]:
        tag, _, params = part.strip().partition(";")
        q = 1.0
        if params.strip().startswith("q="):
            try:
                q = float(params.strip()[2:])
            except ValueError:
                q = 0.0
        if tag and tag != "*" and q > 0:
            prefs.append((-q, tag))
    for _q, tag in sorted(prefs, key=lambda p: p[0]):
        for candidate in (_norm(tag), _norm(tag.split("-")[0])):
            if candidate == "FR" or candidate in supported:
                return candidate
    return "FR"


def _choose_language(query_lang: str, cookie_lang: str, accept: str) -> tuple:
    """(langue, explicite) : ?lang= prioritaire, puis cookie du menu, puis langue du navigateur."""
    supported = _languages()
    for raw, explicit in ((query_lang, True), (cookie_lang, False)):
        code = _norm(raw)
        if code == "FR" or code in supported:
            return code, explicit
    return _from_accept_language(accept, supported), False


def _sort_key(name: str) -> str:
    return "".join(c for c in unicodedata.normalize("NFKD", name) if not unicodedata.combining(c)).casefold()


def _language_options(active: str) -> str:
    rows = [(code, _NATIVE.get(code) or english, english) for code, english in _languages().items()]
    rows.sort(key=lambda row: _sort_key(row[1]))
    rows.insert(0, ("FR", "Français", "French"))
    return "".join(
        f'<button type="button" class="lang-option" data-lang="{code}" '
        f'data-search="{html.escape(f"{code} {name} {english}".lower(), quote=True)}" role="option" '
        f'aria-selected="{str(code == active).lower()}"><b>{code}</b><span>{html.escape(name)}</span></button>'
        for code, name, english in rows
    )


# ---------------------------------------------------------------- DeepL

def _deepl(texts: list, target: str, as_html: bool, context: str = _CONTEXT):
    """Traduit par lots (le contexte est envoyé avec chaque lot) ; None au moindre échec."""
    batches, batch, size = [], [], 0
    for text in texts:
        if batch and (len(batch) == 50 or size + len(text) > 20000):
            batches.append(batch)
            batch, size = [], 0
        batch.append(text)
        size += len(text)
    if batch:
        batches.append(batch)
    out = []
    for batch in batches:
        data = [("text", t) for t in batch] + [("target_lang", target), ("source_lang", "FR"), ("context", context)]
        if as_html:
            data.append(("tag_handling", "html"))
        req = urllib.request.Request(f"{_DEEPL_HOST}/v2/translate", data=urllib.parse.urlencode(data).encode(), method="POST")
        req.add_header("Authorization", f"DeepL-Auth-Key {DEEPL_API_KEY}")
        try:
            with urllib.request.urlopen(req, timeout=25) as r:
                rows = [row["text"] for row in json.loads(r.read())["translations"]]
        except Exception as e:
            print(f"translate : error 'DeepL translate failed for {target} : {e}'")
            return None
        if len(rows) != len(batch):
            return None
        out.extend(rows)
    return out


# ---------------------------------------------------------------- découpage du HTML

_HIDDEN_RE = re.compile(r"<script\b.*?</script>|<style\b.*?</style>|<!--.*?-->", re.S | re.I)
_TAG_RE = re.compile(r"<(/?)([a-zA-Z][a-zA-Z0-9]*)\b([^>]*?)(/?)>")
_VOID = {"area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "source", "track", "wbr"}
# éléments envoyés d'un bloc à DeepL (avec leurs balises internes) ; le texte hors de ceux-là est envoyé tel quel
_TEXT_TAGS = {"h1", "h2", "h3", "h4", "h5", "h6", "p", "td", "th", "li", "a", "button", "label", "span", "b", "i",
              "strong", "em", "small", "summary", "dt", "dd", "caption", "figcaption", "blockquote"}
_ATTR_RE = re.compile(r'(?<![\w-])(aria-label|placeholder|title|alt)="([^"]*)"')
# attribut HTML translate="no" (guillemets simples ou absents acceptés) ; la classe notranslate fait pareil
_NO = r"""(?:\btranslate\s*=\s*["']?no\b|\bclass\s*=\s*["'][^"']*\bnotranslate\b)"""
_NO_RE = re.compile(_NO, re.I)
_TITLE_RE = re.compile(r"<title(\s[^>]*)?>(.*?)</title>", re.S)
_LETTER_RE = re.compile(r"[^\W\d_]")
_BODY_RE = re.compile(r"<body\b[^>]*>")


def _is_no_translate(attrs: str) -> bool:
    return bool(_NO_RE.search(attrs))


def _attr_matches(text: str):
    """Attributs à traduire ; ceux d'une balise translate="no" restent tels quels."""
    for tag in _TAG_RE.finditer(text):
        if not _is_no_translate(tag.group(3)):
            yield from _ATTR_RE.finditer(tag.group(3))


def _has_text(fragment: str) -> bool:
    # le texte des éléments translate="no" ne compte pas
    fragment = re.sub(r"<(\w+)\b[^>]*?" + _NO + r"[^>]*>.*?</\1>", "", fragment, flags=re.S | re.I)
    return bool(_LETTER_RE.search(html.unescape(re.sub(r"<[^>]+>", "", fragment))))


def _split(body: str) -> list:
    """[(début, fin, à_traduire)] triés et sans chevauchement : blocs de texte (True) et zones à laisser telles quelles (False)
    (scripts, styles, commentaires, éléments translate="no" comme le menu de langues)."""
    hidden = _HIDDEN_RE.sub(lambda m: " " * len(m.group(0)), body)
    spans, covered, stack = [], [], []
    for m in _TAG_RE.finditer(hidden):
        closing, tag, attrs, self_closing = m.group(1), m.group(2).lower(), m.group(3), m.group(4)
        if closing:
            while stack:
                open_tag, start, kind = stack.pop()
                if open_tag == tag:
                    if kind != "plain":
                        covered.append((start, m.start()))
                    if kind == "skip" or (kind == "block" and _has_text(body[start:m.start()])):
                        spans.append((start, m.start(), kind == "block"))
                    break
        elif not self_closing and tag not in _VOID:
            kind = "plain"
            if not any(entry[2] != "plain" for entry in stack):
                kind = "skip" if _is_no_translate(attrs) else "block" if tag in _TEXT_TAGS else "plain"
            stack.append((tag, m.end(), kind))
    taken = lambda pos: any(a <= pos < b for a, b in covered)
    # texte seul, hors de tout élément déjà traité (ex. <div>Texte</div>)
    for m in re.finditer(r">([^<>]+)<", hidden):
        text = m.group(1)
        if _LETTER_RE.search(html.unescape(text)) and not taken(m.start(1)):
            lead = len(text) - len(text.lstrip())
            spans.append((m.start(1) + lead, m.end(1) - (len(text) - len(text.rstrip())), True))
    for m in _HIDDEN_RE.finditer(body):
        if not taken(m.start()):
            spans.append((m.start(), m.end(), False))
            covered.append((m.start(), m.end()))
    return sorted(spans)


def _visible_text(fragment: str) -> str:
    """Texte lisible d'un fragment HTML (sans balises, scripts ni styles), espaces réduits."""
    text = re.sub(r"<[^>]+>", " ", _HIDDEN_RE.sub(" ", fragment))
    return re.sub(r"\s+", " ", re.sub(r"%%\w+%%", " ", html.unescape(text))).strip()  # %%jetons%% = pas du texte


def _build_context(raw: str, nav: str) -> str:
    """Contexte envoyé à DeepL avec chaque lot : le site, son menu et le texte de la page traduite."""
    context = f"{_CONTEXT} Site menu: {nav}. Text of the page being translated: {_visible_text(raw)}"
    return context[:_CONTEXT_LIMIT]


# icônes et flèches (éléments translate="no" sans lettre) en début ou fin de bloc : DeepL ne les voit pas, donc ne les déplace pas
_LEAD_RE = re.compile(r"^(?:\s*<(\w+)\b[^>]*?" + _NO + r"[^>]*>[^<]*</\1>)+", re.I)
_TRAIL_RE = re.compile(r"(?:<(\w+)\b[^>]*?" + _NO + r"[^>]*>[^<]*</\1>\s*)+$", re.I)


def _peel(fragment: str) -> tuple:
    """(début, milieu, fin) : retire les éléments translate="no" décoratifs aux deux bouts du bloc."""
    lead = trail = ""
    m = _LEAD_RE.match(fragment)
    if m and not _LETTER_RE.search(_visible_text(m.group(0))):
        lead, fragment = m.group(0), fragment[m.end():]
    m = _TRAIL_RE.search(fragment)
    if m and not _LETTER_RE.search(_visible_text(m.group(0))):
        trail, fragment = m.group(0), fragment[:m.start()]
    return lead, fragment, trail


_HINT_RE = re.compile(r'\bdata-(context|tr-[a-z0-9]+(?:-[a-z0-9]+)*)="([^"]*)"', re.I)
_HINT_STRIP_RE = re.compile(r'\s+data-(?:context|tr-[a-z0-9-]+)="[^"]*"', re.I)
_labels_memory = {}  # (empreinte, langue) -> {texte français: traduction}


def _hints(body: str, start: int) -> dict:
    """Indications (data-context, data-tr-xx) de la balise ouvrante juste avant le texte qui commence à `start`."""
    tag = body[body.rfind("<", 0, start):start]
    return {m.group(1).lower(): html.unescape(m.group(2)) for m in _HINT_RE.finditer(tag)}


def _forced(hints: dict, lang: str):
    """Traduction imposée pour cette langue (EN-US : data-tr-en-us, sinon data-tr-en), ou None."""
    code = lang.lower()
    return hints.get(f"tr-{code}", hints.get(f"tr-{code.split('-')[0]}"))


def _deepl_hinted(items: list, target: str, as_html: bool, context: str):
    """items = [(texte, data-context)] : un envoi par data-context différent, ajouté au contexte général ; None si échec."""
    groups = {}
    for i, (_, hint) in enumerate(items):
        groups.setdefault(hint, []).append(i)
    out = [None] * len(items)
    with ThreadPoolExecutor(max_workers=max(1, len(groups))) as pool:
        jobs = {hint: pool.submit(_deepl, [items[i][0] for i in rows], target, as_html,
                                  f"{context} Meaning of the texts to translate: {hint}" if hint else context)
                for hint, rows in groups.items()}
        for hint, rows in groups.items():
            done = jobs[hint].result()
            if done is None:
                return None
            for i, text in zip(rows, done):
                out[i] = text
    return out


def _label_translations(topbar_raw: str, lang: str):
    """{texte français: traduction} des textes du menu, ou None si DeepL échoue."""
    cut = _BODY_RE.search(topbar_raw)
    body = topbar_raw[cut.end():] if cut else topbar_raw
    labels = {}  # texte français -> indications de son élément
    for a, b, to_translate in _split(body):
        text = _visible_text(body[a:b])
        if to_translate and _LETTER_RE.search(text):
            labels.setdefault(text, {}).update(_hints(body, a))
    key = (hashlib.sha256(json.dumps(labels, sort_keys=True, ensure_ascii=False).encode()).hexdigest(), lang)
    if key not in _labels_memory:
        if not DEEPL_API_KEY or time.time() - _failed.get(lang, 0) < 60:
            return None
        todo = [text for text, hints in labels.items() if _forced(hints, lang) is None]
        context = f"{_CONTEXT} The texts are the menu entries of the site: {', '.join(labels)}."
        done = _deepl_hinted([(text, labels[text].get("context", "")) for text in todo], lang, False, context)
        if done is None:
            _failed[lang] = time.time()
            return None
        _labels_memory[key] = dict(zip(todo, done))
    forced = {text: value for text, hints in labels.items() if (value := _forced(hints, lang)) is not None}
    return {**_labels_memory[key], **forced}


_ONLY_TEXT_RE = re.compile(r"((?:<[^>]+>\s*)*)([^<>]+?)(\s*(?:</[^>]+>\s*)*)")


def _known(core: str, hints: dict, lang: str, labels: dict):
    """Bloc traduit sans DeepL (traduction imposée dans le HTML, ou texte du menu déjà traduit), sinon None."""
    m = _ONLY_TEXT_RE.fullmatch(core)
    text = _forced(hints, lang)
    if text is None and m:
        text = labels.get(_visible_text(m.group(2)))
    if text is None:
        return None
    text = html.escape(text, quote=False)
    return m.group(1) + text + m.group(3) if m else text  # les balises autour du texte sont gardées


def _mark_no_translate(fragment: str) -> str:
    return re.sub(r"<(code|kbd|pre)\b(?![^>]*translate=)", r'<\1 translate="no"', fragment)


def _translate(raw: str, target: str, context: str = _CONTEXT, labels: dict = None):
    """Fragment HTML français -> traduit, mêmes balises et mêmes %%jetons%% ; None si DeepL échoue."""
    cut = _BODY_RE.search(raw)
    head, body = (raw[:cut.end()], raw[cut.end():]) if cut else ("", raw)
    spans = _split(body)
    blocks = [(a, b) for a, b, tr in spans if tr]
    # attributs hors des zones laissées telles quelles (ceux des blocs sont repris dans le bloc)
    gaps, pos = [], 0
    for a, b, tr in spans:
        gaps.append(body[pos:a])
        if tr:
            gaps.append(body[a:b])
        pos = b
    gaps.append(body[pos:])
    attrs = sorted({
        html.unescape(m.group(2)) for part in gaps for m in _attr_matches(part)
        if len(_LETTER_RE.findall(m.group(2))) >= 2 and not m.group(2).isupper()
    })
    title = _TITLE_RE.search(head)
    title = title if title and not _is_no_translate(title.group(1) or "") else None
    plain_in = ([html.unescape(title.group(2))] if title else []) + attrs

    peeled = [_peel(body[a:b]) for a, b in blocks]
    hints = [_hints(body, a) for a, _ in blocks]
    known = [_known(core, h, target, labels or {}) for (_, core, _), h in zip(peeled, hints)]
    todo = [(_mark_no_translate(core), h.get("context", "")) for (_, core, _), h, text in zip(peeled, hints, known) if text is None]
    with ThreadPoolExecutor(max_workers=2) as pool:
        job_blocks = pool.submit(_deepl_hinted, todo, target, True, context) if todo else None
        job_plain = pool.submit(_deepl, plain_in, target, False, context) if plain_in else None
        done_blocks = job_blocks.result() if job_blocks else []
        done_plain = job_plain.result() if job_plain else []
    if done_blocks is None or done_plain is None:
        return None
    fresh = iter(done_blocks)
    done_blocks = [lead + (text if text is not None else next(fresh)) + trail for (lead, _, trail), text in zip(peeled, known)]

    if title:
        head = head.replace(title.group(0), title.group(0).replace(title.group(2), html.escape(done_plain[0]), 1), 1)
        done_plain = done_plain[1:]
    attr_map = {src: html.escape(dst, quote=True) for src, dst in zip(attrs, done_plain)}

    def swap(text: str) -> str:
        def swap_attr(m):
            return f'{m.group(1)}="{attr_map.get(html.unescape(m.group(2)), m.group(2))}"'
        return _TAG_RE.sub(lambda t: t.group(0) if _is_no_translate(t.group(3)) else _ATTR_RE.sub(swap_attr, t.group(0)), text)

    out, pos, translated = [], 0, iter(done_blocks)
    for a, b, tr in spans:
        out.append(swap(body[pos:a]))
        out.append(swap(next(translated)) if tr else body[a:b])
        pos = b
    out.append(swap(body[pos:]))
    return head + "".join(out)


# ---------------------------------------------------------------- caches

_memory = {}  # (empreinte, langue) -> HTML traduit
_failed = {}  # langue -> moment du dernier échec DeepL (pas de nouvel essai avant 60 s)


def _sb(method: str, query: dict, payload=None):
    url = f"{SUPABASE_URL}/rest/v1/bot_translations?" + urllib.parse.urlencode(query)
    req = urllib.request.Request(url, data=json.dumps(payload).encode() if payload else None, method=method)
    req.add_header("apikey", SUPABASE_KEY)
    req.add_header("Authorization", f"Bearer {SUPABASE_KEY}")
    req.add_header("Content-Type", "application/json")
    with urllib.request.urlopen(req, timeout=5) as r:
        return json.loads(r.read() or b"null")


def _cached_translation(name: str, raw: str, lang: str, context: str, labels: dict):
    """(HTML traduit ou None, origine) ; origine = mem, db, deepl ou fail."""
    fingerprint = "sha256:" + hashlib.sha256(("v3:" + context + "\n" + json.dumps(labels, sort_keys=True, ensure_ascii=False) + "\n" + raw).encode()).hexdigest()
    key = (fingerprint, lang)
    if key in _memory:
        return _memory[key], "mem"
    use_db = bool(SUPABASE_URL and SUPABASE_KEY)
    message_key = f"wiki_{name}"
    if use_db:
        try:
            rows = _sb("GET", {"select": "translation", "message_key": f"eq.{message_key}", "lang": f"eq.{lang}",
                               "text_fr": f"eq.{fingerprint}"})
            if rows:
                _memory[key] = rows[0]["translation"]
                return _memory[key], "db"
        except Exception as e:
            print(f"translate : error 'supabase lookup failed for {name}/{lang} : {e}'")
    if not DEEPL_API_KEY or time.time() - _failed.get(lang, 0) < 60:
        return None, "fail"
    text = _translate(raw, lang, context, labels)
    if text is None:
        _failed[lang] = time.time()
        return None, "fail"
    _memory[key] = text
    if use_db:
        try:
            # la table a une contrainte unique (clé, langue) : on supprime l'ancienne ligne avant d'insérer
            _sb("DELETE", {"message_key": f"eq.{message_key}", "lang": f"eq.{lang}"})
            _sb("POST", {}, {"message_key": message_key, "lang": lang, "text_fr": fingerprint, "translation": text})
        except Exception as e:
            print(f"translate : error 'supabase store failed for {name}/{lang} : {e}'")
    return text, "deepl"


# ---------------------------------------------------------------- page

@lru_cache(maxsize=None)
def _read(relative_path: str) -> str:
    with open(os.path.join(_ROOT, relative_path), encoding="utf-8") as f:
        return f.read()


_HREF_RE = re.compile(r'(<a\b[^>]*?\shref=")([^"]*)(")')
_PATH_RE = re.compile(r"^[A-Za-z0-9_-]+(/[A-Za-z0-9_-]+)*$")
_HIDDEN_DIRS = {"api", "global"}


def _link_with_lang(match, param: str) -> str:
    prefix, href, suffix = match.groups()
    if not param or href.startswith(("#", "//")) or re.match(r"^[a-zA-Z][a-zA-Z0-9+.-]*:", href):
        return match.group(0)
    path, hash_sep, fragment = href.partition("#")
    path, _, query = path.partition("?")
    last = path.rsplit("/", 1)[-1]
    if "." in last and not last.endswith(".html"):
        return match.group(0)
    kept = [q for q in query.split("&") if q and not q.startswith("lang=")]
    return f'{prefix}{path}?{"&".join(kept + [param])}{hash_sep}{fragment}{suffix}'


def _translate_parts(parts: dict, lang: str):
    """{nom: (HTML traduit, origine)} pour le menu, le pied de page et la page ; None si DeepL échoue."""
    labels = _label_translations(parts["topbar"], lang)  # d'abord le menu : ses traductions servent ensuite partout
    if labels is None:
        return None
    nav = _visible_text(parts["topbar"])
    with ThreadPoolExecutor(max_workers=len(parts)) as pool:
        jobs = {name: pool.submit(_cached_translation, name, raw, lang, _build_context(raw, nav), labels) for name, raw in parts.items()}
        results = {name: job.result() for name, job in jobs.items()}
    return None if any(text is None for text, _ in results.values()) else results


def _render(page_path: str, lang: str, link_param: str) -> tuple:
    """(HTML final, origine, langue réellement servie)."""
    raw_page = _read(os.path.join(page_path, "index.html"))
    parts = {"topbar": _read("global/topbar.html"), "footer": _read("global/footer.html"), f"page_{page_path or 'index'}": raw_page}
    source = "fr"
    if lang != "FR":
        results = _translate_parts(parts, lang)
        if results is None:
            lang = "FR"  # DeepL indisponible : version française
        else:
            parts = {name: text for name, (text, _) in results.items()}
            source = "+".join(sorted({origin for _, origin in results.values()}))
    page = parts[f"page_{page_path or 'index'}"]
    topbar = (
        parts["topbar"]
        .replace("%%LANG_CODE%%", lang)
        .replace("%%LANG_OPTIONS%%", _language_options(lang))
    )
    page = page.replace('<div id="site-topbar"></div>', topbar).replace('<div id="site-footer"></div>', parts["footer"])
    page = _HINT_STRIP_RE.sub("", page)
    page = _HREF_RE.sub(lambda m: _link_with_lang(m, link_param), page)
    marker = " data-hide-lang" if HIDE_LANG_PARAM else ""  # lu par translate.js : le menu n'ajoute alors pas ?lang= à l'URL
    page = page.replace('<html lang="fr"', f'<html lang="{lang.lower()}"{marker}', 1)
    return page, source, lang


_NOT_FOUND = "<!DOCTYPE html><html><head><meta charset=\"UTF-8\"><title>404</title></head><body><h1>404</h1><p>Page introuvable / Page not found</p></body></html>"
_cold = [True]


class handler(BaseHTTPRequestHandler):
    def do_GET(self):
        started = time.perf_counter()
        url = urlparse(self.path)
        query = parse_qs(url.query, keep_blank_values=True)
        page_path = query.get("p", [url.path])[0].strip("/")
        if page_path.endswith("index.html"):
            page_path = page_path[: -len("index.html")].strip("/")
        valid = not page_path or (_PATH_RE.match(page_path) and page_path.split("/")[0] not in _HIDDEN_DIRS)
        if not valid or not os.path.isfile(os.path.join(_ROOT, page_path, "index.html")):
            return self.send_page(404, _NOT_FOUND, "no-store", "")

        cookie = SimpleCookie(self.headers.get("Cookie", ""))
        lang, explicit = _choose_language(
            query.get("lang", [""])[0],
            cookie["lang"].value if HIDE_LANG_PARAM and "lang" in cookie else "",  # cookie lu seulement si l'URL reste propre
            self.headers.get("Accept-Language", ""),
        )
        if HIDE_LANG_PARAM and explicit:
            # ?lang= valide : on le range dans le cookie et on le retire de l'URL
            rest = [(k, v) for k, values in query.items() if k not in ("lang", "p") for v in values]
            return self.redirect("/" + page_path + ("?" + urllib.parse.urlencode(rest) if rest else ""), lang.lower())
        # la langue suit les liens internes : ?lang=xx (pour le français, seulement s'il a été demandé dans l'URL)
        # False : ?lang= présent -> repris dans les liens internes ; absent -> chaque page suit la langue du navigateur
        link_param = f"lang={lang.lower()}" if explicit and not HIDE_LANG_PARAM else ""
        body, source, served = _render(page_path, lang, link_param)
        # URL avec ?lang= : même page pour tout le monde, le CDN peut la garder ; sinon dépend du navigateur
        shared = explicit and served == lang
        cache = "public, max-age=0, s-maxage=86400, stale-while-revalidate=604800" if shared else "private, no-cache"
        timing = f'app;dur={(time.perf_counter() - started) * 1000:.0f}, cold;desc="{int(_cold[0])}", src;desc="{source}"'
        _cold[0] = False
        self.send_page(200, body, cache, "" if shared else "Accept-Language, Cookie", timing)

    def redirect(self, location: str, lang: str):
        self.send_response(302)
        self.send_header("Location", location)
        self.send_header("Set-Cookie", f"lang={lang}; Path=/; Max-Age=31536000; SameSite=Lax")
        self.send_header("Cache-Control", "no-store")
        self.send_header("Content-Length", "0")
        self.end_headers()

    def send_page(self, status: int, body: str, cache: str, vary: str, timing: str = ""):
        data = body.encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", cache)
        if vary:
            self.send_header("Vary", vary)
        if timing:
            self.send_header("Server-Timing", timing)
        self.end_headers()
        self.wfile.write(data)