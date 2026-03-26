"""
scripts/build_data_json.py

Builds data.json with four sections:
  - world_org_meetings   (next 5 major world organization meetings)
  - diplomatic_visits    (next 5 major diplomatic visits)
  - elections            (next 5 major upcoming elections)
  - global_events        (top 5 unique global stories across 40 outlets)

Zero paid AI APIs. Uses:
  - 40 RSS feeds
  - NewsAPI free tier (optional — degrades gracefully if key absent)
  - Wikipedia Current Events / Elections pages
  - Pure-Python relevance scoring, deduplication, and clustering

Output: public/data.json
"""

from __future__ import annotations

import json
import os
import re
import time
from datetime import datetime, timezone, timedelta
from pathlib import Path
from typing import Dict, List, Optional, Tuple
from urllib.parse import urlparse, parse_qs, urlencode, urlunparse

import feedparser
import requests
from dateutil import parser as dtparser

# ---------------------------------------------------------------------------
# HTTP config
# ---------------------------------------------------------------------------

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/120.0.0.0 Safari/537.36"
    ),
    "Accept": "application/rss+xml, application/xml, text/xml, */*;q=0.8",
    "Accept-Language": "en-US,en;q=0.9",
}

TIMEOUT = 20
MAX_RETRIES = 2
RETRY_SLEEP = 1.2
WINDOW_HOURS = 96           # default: elections & global events (4 days)
ORG_WINDOW_HOURS = 336      # world org meetings (2 weeks)
DIPLOMATIC_WINDOW_HOURS = 336  # diplomatic visits (2 weeks)
NEWSAPI_KEY = os.environ.get("NEWSAPI_KEY", "")

# ---------------------------------------------------------------------------
# RSS feeds
# ---------------------------------------------------------------------------

RSS_FEEDS: Dict[str, str] = {
    "BBC World":          "https://feeds.bbci.co.uk/news/world/rss.xml",
    "Reuters":            "https://feeds.reuters.com/reuters/topNews",
    "AP News":            "https://apnews.com/rss",
    "CNN World":          "https://rss.cnn.com/rss/edition_world.rss",
    "NPR World":          "https://feeds.npr.org/1004/rss.xml",
    "PBS NewsHour":       "https://www.pbs.org/newshour/feeds/rss/world",
    "CBC World":          "https://rss.cbc.ca/lineup/world.xml",
    "ABC News Intl":      "https://abcnews.go.com/abcnews/internationalheadlines",
    "CBS News World":     "https://www.cbsnews.com/latest/rss/world",
    "NBC News World":     "https://feeds.nbcnews.com/nbcnews/public/world",
    "Sky News World":     "https://feeds.skynews.com/feeds/rss/world.xml",
    "Fox News World":     "https://moxie.foxnews.com/google-publisher/world.xml",
    "NYT World":          "https://rss.nytimes.com/services/xml/rss/nyt/World.xml",
    "The Guardian World": "https://www.theguardian.com/world/rss",
    "Wash Post World":    "https://feeds.washingtonpost.com/rss/world",
    "WSJ World":          "https://www.wsj.com/xml/rss/3_7085.xml",
    "FT":                 "https://feeds.ft.com/rss/home/uk",
    "Bloomberg":          "https://feeds.bloomberg.com/markets/news.rss",
    "The Economist":      "https://www.economist.com/the-world-this-week/rss.xml",
    "Newsweek":           "https://www.newsweek.com/rss",
    "Time":               "https://time.com/feed/",
    "The Independent":    "https://www.independent.co.uk/news/world/rss",
    "USA Today World":    "https://rssfeeds.usatoday.com/usatoday-NewsTopStories",
    "Al Jazeera":         "https://www.aljazeera.com/xml/rss/all.xml",
    "DW World":           "https://rss.dw.com/rdf/rss-en-world",
    "France24":           "https://www.france24.com/en/rss",
    "Times of India":     "https://timesofindia.indiatimes.com/rssfeeds/-2128936835.cms",
    "Japan Times":        "https://www.japantimes.co.jp/feed/",
    "The Hindu Intl":     "https://www.thehindu.com/news/international/feeder/default.rss",
    "SCMP":               "https://www.scmp.com/rss/4/feed",
    "Straits Times":      "https://www.straitstimes.com/global/rss.xml",
    "SMH World":          "https://feeds.smh.com.au/rss/world",
    "UN News":            "https://news.un.org/feed/subscribe/en/news/all/rss.xml",
    "Foreign Policy":     "https://foreignpolicy.com/feed/",
    "Atlantic Council":   "https://www.atlanticcouncil.org/feed/",
    "Carnegie":           "https://carnegieendowment.org/rss/carnegie.xml",
    "Politico Intl":      "https://www.politico.com/rss/politics08.xml",
    "The Hill":           "https://thehill.com/feed/",
    "Axios":              "https://www.axios.com/feeds/feed.rss",
    "Vox":                "https://www.vox.com/rss/index.xml",
}

WIKI_API = "https://en.wikipedia.org/w/api.php"

# ---------------------------------------------------------------------------
# Headline cleaning
# ---------------------------------------------------------------------------

_PREFIX_DROPS = [
    r"^watch( now)?:\s*", r"^live( now)?:\s*", r"^video:\s*",
    r"^analysis:\s*", r"^explainer:\s*", r"^opinion:\s*",
    r"^what to know:\s*", r"^fact check:\s*", r"^breaking:\s*",
]
_SUFFIX_DROPS = [
    r"\s*[-|]\s*(ap news|reuters|bbc news?|pbs newshour?|cbc news?|the guardian|dw|npr|cnn|fox news)\s*$",
]
_BRACKET_DROPS = [
    r"\s*\((?:video|watch|live|updated?|analysis|opinion)\)\s*$",
    r"\s*\[(?:video|watch|live|updated?|analysis|opinion)\]\s*$",
]


def clean_headline(title: str) -> str:
    if not title:
        return ""
    t = title.strip()
    for p in _PREFIX_DROPS:
        t = re.sub(p, "", t, flags=re.IGNORECASE)
    for p in _SUFFIX_DROPS:
        t = re.sub(p, "", t, flags=re.IGNORECASE)
    for p in _BRACKET_DROPS:
        t = re.sub(p, "", t, flags=re.IGNORECASE)
    t = re.sub(r"\s+[\|\-]\s*(?:news|newshour|world|international)\s*$", "", t, flags=re.IGNORECASE)
    return re.sub(r"\s+", " ", t).strip()


# ---------------------------------------------------------------------------
# Junk filters
# ---------------------------------------------------------------------------

_JUNK_RE = [re.compile(p, re.IGNORECASE) for p in [
    r"\b(horoscope|zodiac|astrology)\b",
    r"\b(crossword|puzzle|sudoku|quiz)\b",
    r"\b(recipe|cooking|restaurant review)\b",
    r"\b(celebrity gossip|kardashian)\b",
    r"\bnfl\b", r"\bnba\b", r"\bmlb\b", r"\bnhl\b",
    r"\b(hockey|basketball|baseball|soccer|football|tennis|golf|rugby)\b",
    r"\b(score|standings|playoff|championship|tournament|league table)\b",
    r"\b(stock pick|best deal|coupon|discount|sale)\b",
    r"\btop \d+ (tips|ways|hacks|reasons)\b",
    r"\b(weather forecast|today.s weather)\b",
    r"\b(movie|film|album|book|tv|podcast) review\b",
    r"^\s*(gallery|subscribe|newsletter)\b",
    r"\b(viral|trending|tiktok|instagram|meme)\b",
    r"\b(lottery|jackpot|casino)\b",
    r"\b(recipe|calories|diet|weight loss|fitness tip)\b",
]]


def _is_junk(title: str) -> bool:
    return any(p.search(title) for p in _JUNK_RE)


# ---------------------------------------------------------------------------
# US domestic filter
# ---------------------------------------------------------------------------

_INTL_OVERRIDE = [
    "russia", "china", "ukraine", "nato", "iran", "israel", "gaza",
    "taiwan", "north korea", "foreign", "international", "global",
    "sanctions", "tariff", "trade war", "diplomatic", "united nations",
    "middle east", "europe", "asia", "africa", "strait of hormuz",
]

_US_DOMESTIC_RE = [re.compile(p, re.IGNORECASE) for p in [
    r"\b(congress|senate|house of representatives|governor|mayor|supreme court)\b",
    r"\b(gop|democrat|republican)\b",
    r"\b(2026 midterm|2028 election|presidential race|primary election|caucus)\b",
    r"\b(wall street|nasdaq|dow jones|s&p 500|federal reserve|fed rate)\b",
    r"\b(irs|social security|medicare|medicaid)\b",
    r"\bflorida\b|\btexas\b|\bcalifornia\b|\bnew york state\b|\bchicago\b|\blos angeles\b",
]]


def _is_us_domestic(title: str) -> bool:
    t = title.lower()
    if any(kw in t for kw in _INTL_OVERRIDE):
        return False
    return any(p.search(title) for p in _US_DOMESTIC_RE)


# ---------------------------------------------------------------------------
# World Org keyword lists
# ---------------------------------------------------------------------------

# Each entry is (search_string, canonical_org_label).
# Longer/more specific strings must come before shorter ones so the first
# match wins correctly (e.g. "un security council" before " un ").
_ORG_MAP: List[Tuple[str, str]] = [
    # UN bodies — most specific first
    ("un security council",         "UN Security Council"),
    ("un general assembly",         "UN General Assembly"),
    ("un human rights council",     "UN Human Rights Council"),
    ("united nations human rights", "UN Human Rights Council"),
    ("un climate",                  "UN / COP"),
    ("un women",                    "UN Women"),
    ("un peacekeeping",             "UN Peacekeeping"),
    ("united nations",              "UN"),
    # Other major orgs
    ("world health organization",   "WHO"),
    ("world trade organization",    "WTO"),
    ("world bank",                  "World Bank"),
    ("international monetary fund", "IMF"),
    ("international criminal court","ICC"),
    ("international court of justice","ICJ"),
    ("nato",                        "NATO"),
    ("european union",              "EU"),
    ("eu summit",                   "EU"),
    ("eu council",                  "EU"),
    ("european commission",         "EU"),
    ("g7",                          "G7"),
    ("g20",                         "G20"),
    ("asean",                       "ASEAN"),
    ("apec",                        "APEC"),
    ("african union",               "AU"),
    ("arab league",                 "Arab League"),
    ("opec",                        "OPEC"),
    ("brics",                       "BRICS"),
    ("shanghai cooperation",        "SCO"),
    ("organization of american states", "OAS"),
    ("cop30",                       "COP30"),
    ("cop ",                        "COP"),
    ("climate summit",              "COP"),
    ("climate conference",          "COP"),
    # Abbreviation-only matches — wrapped in word boundaries to avoid false matches
    # These are checked separately via regex below
]

# Abbreviation-only patterns needing word-boundary matching to avoid false positives
# e.g. " who " would match "who knows" — use regex instead
_ORG_ABBREV_MAP: List[Tuple[re.Pattern, str]] = [
    (re.compile(r"\bwho\b", re.IGNORECASE),   "WHO"),
    (re.compile(r"\bwto\b", re.IGNORECASE),   "WTO"),
    (re.compile(r"\bimf\b", re.IGNORECASE),   "IMF"),
    (re.compile(r"\bicc\b", re.IGNORECASE),   "ICC"),
    (re.compile(r"\bicj\b", re.IGNORECASE),   "ICJ"),
    (re.compile(r"\bsco\b", re.IGNORECASE),   "SCO"),
    (re.compile(r"\boas\b", re.IGNORECASE),   "OAS"),
    (re.compile(r"\baу\b",  re.IGNORECASE),   "AU"),   # African Union abbreviation
    # " un " with surrounding word boundary — avoid matching "union", "under", etc.
    (re.compile(r"(?<!\w)un(?!\w)", re.IGNORECASE), "UN"),
]

# Keywords used for RSS pre-filtering (broad net; org inference validates afterward)
_WORLD_ORG_FEED_KW = [
    "united nations", "nato", "g7", "g20", "asean", "apec",
    "african union", "wto", "imf", "world bank",
    "world health organization", "who", "cop30", "cop ",
    "climate summit", "opec", "arab league", "brics",
    "shanghai cooperation", "eu summit", "eu council",
    "european union", "icc", "icj", "un security council",
    "un general assembly", "summit", "council meeting",
    "multilateral", "international forum",
]

_WORLD_ORG_EVENT_TYPES = [
    "summit", "meeting", "session", "assembly", "conference",
    "forum", "talks", "gather", "convene", "negotiate", "council",
    "vote", "resolution", "sanctions", "approved", "adopted",
]


def _infer_org(title: str) -> str:
    """
    Return the canonical organisation name for a headline.
    Checks long-form strings first (most specific), then abbreviation regexes.
    Falls back to "" if nothing matches.
    """
    t_lower = title.lower()

    # 1. Long-form / phrase matches (ordered most-specific → least-specific)
    for phrase, label in _ORG_MAP:
        if phrase in t_lower:
            return label

    # 2. Abbreviation-only regex matches (word-boundary safe)
    for pattern, label in _ORG_ABBREV_MAP:
        if pattern.search(title):
            return label

    return ""


def _is_valid_org_item(title: str) -> bool:
    """
    Accept a headline only when it names a known org AND signals an actual event/action
    (not just an opinion piece that happens to mention NATO, etc.).
    """
    t = title.lower()
    has_org = bool(_infer_org(title))          # uses the improved lookup above
    has_event = any(ev in t for ev in _WORLD_ORG_EVENT_TYPES)
    return has_org and has_event


# ---------------------------------------------------------------------------
# Diplomatic visits — keyword lists and filters
# ---------------------------------------------------------------------------

# RSS pre-filter: broad net
_DIPLOMATIC_FEED_KW = [
    "ambassador", "diplomatic visit", "state visit", "bilateral",
    "foreign minister", "secretary of state", "heads of state",
    "official visit", "summit", "joint statement", "signed agreement",
    "signed treaty", "signed pact", "welcomed", "hosted", "arrived",
    "talks between", "meeting between",
]

# Strong signals that an actual visit/meeting took place or is firmly scheduled
_DIPLOMATIC_VISIT_STRONG_RE = [re.compile(p, re.IGNORECASE) for p in [
    r"\bstate visit\b",
    r"\bbilateral (talks|meeting|summit|discussions)\b",
    r"\bofficial visit\b",
    r"\bdiplomatic visit\b",
    r"\bheads of state\b",
    r"\btalks between\b",
    r"\bmeeting between\b",
    r"\bdiplomatic (talks|meeting|summit|discussions)\b",
    # Travel + purpose
    r"\b(arriv(?:es?|ed|ing)|travel(?:s|led|ling)?|flew|flies|heading) to\b.{0,60}\b(meet|talks?|summit|visit)\b",
    # A titled leader + met/visited
    r"\b(president|prime minister|chancellor|foreign minister|secretary of state)\b.{0,60}"
    r"\b(meet(?:s|ing)?|met|visit(?:s|ed|ing)?|arriv(?:es?|ed|ing)?)\b",
    # Hosting a titled leader
    r"\b(host(?:s|ed|ing)?|welcom(?:es?|ed|ing))\b.{0,60}"
    r"\b(president|prime minister|leader|chancellor|counterpart)\b",
    # Signed agreements
    r"\b(sign(?:s|ed|ing)?)\b.{0,60}\b(agreement|deal|pact|treaty|accord|memorandum)\b",
    r"\bjoint (statement|communiqué|press conference|declaration)\b",
    r"\bsummit (between|with|of)\b",
    # Ambassador-related visits
    r"\bambassador\b.{0,60}\b(present(?:s|ed)?|credentials|arriv(?:es?|ed)|meet(?:s|ing)?|met)\b",
    r"\bnew ambassador\b",
    r"\benvoy\b.{0,40}\b(arriv(?:es?|ed)|meet(?:s|ing)?|met|sent)\b",
]]

# Hard-block patterns — reject regardless of strong signals
_DIPLOMATIC_BLOCK_RE = [re.compile(p, re.IGNORECASE) for p in [
    # Live war/conflict updates
    r"\b(war live|live update|live blog)\b",
    r"\blive:\s",
    r"\b(airstrike|missile strike|drone strike|bombing|shelling|invasion)\b",
    r"\b(kill(?:s|ed)|wound(?:s|ed)|dead|casualties|death toll)\b",
    # Pure statements or accusations — not visits
    r"\bno plans? (for|to)\b",
    r"\brejects? (deal|proposal|offer|talks)\b",
    r"\bbegging\b",
    r"'no problem'",
    r"\baccus(?:es?|ed)\b",
    r"\bwarn(?:s|ed)\b.{0,40}\b(war|attack|strike|retaliate)\b",
    r"\bthreaten(?:s|ed)\b",
    # Opinion / speculation
    r"\b(could|might|may|would)\b.{0,20}\b(improve|worsen|change|signal|pave the way)\b",
    r"\b(sign of|what it means|analysis|opinion|commentary|column|explainer)\b",
    # "Offers to host" / "proposes" — not yet a real visit
    r"\b(offer(?:s|ed)?|propos(?:es?|ed)?|seek(?:s|ing)?|call(?:s|ed)? for)\b.{0,40}"
    r"\b(host|mediat|facilitat|broker|arrang)\b",
    # Media visits
    r"\b(journalist|reporter|correspondent|editor|anchor)\b.{0,30}\bvisit",
    # Legal / criminal
    r"\b(arrested?|indicted?|charged?|sentenced?|extradited?)\b",
    # Health / succession
    r"\b(injur|health|hospital|succession)\b.{0,40}\b(supreme leader|president|minister)\b",
    # Vague summits without named leaders (e.g. "Melania opens summit")
    r"^melania\b",   # first lady summits are not head-of-state diplomatic visits
]]


def _is_valid_diplomatic_item(title: str) -> bool:
    if any(p.search(title) for p in _DIPLOMATIC_BLOCK_RE):
        return False
    if not any(p.search(title) for p in _DIPLOMATIC_VISIT_STRONG_RE):
        return False
    return True


# ---------------------------------------------------------------------------
# Participant name extraction — improved multi-word name handling
# ---------------------------------------------------------------------------

# Known multi-word titles to strip before extracting names so they don't
# get split into separate tokens
_TITLE_STRIP_RE = re.compile(
    r"\b(Prime Minister|Foreign Minister|Secretary of State|President|Chancellor|"
    r"King|Queen|Prince|Princess|Emperor|Pope|Sheikh|Emir|Sultan|General|Admiral|"
    r"Minister|Senator|Governor|Mayor|Ambassador|Deputy|Vice|Sir|Lord|Dame)\b",
    re.IGNORECASE,
)

# Pairs of consecutive capitalized words are treated as a full name
def _infer_participants(title: str) -> List[str]:
    """
    Extract person/country names as full tokens (e.g. 'Joe Biden', 'Saudi Arabia').
    Returns up to 4 unique names, preferring multi-word proper nouns over singles.
    """
    skip_words = {
        "The", "This", "That", "After", "During", "When", "While", "As", "But",
        "And", "Or", "For", "With", "From", "Into", "Over", "Under", "About",
        "Is", "Are", "Was", "Were", "Has", "Have", "Had", "Will", "Would",
        "Could", "Should", "Foe", "Friend", "New", "Old", "First", "Last",
        "Top", "Key", "Major", "How", "Why", "What", "Where", "Who", "NATO",
        "UN", "EU", "US", "UK", "G7", "G20", "IMF", "WTO", "WHO",
    }

    # Tokenise on whitespace, strip punctuation from edges
    words = [w.strip(".,;:'\"()[]") for w in title.split()]

    names: List[str] = []
    i = 0
    while i < len(words):
        w = words[i]
        if not w or not w[0].isupper() or w in skip_words:
            i += 1
            continue

        # Try to absorb following capitalised words into a multi-word name
        # Stop if we hit a short connector word (of, the, and, etc.) or lower-case
        j = i + 1
        while j < len(words):
            nw = words[j].strip(".,;:'\"()[]")
            # Allow "of" in the middle of a name (e.g. "King of Jordan") only once
            if nw.lower() in ("of", "the") and j + 1 < len(words) and words[j+1][0].isupper():
                j += 2
                continue
            if nw and nw[0].isupper() and nw not in skip_words:
                j += 1
            else:
                break

        chunk = " ".join(w.strip(".,;:'\"()[]") for w in words[i:j])
        # Only keep if at least 3 chars and not a plain title word
        if len(chunk) >= 3 and chunk not in skip_words:
            if chunk not in names:
                names.append(chunk)
        i = j

    return names[:4]


# ---------------------------------------------------------------------------
# Election keywords
# ---------------------------------------------------------------------------

_ELECTION_KW = [
    "election", "presidential election", "parliamentary election",
    "general election", "legislative election", "referendum",
    "snap election", "federal election", "national election",
    "goes to polls", "voters head", "polling day",
    "votes for", "casts ballot", "election campaign",
    "election result", "election winner", "sweeps election",
    "wins election", "won election",
]

_ELECTION_BLOCK_RE = [re.compile(p, re.IGNORECASE) for p in [
    r"\b(midterm|2028|trump|gop|democrat|republican|senate race|house race)\b",
    r"\b(betting market|odds|favorite for|polling average|kevin o.leary)\b",
    r"\b(selection is a sign|sign of political|political exhaustion)\b",
    r"\b(selection|appointed|named as|chosen as)\b.{0,30}\b(supreme leader|leader|head)\b",
]]

_GLOBAL_KW = [
    "war", "conflict", "attack", "military", "troops", "invasion",
    "ceasefire", "missile", "drone", "airstrike", "shelling",
    "election", "vote", "president", "prime minister", "parliament",
    "summit", "treaty", "sanctions", "diplomatic",
    "un ", "nato", "eu ", "g7", "g20",
    "crisis", "protest", "coup", "uprising",
    "earthquake", "flood", "hurricane", "disaster", "climate",
    "nuclear", "weapon", "bomb",
    "trade", "tariff", "economy", "inflation", "recession",
    "pandemic", "outbreak", "vaccine",
    "terror", "assassination",
    "refugee", "migration",
    "iran", "russia", "ukraine", "china", "israel", "gaza", "taiwan",
    "north korea", "india", "pakistan", "middle east", "africa",
]

# ---------------------------------------------------------------------------
# Deduplication / clustering
# ---------------------------------------------------------------------------

_STOPWORDS = {
    "the","a","an","in","on","at","to","of","for","and","or","is","are",
    "was","were","with","that","this","by","as","it","its","he","she",
    "they","after","over","into","from","says","said","will","could",
    "would","should","amid","about","new","more","than","their","our",
    "report","update","latest","live","watch","has","have","been","be",
    "not","but","also","when","who","what","where","how",
}


def _tokens(title: str) -> set:
    t = re.sub(r"[^a-z0-9 ]", " ", title.lower())
    return {w for w in t.split() if len(w) >= 3 and w not in _STOPWORDS}


def _story_sig(title: str) -> str:
    t = re.sub(r"[^a-z0-9\s]", " ", title.lower())
    tokens = [w for w in t.split() if len(w) >= 3 and w not in _STOPWORDS]
    return " ".join(tokens[:10])


def _jaccard(a: set, b: set) -> float:
    if not a or not b:
        return 0.0
    return len(a & b) / len(a | b)


def canonicalize_url(url: str) -> str:
    try:
        u = urlparse(url)
        qs = parse_qs(u.query, keep_blank_values=True)
        drop = {"utm_source","utm_medium","utm_campaign","utm_term","utm_content","fbclid","gclid"}
        for k in list(qs):
            if k.lower() in drop:
                qs.pop(k)
        new_q = urlencode({k: v[0] for k, v in qs.items() if v})
        path = u.path.rstrip("/") or "/"
        return urlunparse((u.scheme, u.netloc, path, u.params, new_q, ""))
    except Exception:
        return url


def _dedup_items(items: List[dict]) -> List[dict]:
    seen_sigs: dict = {}
    out = []
    for it in items:
        sig = _story_sig(it.get("title", ""))
        if not sig:
            continue
        if sig in seen_sigs:
            existing = out[seen_sigs[sig]]
            if not existing.get("source_url") and it.get("source_url"):
                out[seen_sigs[sig]] = it
        else:
            seen_sigs[sig] = len(out)
            out.append(it)
    return out


# ---------------------------------------------------------------------------
# HTTP helpers
# ---------------------------------------------------------------------------

def _get(url: str) -> Optional[str]:
    sess = requests.Session()
    sess.headers.update(HEADERS)
    for attempt in range(1, MAX_RETRIES + 1):
        try:
            r = sess.get(url, timeout=TIMEOUT, allow_redirects=True)
            if r.status_code == 200:
                return r.text
        except requests.RequestException:
            pass
        time.sleep(RETRY_SLEEP * attempt)
    return None


def _newsapi(q: str, page_size: int = 30) -> List[dict]:
    if not NEWSAPI_KEY:
        return []
    params = {
        "q": q, "language": "en", "sortBy": "publishedAt",
        "pageSize": page_size, "apiKey": NEWSAPI_KEY,
    }
    try:
        r = requests.get("https://newsapi.org/v2/everything", params=params, timeout=15)
        r.raise_for_status()
        return r.json().get("articles", [])
    except Exception:
        return []


def _parse_dt(entry: dict) -> Optional[datetime]:
    for k in ("published_parsed", "updated_parsed"):
        st = entry.get(k)
        if st:
            try:
                return datetime(*st[:6], tzinfo=timezone.utc)
            except Exception:
                pass
    for k in ("published", "updated"):
        v = entry.get(k)
        if v:
            try:
                dt = dtparser.parse(v)
                return dt.replace(tzinfo=timezone.utc) if dt.tzinfo is None else dt.astimezone(timezone.utc)
            except Exception:
                pass
    return None


# ---------------------------------------------------------------------------
# RSS feed loader
# ---------------------------------------------------------------------------

def _load_feed(source: str, url: str, keywords: List[str], window_hours: int = WINDOW_HOURS) -> List[dict]:
    txt = _get(url)
    if not txt:
        return []
    d = feedparser.parse(txt)
    cutoff = datetime.now(timezone.utc) - timedelta(hours=window_hours)
    items = []
    for e in getattr(d, "entries", []):
        raw = (e.get("title") or "").strip()
        link = canonicalize_url((e.get("link") or "").strip())
        if not raw or not link:
            continue
        title = clean_headline(raw)
        if not title or _is_junk(title):
            continue
        dt = _parse_dt(e)
        if dt and dt < cutoff:
            continue
        t_lower = title.lower()
        if not any(kw in t_lower for kw in keywords):
            continue
        items.append({
            "title": title,
            "url": link,
            "source": source,
            "publishedAt": dt.isoformat().replace("+00:00", "Z") if dt else None,
        })
    return items


# ---------------------------------------------------------------------------
# Cluster and rank
# ---------------------------------------------------------------------------

def _cluster_and_rank(items: List[dict], limit: int) -> List[dict]:
    seen_urls: set = set()
    unique: List[dict] = []
    for it in items:
        u = it.get("url", "")
        if u and u not in seen_urls:
            seen_urls.add(u)
            unique.append(it)

    clusters: List[List[dict]] = []
    cluster_tokens: List[set] = []

    for it in unique:
        toks = _tokens(it["title"])
        matched = False
        for i, ct in enumerate(cluster_tokens):
            if _jaccard(toks, ct) >= 0.35:
                clusters[i].append(it)
                cluster_tokens[i] |= toks
                matched = True
                break
        if not matched:
            clusters.append([it])
            cluster_tokens.append(set(toks))

    scored: List[Tuple[float, dict]] = []
    for group in clusters:
        unique_sources = len({g["source"] for g in group})
        rep = max(group, key=lambda x: (
            dtparser.parse(x["publishedAt"]).timestamp()
            if x.get("publishedAt") else 0.0
        ))
        try:
            ts = dtparser.parse(rep["publishedAt"]).timestamp() if rep.get("publishedAt") else 0.0
        except Exception:
            ts = 0.0
        scored.append((unique_sources * 1_000_000 + ts, rep))

    scored.sort(key=lambda x: x[0], reverse=True)

    seen_sigs: set = set()
    out = []
    for _, rep in scored:
        sig = _story_sig(rep["title"])
        if sig in seen_sigs:
            continue
        seen_sigs.add(sig)
        out.append(rep)
        if len(out) >= limit:
            break
    return out


# ---------------------------------------------------------------------------
# Wikipedia helpers
# ---------------------------------------------------------------------------

def _wiki_extract(titles: str) -> str:
    params = {
        "action": "query", "titles": titles,
        "prop": "extracts", "explaintext": True, "format": "json",
    }
    try:
        r = requests.get(WIKI_API, params=params, timeout=15)
        r.raise_for_status()
        pages = r.json()["query"]["pages"]
        return "\n\n".join(p.get("extract", "")[:4000] for p in pages.values())
    except Exception:
        return ""


# ---------------------------------------------------------------------------
# Date helpers
# ---------------------------------------------------------------------------

_MONTHS = r"(?:Jan(?:uary)?|Feb(?:ruary)?|Mar(?:ch)?|Apr(?:il)?|May|Jun(?:e)?|Jul(?:y)?|Aug(?:ust)?|Sep(?:tember)?|Oct(?:ober)?|Nov(?:ember)?|Dec(?:ember)?)"
_DATE_PAT = re.compile(
    rf"\b(?:\d{{1,2}}\s+{_MONTHS}|\d{{4}}-\d{{2}}-\d{{2}}|{_MONTHS}\s+\d{{1,2}}(?:–\d{{1,2}})?)\b",
    re.IGNORECASE,
)


def _extract_date(text: str) -> str:
    m = _DATE_PAT.search(text)
    return m.group(0) if m else ""


# ---------------------------------------------------------------------------
# Inference helpers
# ---------------------------------------------------------------------------

def _infer_election_type(title: str) -> str:
    t = title.lower()
    if "presidential" in t: return "Presidential"
    if "parliamentary" in t or "parliament" in t: return "Parliamentary"
    if "general election" in t: return "General"
    if "snap election" in t: return "Snap"
    if "referendum" in t: return "Referendum"
    if "legislative" in t: return "Legislative"
    if "federal election" in t: return "Federal"
    if "local election" in t: return "Local"
    if "mayoral" in t: return "Mayoral"
    return "National"


_COUNTRY_LIST = [
    "United States", "United Kingdom", "South Korea", "North Korea",
    "South Africa", "New Zealand", "Saudi Arabia", "Sri Lanka",
    "Czech Republic", "Dominican Republic", "Republic of Congo",
    "Bosnia", "Herzegovina",
    "Germany", "France", "Italy", "Spain", "Poland", "Britain",
    "Canada", "Australia", "Japan", "India", "Pakistan",
    "Brazil", "Argentina", "Mexico", "Colombia", "Venezuela",
    "Iran", "Iraq", "Turkey", "Israel", "Egypt", "Nigeria",
    "Kenya", "Ghana", "Ukraine", "Russia", "Belarus",
    "Philippines", "Indonesia", "Thailand", "Malaysia", "Taiwan",
    "Nepal", "Bangladesh", "Myanmar", "Vietnam", "Singapore",
    "Sweden", "Norway", "Finland", "Denmark", "Netherlands",
    "Belgium", "Switzerland", "Austria", "Portugal", "Greece",
    "Hungary", "Romania", "Serbia", "Croatia",
    "Bolivia", "Peru", "Chile", "Ecuador", "Paraguay", "Uruguay",
    "Congo", "Sudan", "Ethiopia", "Somalia", "Libya", "Algeria",
    "Morocco", "Tunisia", "Senegal", "Cameroon", "Zimbabwe",
    "Georgia", "Armenia", "Azerbaijan", "Kazakhstan", "Uzbekistan",
]


def _infer_country(title: str) -> str:
    t_lower = title.lower()
    for c in _COUNTRY_LIST:
        pattern = r'\b' + re.escape(c.lower()) + r'\b'
        if re.search(pattern, t_lower):
            return c
    return ""


def _infer_category(title: str) -> str:
    t = title.lower()
    if any(k in t for k in ["war","conflict","attack","troops","military","missile","bomb","airstrike","ceasefire","siege","invasion"]):
        return "Conflict"
    if any(k in t for k in ["election","vote","parliament","coup","protest","uprising","referendum","political"]):
        return "Politics"
    if any(k in t for k in ["trade","tariff","economy","inflation","recession","gdp","imf","world bank","market","oil price","sanction"]):
        return "Economy"
    if any(k in t for k in ["climate","flood","earthquake","hurricane","wildfire","disaster","drought","tsunami","eruption"]):
        return "Climate"
    if any(k in t for k in ["pandemic","outbreak","vaccine","disease","health crisis"]):
        return "Health"
    if any(k in t for k in ["chip","semiconductor","ai ","technology","cyber","hack","space"]):
        return "Technology"
    return "Politics"


def _infer_region(title: str) -> str:
    t = title.lower()
    if any(k in t for k in ["ukraine","russia","moscow","kyiv","belarus","moldova"]):
        return "Europe / Russia"
    if any(k in t for k in ["china","beijing","taiwan","hong kong","xi jinping"]):
        return "China"
    if any(k in t for k in ["middle east","israel","gaza","iran","tehran","iraq","syria","yemen","saudi","uae","qatar","strait of hormuz"]):
        return "Middle East"
    if any(k in t for k in ["india","pakistan","afghanistan","bangladesh","sri lanka","nepal"]):
        return "South Asia"
    if any(k in t for k in ["north korea","south korea","japan","tokyo","seoul","asean","philippines","vietnam","indonesia","myanmar","singapore"]):
        return "East / Southeast Asia"
    if any(k in t for k in ["africa","nigeria","ethiopia","kenya","somalia","sudan","congo","sahel","ghana","egypt","libya"]):
        return "Africa"
    if any(k in t for k in ["europe","germany","france","italy","spain","poland","eu ","nato","britain","uk ","london","brussels","hungary"]):
        return "Europe"
    if any(k in t for k in ["latin america","brazil","argentina","mexico","colombia","venezuela","cuba","haiti","chile","peru"]):
        return "Latin America"
    return "Global"


# ---------------------------------------------------------------------------
# Section: World Org Meetings
# ---------------------------------------------------------------------------

def fetch_org_meetings() -> List[dict]:
    print("  → Fetching world org meetings...")

    rss_items = []
    for src, url in RSS_FEEDS.items():
        for item in _load_feed(src, url, _WORLD_ORG_FEED_KW, window_hours=ORG_WINDOW_HOURS):
            if _is_valid_org_item(item["title"]) and not _is_us_domestic(item["title"]):
                rss_items.append(item)

    for article in _newsapi("UN NATO G7 G20 ASEAN WTO WHO IMF World Bank summit meeting 2026")[:20]:
        title = clean_headline((article.get("title") or "").strip())
        if title and _is_valid_org_item(title) and not _is_us_domestic(title):
            rss_items.append({
                "title": title,
                "url": canonicalize_url(article.get("url") or ""),
                "source": "NewsAPI",
                "publishedAt": article.get("publishedAt"),
            })

    wiki_text = _wiki_extract("Portal:Current_events") + "\n" + _wiki_extract("United_Nations_General_Assembly")
    wiki_items = []
    seen_sigs: set = set()
    for line in [l.strip() for l in wiki_text.splitlines() if l.strip()]:
        if _is_junk(line) or _is_us_domestic(line):
            continue
        if not _is_valid_org_item(line):
            continue
        sig = _story_sig(line)
        if sig in seen_sigs:
            continue
        seen_sigs.add(sig)
        wiki_items.append({
            "title": clean_headline(line)[:200],
            "organization": _infer_org(line),
            "date": _extract_date(line),
            "location": "",
            "description": line[:300],
            "source_url": None,
        })

    all_structured = wiki_items.copy()
    for r in _cluster_and_rank(rss_items, 10):
        all_structured.append({
            "title": r["title"],
            "organization": _infer_org(r["title"]),
            "date": "",
            "location": "",
            "description": r["title"],
            "source_url": r.get("url"),
        })

    deduped = _dedup_items(all_structured)

    return [{
        "title": it.get("title", ""),
        "organization": it.get("organization") or _infer_org(it.get("title", "")),
        "date": it.get("date", ""),
        "location": it.get("location", ""),
        "description": it.get("description", it.get("title", ""))[:300],
        "source_url": it.get("source_url"),
    } for it in deduped[:5]]


# ---------------------------------------------------------------------------
# Section: Diplomatic Visits
# ---------------------------------------------------------------------------

def fetch_diplomatic_visits() -> List[dict]:
    print("  → Fetching diplomatic visits...")

    rss_items = []
    for src, url in RSS_FEEDS.items():
        for item in _load_feed(src, url, _DIPLOMATIC_FEED_KW, window_hours=DIPLOMATIC_WINDOW_HOURS):
            if _is_valid_diplomatic_item(item["title"]) and not _is_us_domestic(item["title"]):
                rss_items.append(item)

    for article in _newsapi(
        "state visit bilateral summit heads of state diplomatic foreign minister ambassador 2026"
    )[:20]:
        title = clean_headline((article.get("title") or "").strip())
        if title and _is_valid_diplomatic_item(title) and not _is_us_domestic(title):
            rss_items.append({
                "title": title,
                "url": canonicalize_url(article.get("url") or ""),
                "source": "NewsAPI",
                "publishedAt": article.get("publishedAt"),
            })

    wiki_text = _wiki_extract("Portal:Current_events")
    wiki_items = []
    seen_sigs: set = set()
    for line in [l.strip() for l in wiki_text.splitlines() if l.strip()]:
        if _is_junk(line) or _is_us_domestic(line):
            continue
        if not _is_valid_diplomatic_item(line):
            continue
        sig = _story_sig(line)
        if sig in seen_sigs:
            continue
        seen_sigs.add(sig)
        wiki_items.append({
            "title": clean_headline(line)[:200],
            "participants": _infer_participants(line),
            "date": _extract_date(line),
            "location": "",
            "description": line[:300],
            "source_url": None,
        })

    all_structured = wiki_items.copy()
    for r in _cluster_and_rank(rss_items, 10):
        all_structured.append({
            "title": r["title"],
            "participants": _infer_participants(r["title"]),
            "date": "",
            "location": "",
            "description": r["title"],
            "source_url": r.get("url"),
        })

    deduped = _dedup_items(all_structured)

    return [{
        "title": it.get("title", ""),
        "participants": it.get("participants") or _infer_participants(it.get("title", "")),
        "date": it.get("date", ""),
        "location": it.get("location", ""),
        "description": it.get("description", it.get("title", ""))[:300],
        "source_url": it.get("source_url"),
    } for it in deduped[:5]]


# ---------------------------------------------------------------------------
# Section: Elections
# ---------------------------------------------------------------------------

def _is_valid_election_item(title: str) -> bool:
    t = title.lower()
    if any(p.search(title) for p in _ELECTION_BLOCK_RE):
        return False
    if _is_us_domestic(title):
        return False
    if not any(kw in t for kw in _ELECTION_KW):
        return False
    is_opinion = re.search(
        r"\b(sign of|exhaustion|could spell|might win|may win|analysis|what it means)\b", t
    )
    is_event = re.search(
        r"\b(sweeps|wins|won|heads to polls|voted|results|campaign|candidates|held|scheduled)\b", t
    )
    if is_opinion and not is_event:
        return False
    return True


def fetch_elections() -> List[dict]:
    print("  → Fetching upcoming elections...")

    rss_items = []
    for src, url in RSS_FEEDS.items():
        for item in _load_feed(src, url, _ELECTION_KW):
            if _is_valid_election_item(item["title"]):
                rss_items.append(item)

    for article in _newsapi("election presidential parliamentary national vote 2025 2026")[:20]:
        title = clean_headline((article.get("title") or "").strip())
        if title and _is_valid_election_item(title):
            rss_items.append({
                "title": title,
                "url": canonicalize_url(article.get("url") or ""),
                "source": "NewsAPI",
                "publishedAt": article.get("publishedAt"),
            })

    wiki_text = (
        _wiki_extract("List_of_elections_in_2025") + "\n" +
        _wiki_extract("List_of_elections_in_2026") + "\n" +
        _wiki_extract("Portal:Current_events")
    )
    wiki_items = []
    seen_sigs: set = set()
    for line in [l.strip() for l in wiki_text.splitlines() if l.strip()]:
        if _is_junk(line) or not _is_valid_election_item(line):
            continue
        sig = _story_sig(line)
        if sig in seen_sigs:
            continue
        seen_sigs.add(sig)
        wiki_items.append({
            "title": clean_headline(line)[:200],
            "country": _infer_country(line),
            "election_type": _infer_election_type(line),
            "date": _extract_date(line),
            "description": line[:300],
            "source_url": None,
        })

    all_structured = wiki_items.copy()
    for r in _cluster_and_rank(rss_items, 10):
        all_structured.append({
            "title": r["title"],
            "country": _infer_country(r["title"]),
            "election_type": _infer_election_type(r["title"]),
            "date": "",
            "description": r["title"],
            "source_url": r.get("url"),
        })

    deduped = _dedup_items(all_structured)

    return [{
        "title": it.get("title", ""),
        "country": it.get("country") or _infer_country(it.get("title", "")),
        "election_type": it.get("election_type") or _infer_election_type(it.get("title", "")),
        "date": it.get("date", ""),
        "description": it.get("description", it.get("title", ""))[:300],
        "source_url": it.get("source_url"),
    } for it in deduped[:5]]


# ---------------------------------------------------------------------------
# Section: Global Events
# ---------------------------------------------------------------------------

def fetch_global_events() -> List[dict]:
    print("  → Fetching global events from RSS feeds...")
    all_items: List[dict] = []
    for src, url in RSS_FEEDS.items():
        all_items.extend(_load_feed(src, url, _GLOBAL_KW))

    print(f"     Collected {len(all_items)} relevant items from {len(RSS_FEEDS)} feeds")

    for article in _newsapi("world news conflict diplomacy election crisis 2026")[:30]:
        title = clean_headline((article.get("title") or "").strip())
        if not title or _is_junk(title):
            continue
        if not any(kw in title.lower() for kw in _GLOBAL_KW):
            continue
        src_name = (article.get("source") or {}).get("name", "NewsAPI")
        pub_str = article.get("publishedAt", "")
        try:
            dt = dtparser.parse(pub_str).replace(tzinfo=timezone.utc) if pub_str else None
        except Exception:
            dt = None
        all_items.append({
            "title": title,
            "url": canonicalize_url(article.get("url") or ""),
            "source": src_name,
            "publishedAt": dt.isoformat().replace("+00:00", "Z") if dt else None,
        })

    top5 = _cluster_and_rank(all_items, 5)
    out = []
    for rep in top5:
        toks = _tokens(rep["title"])
        covering = [it["source"] for it in all_items if _jaccard(_tokens(it["title"]), toks) >= 0.25]
        unique_covering = list(dict.fromkeys(covering))[:10]
        out.append({
            "title": rep["title"],
            "summary": rep["title"],
            "outlets_covering": unique_covering,
            "coverage_count": len(covering),
            "region": _infer_region(rep["title"]),
            "category": _infer_category(rep["title"]),
            "source_url": rep.get("url"),
        })
    return out


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def main():
    print("Starting data build...")
    now = datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")

    data = {
        "last_updated": now,
        "world_org_meetings": fetch_org_meetings(),
        "diplomatic_visits":  fetch_diplomatic_visits(),
        "elections":          fetch_elections(),
        "global_events":      fetch_global_events(),
    }

    out_dir = Path("public")
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / "data.json"
    out_path.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
    print(f"\n✅ Wrote data.json → {out_path.resolve()}")
    for section, items in data.items():
        if isinstance(items, list):
            print(f"   {section}: {len(items)} items")


if __name__ == "__main__":
    main()
