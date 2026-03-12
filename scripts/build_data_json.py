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

import hashlib
import json
import os
import re
import time
from collections import defaultdict
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
WINDOW_HOURS = 96
NEWSAPI_KEY = os.environ.get("NEWSAPI_KEY", "")

# ---------------------------------------------------------------------------
# 40 major English-language RSS feeds
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
    r"\bnfl (draft|trade|score)\b",
    r"\bnba (trade|score|roster)\b",
    r"\b(stock pick|best deal|coupon|discount)\b",
    r"\btop \d+ (tips|ways|hacks)\b",
    r"^(weather forecast|today.s weather)\b",
    r"\b(movie|film|album|book|tv) review\b",
    r"^\s*(gallery|podcast|subscribe)\b",
    r"\b(viral|trending|tiktok)\b",
    r"\b(lottery|jackpot)\b",
]]


def _is_junk(title: str) -> bool:
    return any(p.search(title) for p in _JUNK_RE)


# ---------------------------------------------------------------------------
# Relevance keywords per section
# ---------------------------------------------------------------------------

_WORLD_ORG_KW = [
    "united nations", " un ", "un general assembly", "un security council",
    "g7", "g20", "nato", "european union", " eu ", "eu summit", "eu council",
    "asean", "apec", "african union", " au ", "wto", "imf", "world bank",
    "world health", " who ", "cop ", "climate summit", "opec", "opec+",
    "arab league", "brics", "sco ", "shanghai cooperation",
    "organization of american", " oas ",
]

_DIPLOMATIC_KW = [
    "state visit", "bilateral", "summit", "diplomatic visit",
    "foreign minister", "secretary of state", "presidential visit",
    "prime minister visit", "official visit", "talks between",
    "meeting between", "heads of state", "heads-of-state",
    "ambassador", "embassy", "diplomatic talks",
]

_ELECTION_KW = [
    "election", "presidential election", "parliamentary election",
    "general election", "legislative election", "referendum",
    "snap election", "federal election", "national election",
    "goes to polls", "voters head", "polling day",
]

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
    "not","but","are","its","also","when","who","what","where","how",
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

def _load_feed(source: str, url: str, keywords: List[str]) -> List[dict]:
    txt = _get(url)
    if not txt:
        return []
    d = feedparser.parse(txt)
    cutoff = datetime.now(timezone.utc) - timedelta(hours=WINDOW_HOURS)
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
# Deduplication + ranking
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
        score = unique_sources * 1_000_000 + ts
        scored.append((score, rep))

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
# Calendar text parser
# ---------------------------------------------------------------------------

_MONTHS = r"(?:Jan(?:uary)?|Feb(?:ruary)?|Mar(?:ch)?|Apr(?:il)?|May|Jun(?:e)?|Jul(?:y)?|Aug(?:ust)?|Sep(?:tember)?|Oct(?:ober)?|Nov(?:ember)?|Dec(?:ember)?)"
_DATE_PAT = re.compile(
    rf"\b(?:\d{{1,2}}\s+{_MONTHS}|\d{{4}}-\d{{2}}-\d{{2}}|{_MONTHS}\s+\d{{1,2}}(?:–\d{{1,2}})?)\b",
    re.IGNORECASE,
)


def _extract_date(text: str) -> str:
    m = _DATE_PAT.search(text)
    return m.group(0) if m else ""


def _parse_calendar_items(
    raw_text: str,
    keywords: List[str],
    extra_context_kw: List[str],
    limit: int,
    section_name: str,
) -> List[dict]:
    items = []
    seen_sigs: set = set()
    lines = [l.strip() for l in raw_text.splitlines() if l.strip()]
    for line in lines:
        if _is_junk(line):
            continue
        low = line.lower()
        if not any(kw in low for kw in keywords):
            continue
        has_date = bool(_DATE_PAT.search(line))
        has_ctx = any(k in low for k in extra_context_kw)
        if not has_date and not has_ctx:
            continue
        sig = _story_sig(line)
        if sig in seen_sigs:
            continue
        seen_sigs.add(sig)
        date_str = _extract_date(line)
        items.append({
            "title": clean_headline(line)[
