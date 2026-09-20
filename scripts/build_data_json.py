"""
Builds data.json with four sections:
  - world_org_meetings (top 5 major world organization meetings)
  - diplomatic_visits (top 5 major diplomatic visits)
  - elections (top 5 major upcoming or active elections)
  - global_events (top 5 unique global stories across RSS feeds)

Carry-forward rule:
  Preserves existing entries from previous runs to fill empty or sub-5 slots.
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

# Configuration
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
WINDOW_HOURS = 168  # 7 days
NEWSAPI_KEY = os.environ.get("NEWSAPI_KEY", "")

RSS_FEEDS: Dict[str, str] = {
    "BBC World": "https://feeds.bbci.co.uk/news/world/rss.xml",
    "Reuters": "https://feeds.reuters.com/reuters/topNews",
    "AP News": "https://apnews.com/rss",
    "CNN World": "https://rss.cnn.com/rss/edition_world.rss",
    "NPR World": "https://feeds.npr.org/1004/rss.xml",
    "PBS NewsHour": "https://www.pbs.org/newshour/feeds/rss/world",
    "CBC World": "https://rss.cbc.ca/lineup/world.xml",
    "ABC News Intl": "https://abcnews.go.com/abcnews/internationalheadlines",
    "CBS News World": "https://www.cbsnews.com/latest/rss/world",
    "NBC News World": "https://feeds.nbcnews.com/nbcnews/public/world",
    "Sky News World": "https://feeds.skynews.com/feeds/rss/world.xml",
    "Fox News World": "https://moxie.foxnews.com/google-publisher/world.xml",
    "NYT World": "https://rss.nytimes.com/services/xml/rss/nyt/World.xml",
    "The Guardian World": "https://www.theguardian.com/world/rss",
    "Wash Post World": "https://feeds.washingtonpost.com/rss/world",
    "WSJ World": "https://www.wsj.com/xml/rss/3_7085.xml",
    "FT": "https://feeds.ft.com/rss/home/uk",
    "Bloomberg": "https://feeds.bloomberg.com/markets/news.rss",
    "The Economist": "https://www.economist.com/the-world-this-week/rss.xml",
    "Newsweek": "https://www.newsweek.com/rss",
    "Time": "https://time.com/feed/",
    "The Independent": "https://www.independent.co.uk/news/world/rss",
    "USA Today World": "https://rssfeeds.usatoday.com/usatoday-NewsTopStories",
    "Al Jazeera": "https://www.aljazeera.com/xml/rss/all.xml",
    "DW World": "https://rss.dw.com/rdf/rss-en-world",
    "France24": "https://www.france24.com/en/rss",
    "Times of India": "https://timesofindia.indiatimes.com/rssfeeds/-2128936835.cms",
    "Japan Times": "https://www.japantimes.co.jp/feed/",
    "The Hindu Intl": "https://www.thehindu.com/news/international/feeder/default.rss",
    "SCMP": "https://www.scmp.com/rss/4/feed",
    "Straits Times": "https://www.straitstimes.com/global/rss.xml",
    "SMH World": "https://feeds.smh.com.au/rss/world",
    "UN News": "https://news.un.org/feed/subscribe/en/news/all/rss.xml",
    "Foreign Policy": "https://foreignpolicy.com/feed/",
    "Atlantic Council": "https://www.atlanticcouncil.org/feed/",
    "Carnegie": "https://carnegieendowment.org/rss/carnegie.xml",
    "Politico Intl": "https://www.politico.com/rss/politics08.xml",
    "The Hill": "https://thehill.com/feed/",
    "Axios": "https://www.axios.com/feeds/feed.rss",
    "Vox": "https://www.vox.com/rss/index.xml",
}

# Helpers: Cleaning and Normalization
_PREFIX_DROPS = [
    r"^watch( now)?:\s*", r"^live( now)?:\s*", r"^video:\s*",
    r"^analysis:\s*", r"^explainer:\s*", r"^opinion:\s*",
    r"^what to know:\s*", r"^fact check:\s*", r"^breaking:\s*",
]
_SUFFIX_DROPS = [
    r"\s*[-|]\s*(ap news|reuters|bbc news?|pbs newshour?|cbc news?|the guardian|dw|npr|cnn|fox news)\s*$",
]

def clean_headline(title: str) -> str:
    if not title:
        return ""
    t = title.strip()
    for p in _PREFIX_DROPS:
        t = re.sub(p, "", t, flags=re.IGNORECASE)
    for p in _SUFFIX_DROPS:
        t = re.sub(p, "", t, flags=re.IGNORECASE)
    return re.sub(r"\s+", " ", t).strip()

_JUNK_RE = [re.compile(p, re.IGNORECASE) for p in [
    r"\b(horoscope|zodiac|astrology)\b", r"\b(crossword|puzzle|sudoku)\b",
    r"\b(recipe|cooking|review)\b", r"\b(nfl|nba|mlb|nhl|soccer|football|tennis)\b",
    r"\b(stock pick|coupon|discount|sale)\b", r"\b(weather forecast)\b",
]]

def _is_junk(title: str) -> bool:
    return any(p.search(title) for p in _JUNK_RE)

def canonicalize_url(url: str) -> str:
    try:
        u = urlparse(url)
        qs = parse_qs(u.query, keep_blank_values=True)
        drop = {"utm_source", "utm_medium", "utm_campaign", "utm_term", "utm_content", "fbclid", "gclid"}
        for k in list(qs):
            if k.lower() in drop:
                qs.pop(k)
        new_q = urlencode({k: v[0] for k, v in qs.items() if v})
        path = u.path.rstrip("/") or "/"
        return urlunparse((u.scheme, u.netloc, path, u.params, new_q, ""))
    except Exception:
        return url

def _get(url: str) -> Optional[str]:
    sess = requests.Session()
    sess.headers.update(HEADERS)
    for attempt in range(MAX_RETRIES + 1):
        try:
            r = sess.get(url, timeout=TIMEOUT, allow_redirects=True)
            if r.status_code == 200:
                return r.text
        except requests.RequestException:
            pass
        time.sleep(RETRY_SLEEP * attempt)
    return None

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

# Inference Helpers
_COUNTRY_MAP = {
    "German": "Germany", "Russian": "Russia", "Ukrainian": "Ukraine",
    "Brazilian": "Brazil", "British": "United Kingdom", "American": "United States",
    "French": "France", "Italian": "Italy", "Spanish": "Spain",
    "Chinese": "China", "Japanese": "Japan", "Indian": "India",
    "Germany": "Germany", "Russia": "Russia", "Ukraine": "Ukraine",
    "Brazil": "Brazil", "United Kingdom": "United Kingdom", "United States": "United States",
    "France": "France", "Italy": "Italy", "Spain": "Spain",
    "China": "China", "Japan": "Japan", "India": "India", "Taiwan": "Taiwan"
}

def _infer_country(text: str) -> str:
    for kw, country in _COUNTRY_MAP.items():
        if re.search(r'\b' + re.escape(kw) + r'\b', text, re.IGNORECASE):
            return country
    return ""

_MONTHS = r"(?:Jan(?:uary)?|Feb(?:ruary)?|Mar(?:ch)?|Apr(?:il)?|May|Jun(?:e)?|Jul(?:y)?|Aug(?:ust)?|Sep(?:tember)?|Oct(?:ober)?|Nov(?:ember)?|Dec(?:ember)?)"
_DATE_PAT = re.compile(rf"\b(?:\d{{1,2}}\s+{_MONTHS}|\d{{4}}-\d{{2}}-\d{{2}}|{_MONTHS}\s+\d{{1,2}}(?:–\d{{1,2}})?)\b", re.IGNORECASE)

def _extract_date(text: str, pub_dt: Optional[datetime] = None) -> str:
    m = _DATE_PAT.search(text)
    if m:
        return m.group(0)
    if pub_dt:
        return pub_dt.strftime("%Y-%m-%d")
    return ""

def _infer_org(text: str) -> str:
    text_lower = text.lower()
    orgs = {
        "UN": ["united nations", " un ", "un assembly", "un general", "un security"],
        "G20": ["g20"], "G7": ["g7"], "BRICS": ["brics"], "NATO": ["nato"],
        "APEC": ["apec"], "EU": ["european union", "eu summit"], "ASEAN": ["asean"]
    }
    for org, kws in orgs.items():
        if any(kw in text_lower for kw in kws):
            return org
    return "Global"

# Feed Loaders
def fetch_all_feed_entries() -> List[dict]:
    cutoff = datetime.now(timezone.utc) - timedelta(hours=WINDOW_HOURS)
    all_entries = []
    for source, url in RSS_FEEDS.items():
        txt = _get(url)
        if not txt:
            continue
        d = feedparser.parse(txt)
        for e in getattr(d, "entries", []):
            raw_title = (e.get("title") or "").strip()
            link = canonicalize_url((e.get("link") or "").strip())
            desc = clean_headline((e.get("summary") or e.get("description") or raw_title).strip())
            if not raw_title or not link:
                continue
            title = clean_headline(raw_title)
            if not title or _is_junk(title):
                continue
            dt = _parse_dt(e)
            if dt and dt < cutoff:
                continue
            all_entries.append({
                "title": title,
                "link": link,
                "source": source,
                "publishedAt": dt,
                "description": desc
            })
    return all_entries

def process_sections(entries: List[dict]) -> dict:
    org_items = []
    diplomatic_items = []
    election_items = []
    global_items = []

    _DIPLOMATIC_KW = [r"\bvisit\b", r"\bmeets?\b", r"\bmet\b", r"\btalks\b", r"\bsummit\b", r"\btravels to\b", r"\barrives in\b"]
    _ELECTION_KW = [r"\belection\b", r"\bpolls\b", r"\bvoters\b", r"\bvote\b", r"\bballot\b"]

    for entry in entries:
        t = entry["title"]
        d = entry["description"]
        pub_dt = entry["publishedAt"]
        full_text = f"{t} {d}"

        # World Org Meetings
        org = _infer_org(full_text)
        if org != "Global" or any(k in full_text.lower() for k in ["summit", "assembly", "conference", "meeting"]):
            if len(org_items) < 10 and org != "Global":
                org_items.append({
                    "title": t,
                    "organization": org,
                    "date": _extract_date(full_text, pub_dt),
                    "location": _infer_country(full_text),
                    "description": d,
                    "source_url": entry["link"]
                })

        # Diplomatic Visits
        if any(re.search(kw, full_text, re.IGNORECASE) for kw in _DIPLOMATIC_KW):
            if len(diplomatic_items) < 10:
                diplomatic_items.append({
                    "title": t,
                    "visiting_leader": "",
                    "host_country": _infer_country(full_text),
                    "date": _extract_date(full_text, pub_dt),
                    "description": d,
                    "source_url": entry["link"]
                })

        # Elections
        if any(re.search(kw, full_text, re.IGNORECASE) for kw in _ELECTION_KW):
            if len(election_items) < 10:
                election_items.append({
                    "title": t,
                    "country": _infer_country(full_text),
                    "election_type": "National",
                    "date": _extract_date(full_text, pub_dt),
                    "description": d,
                    "source_url": entry["link"]
                })

        # Global Events
        if len(global_items) < 5:
            global_items.append({
                "title": t,
                "summary": d,
                "outlets_covering": [entry["source"]],
                "coverage_count": 1,
                "region": _infer_country(full_text) or "Global",
                "category": "General",
                "source_url": entry["link"]
            })

    return {
        "world_org_meetings": org_items[:5],
        "diplomatic_visits": diplomatic_items[:5],
        "elections": election_items[:5],
        "global_events": global_items[:5]
    }

def apply_carry_forward(new_data: dict, file_path: str = "public/data.json") -> dict:
    """Applies slot-filling logic using existing data.json records."""
    if not os.path.exists(file_path):
        return new_data

    try:
        with open(file_path, "r") as f:
            existing = json.load(f)
    except Exception:
        return new_data

    sections = ["world_org_meetings", "diplomatic_visits", "elections", "global_events"]
    
    for sec in sections:
        current_list = new_data.get(sec, [])
        existing_list = existing.get(sec, [])
        
        seen_urls = {item.get("source_url") for item in current_list if item.get("source_url")}
        
        # Fill remaining slots up to 5 items using old valid data
        for old_item in existing_list:
            if len(current_list) >= 5:
                break
            url = old_item.get("source_url")
            if url and url not in seen_urls:
                current_list.append(old_item)
                seen_urls.add(url)
                
        new_data[sec] = current_list

    return new_data

def main():
    entries = fetch_all_feed_entries()
    fresh_data = process_sections(entries)
    
    # Carry forward historical data to maintain full 5-slot targets
    final_data = apply_carry_forward(fresh_data, "public/data.json")
    final_data["last_updated"] = datetime.now(timezone.utc).isoformat()

    os.makedirs("public", exist_ok=True)
    with open("public/data.json", "w") as f:
        json.dump(final_data, f, indent=2)
    print("Successfully updated public/data.json")

if __name__ == "__main__":
    main()
