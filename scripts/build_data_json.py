from __future__ import annotations
import json
import os
import re
import time
from datetime import datetime, timezone, timedelta
from pathlib import Path
from typing import Dict, List, Optional
from urllib.parse import urlparse, parse_qs, urlencode, urlunparse
import feedparser
import requests
from dateutil import parser as dtparser

REPO_ROOT = Path(__file__).resolve().parent.parent
DOCS_DATA_PATH = REPO_ROOT / "docs" / "data.json"

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/120.0.0.0 Safari/537.36"
    ),
    "Accept": "application/rss+xml, application/xml, text/xml, */*;q=0.8",
}
TIMEOUT = 15
MAX_RETRIES = 1
RETRY_SLEEP = 1.0
WINDOW_HOURS = 168

RSS_FEEDS: Dict[str, str] = {
    "BBC World": "https://feeds.bbci.co.uk/news/world/rss.xml",
    "BBC News Home": "https://feeds.bbci.co.uk/news/rss.xml",
    "Reuters Top News": "https://feeds.reuters.com/reuters/topNews",
    "AP News": "https://apnews.com/rss",
    "CNN World": "http://rss.cnn.com/rss/edition_world.rss",
    "NPR World": "https://feeds.npr.org/1004/rss.xml",
    "PBS NewsHour": "https://www.pbs.org/newshour/feeds/rss/world",
    "CBC World": "https://rss.cbc.ca/lineup/world.xml",
    "ABC News Intl": "https://abcnews.go.com/abcnews/internationalheadlines",
    "DW World": "https://rss.dw.com/rdf/rss-en-world",
    "France24 English": "https://www.france24.com/en/rss",
    "Euronews": "https://www.euronews.com/rss?level=theme&name=news",
    "Al Jazeera English": "https://www.aljazeera.com/xml/rss/all.xml",
    "Kyiv Independent": "https://kyivindependent.com/feed/",
    "Politico US": "https://www.politico.com/rss/politicopicks.xml",
}

# --- ENHANCED FILTERING PATTERNS ---

_JUNK_RE = [re.compile(p, re.IGNORECASE) for p in [
    r"\b(horoscope|zodiac|astrology)\b", r"\b(crossword|puzzle|sudoku)\b",
    r"\b(recipe|cooking|review)\b", r"\b(nfl|nba|mlb|nhl|soccer|football|tennis)\b",
    r"\b(stock pick|coupon|discount|sale|treasury|yield|oil prices?)\b", 
    r"\b(royal fallout|memoir|interview|book review)\b"
]]

_MEETING_WORDS = r"\b(summit|assembly|session|conference|forum|convenes?|meets?|meeting)\b"
_LEADER_WORDS = r"\b(president|prime minister|pm|chancellor|envoy|ambassador|king|queen|crown prince|foreign minister|secretary of state)\b"
_DIPLOMATIC_VERBS = r"\b(visits?|travels to|arrives in|hosts?|holds talks|meets with|bilateral talks)\b"
_ELECTION_WORDS = r"\b(presidential election|parliamentary election|general election|national election|vote|ballots?|polls?)\b"

def clean_headline(title: str) -> str:
    if not title: return ""
    t = re.sub(r"<[^>]+>", "", title).strip()
    return re.sub(r"\s+", " ", t)

def _is_junk(text: str) -> bool:
    return any(p.search(text) for p in _JUNK_RE)

def canonicalize_url(url: str) -> str:
    try:
        u = urlparse(url)
        qs = parse_qs(u.query, keep_blank_values=True)
        drop = {"utm_source", "utm_medium", "utm_campaign", "utm_term", "utm_content", "fbclid", "gclid", "at_medium", "at_campaign", "cmp"}
        for k in list(qs):
            if k.lower() in drop:
                qs.pop(k)
        new_q = urlencode({k: v[0] for k, v in qs.items() if v}, doseq=True)
        return urlunparse((u.scheme, u.netloc, u.path.rstrip('/') or '/', u.params, new_q, ""))
    except Exception:
        return url

def _get(url: str) -> Optional[str]:
    sess = requests.Session()
    sess.headers.update(HEADERS)
    for attempt in range(MAX_RETRIES + 1):
        try:
            r = sess.get(url, timeout=TIMEOUT, allow_redirects=True)
            if r.status_code == 200: return r.text
        except requests.RequestException: pass
        time.sleep(RETRY_SLEEP * attempt)
    return None

def _parse_dt(entry: dict) -> Optional[datetime]:
    for k in ("published_parsed", "updated_parsed"):
        st = entry.get(k)
        if st:
            try: return datetime(*st[:6], tzinfo=timezone.utc)
            except Exception: pass
    for k in ("published", "updated"):
        v = entry.get(k)
        if v:
            try:
                dt = dtparser.parse(v)
                return dt.replace(tzinfo=timezone.utc) if dt.tzinfo is None else dt.astimezone(timezone.utc)
            except Exception: pass
    return None

_COUNTRY_MAP = {
    "German": "Germany", "Russian": "Russia", "Ukrainian": "Ukraine",
    "Brazilian": "Brazil", "British": "United Kingdom", "American": "United States",
    "French": "France", "Italian": "Italy", "Spanish": "Spain",
    "Chinese": "China", "Japanese": "Japan", "Indian": "India", "Canada": "Canada",
    "Canadian": "Canada", "Germany": "Germany", "Russia": "Russia", "Ukraine": "Ukraine"
}

def _infer_country(text: str) -> str:
    for kw, country in _COUNTRY_MAP.items():
        if re.search(r'\b' + re.escape(kw) + r'\b', text, re.IGNORECASE):
            return country
    return ""

def _infer_org(text: str) -> str:
    text_lower = text.lower()
    orgs = {
        "UN": ["united nations", " un assembly", "un security council", "un summit"],
        "G20": ["g20", "g-20 summit"], "G7": ["g7", "g-7 summit"], "BRICS": ["brics summit"], 
        "NATO": ["nato summit", "nato meeting", "nato ministers"],
        "APEC": ["apec summit"], "EU": ["european union summit", "eu leaders meeting", "eu summit"], 
        "ASEAN": ["asean summit"]
    }
    for org, kws in orgs.items():
        if any(kw in text_lower for kw in kws):
            return org
    return ""

def _is_duplicate_story(title: str, existing_items: List[dict]) -> bool:
    """Simple deduplication check based on key word overlap."""
    words_a = set(re.findall(r'\w+', title.lower())) - {"the", "a", "an", "and", "or", "in", "on", "at", "to", "for", "of", "with"}
    for item in existing_items:
        words_b = set(re.findall(r'\w+', item["title"].lower())) - {"the", "a", "an", "and", "or", "in", "on", "at", "to", "for", "of", "with"}
        overlap = len(words_a & words_b)
        if overlap >= 4 or (len(words_a) > 0 and overlap / len(words_a) > 0.6):
            return True
    return False

def fetch_all_feed_entries() -> List[dict]:
    cutoff = datetime.now(timezone.utc) - timedelta(hours=WINDOW_HOURS)
    all_entries = []
    seen_urls = set()

    for source, url in RSS_FEEDS.items():
        txt = _get(url)
        if not txt: continue
        d = feedparser.parse(txt)
        for e in getattr(d, "entries", []):
            raw_title = (e.get("title") or "").strip()
            link = canonicalize_url((e.get("link") or "").strip())
            desc = clean_headline((e.get("summary") or e.get("description") or raw_title).strip())
            
            if not raw_title or not link or link in seen_urls: continue
            
            title = clean_headline(raw_title)
            if not title or _is_junk(f"{title} {desc}"): continue
                
            dt = _parse_dt(e)
            if dt and dt < cutoff: continue
            
            seen_urls.add(link)
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
    assigned_urls = set()

    for entry in entries:
        t = entry["title"]
        d = entry["description"]
        pub_dt = entry["publishedAt"]
        url = entry["link"]
        full_text = f"{t} {d}"
        date_str = pub_dt.strftime("%Y-%m-%d") if pub_dt else datetime.now(timezone.utc).strftime("%Y-%m-%d")

        # 1. World Org Meetings (Requires explicit org + meeting verb/noun)
        org = _infer_org(full_text)
        if org and re.search(_MEETING_WORDS, full_text, re.IGNORECASE):
            if len(org_items) < 5 and not _is_duplicate_story(t, org_items):
                org_items.append({
                    "title": t,
                    "organization": org,
                    "date": date_str,
                    "location": _infer_country(full_text) or "Global",
                    "description": d,
                    "source_url": url
                })
                assigned_urls.add(url)
                continue

        # 2. Diplomatic Visits (Requires leader + diplomatic travel/meeting terms)
        has_leader = re.search(_LEADER_WORDS, full_text, re.IGNORECASE)
        has_diplomatic_action = re.search(_DIPLOMATIC_VERBS, full_text, re.IGNORECASE) or "summit" in full_text.lower()
        
        if url not in assigned_urls and has_leader and has_diplomatic_action:
            if len(diplomatic_items) < 5 and not _is_duplicate_story(t, diplomatic_items):
                diplomatic_items.append({
                    "title": t,
                    "visiting_leader": "",
                    "host_country": _infer_country(full_text) or "Global",
                    "date": date_str,
                    "description": d,
                    "source_url": url
                })
                assigned_urls.add(url)
                continue

        # 3. Real National Elections (Requires actual election keywords, excludes pure local state elections if needed)
        has_election = re.search(_ELECTION_WORDS, full_text, re.IGNORECASE)
        if url not in assigned_urls and has_election:
            if len(election_items) < 5 and not _is_duplicate_story(t, election_items):
                election_items.append({
                    "title": t,
                    "country": _infer_country(full_text) or "Global",
                    "election_type": "National",
                    "date": date_str,
                    "description": d,
                    "source_url": url
                })
                assigned_urls.add(url)
                continue

    return {
        "world_org_meetings": org_items,
        "diplomatic_visits": diplomatic_items,
        "elections": election_items
    }

def apply_carry_forward(new_data: dict, file_path: Path = DOCS_DATA_PATH) -> dict:
    if not file_path.exists(): return new_data
    try:
        with open(file_path, "r") as f:
            existing = json.load(f)
    except Exception: return new_data

    sections = ["world_org_meetings", "diplomatic_visits", "elections"]
    for sec in sections:
        current_list = new_data.get(sec, [])
        existing_list = existing.get(sec, [])
        seen_urls = {item.get("source_url") for item in current_list if item.get("source_url")}
        
        for old_item in existing_list:
            if len(current_list) >= 5: break
            url = old_item.get("source_url")
            if url and url not in seen_urls and not _is_duplicate_story(old_item["title"], current_list):
                current_list.append(old_item)
                seen_urls.add(url)
                
        new_data[sec] = current_list

    return new_data

def main():
    entries = fetch_all_feed_entries()
    fresh_data = process_sections(entries)
    final_data = apply_carry_forward(fresh_data)
    final_data["last_updated"] = datetime.now(timezone.utc).isoformat()

    DOCS_DATA_PATH.parent.mkdir(parents=True, exist_ok=True)
    with open(DOCS_DATA_PATH, "w") as f:
        json.dump(final_data, f, indent=2)
    print(f"Successfully processed {len(entries)} entries and updated {DOCS_DATA_PATH}")

if __name__ == "__main__":
    main()
