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
TIMEOUT = 15
MAX_RETRIES = 1
RETRY_SLEEP = 1.0
WINDOW_HOURS = 168  # 7 days

# 100 Reliable and Free Global News RSS Feeds
RSS_FEEDS: Dict[str, str] = {
    # Global Wire Services & Major International Outlets
    "BBC World": "https://feeds.bbci.co.uk/news/world/rss.xml",
    "BBC News Home": "https://feeds.bbci.co.uk/news/rss.xml",
    "Reuters Top News": "https://feeds.reuters.com/reuters/topNews",
    "AP News": "https://apnews.com/rss",
    "CNN World": "http://rss.cnn.com/rss/edition_world.rss",
    "CNN Top Stories": "http://rss.cnn.com/rss/edition.rss",
    "NPR World": "https://feeds.npr.org/1004/rss.xml",
    "NPR News": "https://feeds.npr.org/1001/rss.xml",
    "PBS NewsHour": "https://www.pbs.org/newshour/feeds/rss/world",
    "CBC World": "https://rss.cbc.ca/lineup/world.xml",
    "ABC News Intl": "https://abcnews.go.com/abcnews/internationalheadlines",
    "CBS News World": "https://www.cbsnews.com/latest/rss/world",
    "NBC News World": "https://feeds.nbcnews.com/nbcnews/public/world",
    "Sky News World": "https://feeds.skynews.com/feeds/rss/world.xml",
    "Fox News World": "https://moxie.foxnews.com/google-publisher/world.xml",
    "NYT World": "https://rss.nytimes.com/services/xml/rss/nyt/World.xml",
    "The Guardian World": "https://www.theguardian.com/world/rss",
    "The Guardian UK": "https://www.theguardian.com/uk/rss",
    "Wash Post World": "https://feeds.washingtonpost.com/rss/world",
    "WSJ World": "https://feeds.a.dj.com/rss/RSSWorldNews.xml",
    "FT World": "https://www.ft.com/world?format=rss",
    "Bloomberg Markets": "https://feeds.bloomberg.com/markets/news.rss",
    "The Economist": "https://www.economist.com/the-world-this-week/rss.xml",
    "Newsweek": "https://www.newsweek.com/rss",
    "Time Magazine": "https://time.com/feed/",
    "The Independent": "https://www.independent.co.uk/news/world/rss",
    "USA Today World": "https://rssfeeds.usatoday.com/usatoday-NewsTopStories",
    "LA Times World": "https://www.latimes.com/world/rss2.0.xml",
    "Chicago Tribune": "https://www.chicagotribune.com/arcio/rss/category/news/",

    # Middle East & North Africa
    "Al Jazeera English": "https://www.aljazeera.com/xml/rss/all.xml",
    "Arab News": "https://www.arabnews.com/cat/1/rss.xml",
    "The National UAE": "https://www.thenationalnews.com/arc/outboundfeeds/rss/",
    "Haaretz": "https://www.haaretz.com/cmlink/1.4678280",
    "Times of Israel": "https://www.timesofisrael.com/feed/",
    "TRT World": "https://www.trtworld.com/rss/world",
    "Middle East Eye": "https://www.middleeasteye.net/rss",
    "Asharq Al-Awsat": "https://english.aawsat.com/rss.xml",

    # Europe & Eurasia
    "DW World": "https://rss.dw.com/rdf/rss-en-world",
    "France24 English": "https://www.france24.com/en/rss",
    "Euronews": "https://www.euronews.com/rss?level=theme&name=news",
    "Politico Europe": "https://www.politico.eu/feed/",
    "Radio Free Europe": "https://www.rferl.org/api/",
    "The Local Europe": "https://www.thelocal.com/feed/",
    "Kyiv Independent": "https://kyivindependent.com/feed/",
    "The Moscow Times": "https://www.themoscowtimes.com/rss/news",
    "Irish Times": "https://www.irishtimes.com/cmlink/news-1.258270",
    "El País English": "https://english.elpais.com/rss/index.xml",
    "Swissinfo": "https://www.swissinfo.ch/eng/rss",
    "Der Spiegel English": "https://www.spiegel.de/international/index.rss",

    # Asia-Pacific
    "Times of India": "https://timesofindia.indiatimes.com/rssfeeds/-2128936835.cms",
    "The Hindu Intl": "https://www.thehindu.com/news/international/feeder/default.rss",
    "Indian Express": "https://indianexpress.com/section/world/feed/",
    "Japan Times": "https://www.japantimes.co.jp/feed/",
    "Kyodo News": "https://english.kyodonews.net/rss/news.xml",
    "NHK World": "https://www3.nhk.or.jp/nhkworld/en/news/ata glance/rss/",
    "SCMP Asia": "https://www.scmp.com/rss/91/feed",
    "Straits Times": "https://www.straitstimes.com/global/rss.xml",
    "CNA Singapore": "https://www.channelnewsasia.com/api/v1/rss-outbound/feed.xml",
    "Yonhap News": "https://en.yna.co.kr/RSS/news.xml",
    "SMH World": "https://feeds.smh.com.au/rss/world",
    "ABC Australia": "https://www.abc.net.au/news/feed/51120/rss.xml",
    "RNZ World": "https://www.rnz.co.nz/rss/world.xml",
    "Bangkok Post": "https://www.bangkokpost.com/rss/data/mostrecent.xml",
    "Jakarta Post": "https://www.thejakartapost.com/rss/paper",
    "Manila Bulletin": "https://mb.com.ph/feed",

    # Latin America & Caribbean
    "Buenos Aires Times": "https://www.batimes.com.ar/feed",
    "Rio Times": "https://www.riotimesonline.com/feed/",
    "MercoPress": "https://en.mercopress.com/rss/",
    "Reuters LatAm": "https://feeds.reuters.com/reuters/latamNews",
    "BBC Para todos": "https://www.bbc.com/mundo/index.xml",

    # Africa
    "AllAfrica Top News": "https://allafrica.com/tools/headlines/rdf/latest/headlines.rdf",
    "News24 South Africa": "https://feeds.24.com/articles/news24/SouthAfrica/rss",
    "The EastAfrican": "https://www.theeastafrican.co.ke/tea/rss/2558-2558-132d20gz/index.xml",
    "African Arguments": "https://africanarguments.org/feed/",
    "Premium Times Nigeria": "https://www.premiumtimesng.com/feed",

    # Think Tanks, Multilateral & Foreign Affairs
    "UN News": "https://news.un.org/feed/subscribe/en/news/all/rss.xml",
    "Foreign Policy": "https://foreignpolicy.com/feed/",
    "Foreign Affairs": "https://www.foreignaffairs.com/rss.xml",
    "Atlantic Council": "https://www.atlanticcouncil.org/feed/",
    "Carnegie Endowment": "https://carnegieendowment.org/rss/carnegie.xml",
    "Chatham House": "https://www.chathamhouse.org/rss/news.xml",
    "Brookings Institution": "https://www.brookings.edu/feed/",
    "CSIS": "https://www.csis.org/rss.xml",
    "Low Institute": "https://www.lowyinstitute.org/the-interpreter/rss.xml",
    "Crisis Group": "https://www.crisisgroup.org/rss",

    # Analysis, Tech & Business Politics
    "Politico US": "https://www.politico.com/rss/politicopicks.xml",
    "The Hill": "https://thehill.com/feed/",
    "Axios": "https://www.axios.com/feeds/feed.rss",
    "Vox": "https://www.vox.com/rss/index.xml",
    "Slate World": "https://slate.com/feeds/news-and-politics.rss",
    "The Intercept": "https://theintercept.com/feed/?rss",
    "ProPublica": "https://feeds.propublica.org/propublica/main",
    "The Conversation": "https://theconversation.com/us/articles.atom",
    "World Economic Forum": "https://www.weforum.org/feed/",
    "MarketWatch": "https://www.marketwatch.com/rss/topstories",
    "CNBC World": "https://www.cnbc.com/id/100003114/device/rss/rss.html",
    "Barron's": "https://feeds.a.dj.com/rss/RSSBarrons.xml",
    "Fortune": "https://fortune.com/feed/",
    "Quartz": "https://qz.com/rss",
    "Rest of World": "https://restofworld.org/feed/latest",
    "Wired Top": "https://www.wired.com/feed/rss"
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
        new_q = urlencode({k: v[0] for k, v in qs.items() if v}, doseq=True)
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

_COUNTRY_MAP = {
    "German": "Germany", "Russian": "Russia", "Ukrainian": "Ukraine",
    "Brazilian": "Brazil", "British": "United Kingdom", "American": "United States",
    "French": "France", "Italian": "Italy", "Spanish": "Spain",
    "Chinese": "China", "Japanese": "Japan", "Indian": "India", "Mexican": "Mexico",
    "Germany": "Germany", "Russia": "Russia", "Ukraine": "Ukraine",
    "Brazil": "Brazil", "United Kingdom": "United Kingdom", "United States": "United States",
    "France": "France", "Italy": "Italy", "Spain": "Spain", "Mexico": "Mexico",
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
    return datetime.now(timezone.utc).strftime("%Y-%m-%d")

def _infer_org(text: str) -> str:
    text_lower = text.lower()
    orgs = {
        "UN": ["united nations", " un ", "un assembly", "un general", "un security council"],
        "G20": ["g20", "g-20"], "G7": ["g7", "g-7"], "BRICS": ["brics"], "NATO": ["nato"],
        "APEC": ["apec"], "EU": ["european union", "eu summit"], "ASEAN": ["asean"]
    }
    for org, kws in orgs.items():
        if any(kw in text_lower for kw in kws):
            return org
    return "Global"

# Feed Fetching
def fetch_all_feed_entries() -> List[dict]:
    cutoff = datetime.now(timezone.utc) - timedelta(hours=WINDOW_HOURS)
    all_entries = []
    seen_urls = set()

    for source, url in RSS_FEEDS.items():
        txt = _get(url)
        if not txt:
            continue
        d = feedparser.parse(txt)
        for e in getattr(d, "entries", []):
            raw_title = (e.get("title") or "").strip()
            link = canonicalize_url((e.get("link") or "").strip())
            desc = clean_headline((e.get("summary") or e.get("description") or raw_title).strip())
            
            if not raw_title or not link or link in seen_urls:
                continue
            
            title = clean_headline(raw_title)
            if not title or _is_junk(title):
                continue
                
            dt = _parse_dt(e)
            if dt and dt < cutoff:
                continue
            
            seen_urls.add(link)
            all_entries.append({
                "title": title,
                "link": link,
                "source": source,
                "publishedAt": dt,
                "description": desc
            })
    return all_entries

# Processing and Categorization Logic
def process_sections(entries: List[dict]) -> dict:
    org_items = []
    diplomatic_items = []
    election_items = []
    global_items = []

    _DIPLOMATIC_KW = [r"\bvisit\b", r"\bmeets?\b", r"\bmet\b", r"\btalks\b", r"\bsummit\b", r"\btravels to\b", r"\barrives in\b"]
    _ELECTION_KW = [r"\belection\b", r"\bpresidential vote\b", r"\bparliamentary vote\b", r"\bballots\b"]

    assigned_urls = set()

    for entry in entries:
        t = entry["title"]
        d = entry["description"]
        pub_dt = entry["publishedAt"]
        url = entry["link"]
        src = entry["source"]
        full_text = f"{t} {d}"

        # 1. World Org Meetings
        org = _infer_org(full_text)
        if len(org_items) < 5 and org != "Global":
            org_items.append({
                "title": t,
                "organization": org,
                "date": _extract_date(full_text, pub_dt),
                "location": _infer_country(full_text) or "Global",
                "description": d,
                "source_url": url
            })
            assigned_urls.add(url)
            continue

        # 2. Diplomatic Visits
        if url not in assigned_urls and any(re.search(kw, full_text, re.IGNORECASE) for kw in _DIPLOMATIC_KW):
            if len(diplomatic_items) < 5:
                diplomatic_items.append({
                    "title": t,
                    "visiting_leader": "",
                    "host_country": _infer_country(full_text) or "Global",
                    "date": _extract_date(full_text, pub_dt),
                    "description": d,
                    "source_url": url
                })
                assigned_urls.add(url)
                continue

        # 3. Elections
        if url not in assigned_urls and any(re.search(kw, full_text, re.IGNORECASE) for kw in _ELECTION_KW):
            if len(election_items) < 5:
                election_items.append({
                    "title": t,
                    "country": _infer_country(full_text) or "Global",
                    "election_type": "National",
                    "date": _extract_date(full_text, pub_dt),
                    "description": d,
                    "source_url": url
                })
                assigned_urls.add(url)
                continue

        # 4. Global Events Coverage Aggregation
        if url not in assigned_urls:
            # Check if story exists in global_items to consolidate source coverage
            matched = False
            for g_item in global_items:
                # Basic token-overlap similarity check for multi-outlet coverage
                t_words = set(re.findall(r"\w+", t.lower()))
                g_words = set(re.findall(r"\w+", g_item["title"].lower()))
                overlap = len(t_words & g_words) / max(len(t_words), 1)
                
                if overlap > 0.6:
                    if src not in g_item["outlets_covering"]:
                        g_item["outlets_covering"].append(src)
                        g_item["coverage_count"] += 1
                    matched = True
                    assigned_urls.add(url)
                    break
            
            if not matched and len(global_items) < 5:
                global_items.append({
                    "title": t,
                    "summary": d,
                    "outlets_covering": [src],
                    "coverage_count": 1,
                    "region": _infer_country(full_text) or "Global",
                    "category": "General",
                    "source_url": url
                })
                assigned_urls.add(url)

    return {
        "world_org_meetings": org_items,
        "diplomatic_visits": diplomatic_items,
        "elections": election_items,
        "global_events": global_items
    }

def apply_carry_forward(new_data: dict, file_path: str = "public/data.json") -> dict:
    """Carries forward historical records if fresh scrape yields fewer than 5 items."""
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
    
    # Preserve 5-slot targets using existing JSON data
    final_data = apply_carry_forward(fresh_data, "public/data.json")
    final_data["last_updated"] = datetime.now(timezone.utc).isoformat()

    os.makedirs("public", exist_ok=True)
    with open("public/data.json", "w") as f:
        json.dump(final_data, f, indent=2)
    print(f"Successfully processed {len(entries)} entries across 100 feeds and updated public/data.json")

if __name__ == "__main__":
    main()
