"""
Israel–Iran Crisis Map — Live Update Server
Serves on port 6161.
- Fetches RSS feeds every 10 minutes for strike news.
- Scrapes DXB flight arrivals/departures from avionio.com every 10 minutes.
"""

import json
import os
import threading
import time
import hashlib
import re
import ssl
from datetime import datetime, timezone, timedelta
from http.server import HTTPServer, BaseHTTPRequestHandler
from urllib.request import urlopen, Request
from urllib.error import URLError
from urllib.parse import urlparse
import xml.etree.ElementTree as ET

PORT = int(os.environ.get('PORT', 6161))
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
UPDATE_INTERVAL = 600  # 10 minutes

# SSL context that skips verification (some sites have chain issues)
SSL_CTX = ssl.create_default_context()
SSL_CTX.check_hostname = False
SSL_CTX.verify_mode = ssl.CERT_NONE

# ── RSS Feeds to monitor ───────────────────────────────────────────────────
RSS_FEEDS = [
    "https://www.aljazeera.com/xml/rss/all.xml",
    "https://feeds.bbci.co.uk/news/world/middle_east/rss.xml",
    "https://moxie.foxnews.com/google-publisher/world.xml",
    "https://rss.nytimes.com/services/xml/rss/nyt/MiddleEast.xml",
    "https://feeds.reuters.com/reuters/topNews",
    "https://www.jpost.com/rss/rssfeedsfrontpage.aspx",
]

# Keywords to filter Israel-Iran related articles
ISRAEL_KEYWORDS   = ['israel', 'idf', 'mossad', 'iaf', 'tel aviv', 'haifa', 'jerusalem',
                      'operation roaring', 'operation rising', 'operation epic']
IRAN_KEYWORDS     = ['iran', 'irgc', 'tehran', 'isfahan', 'natanz', 'khamenei',
                      'iranian', 'houthi', 'hezbollah']
STRIKE_KEYWORDS   = ['strike', 'attack', 'bomb', 'missile', 'drone', 'airstrike',
                      'explosion', 'kill', 'dead', 'casualt', 'wound', 'hit']

# Location → coordinates mapping for parsing new articles
LOCATION_COORDS = {
    'tehran':      (35.6892, 51.3890),
    'isfahan':     (32.6546, 51.6680),
    'natanz':      (33.7228, 51.7260),
    'qom':         (34.6416, 50.8746),
    'karaj':       (35.8400, 50.9391),
    'kermanshah':  (34.3277, 47.0785),
    'fordow':      (34.8851, 49.2195),
    'arak':        (34.0892, 49.8497),
    'minab':       (27.1499, 57.0816),
    'khorramabad': (33.4876, 48.3558),
    'lamerd':      (27.3422, 53.1888),
    'shiraz':      (29.5918, 52.5837),
    'tabriz':      (38.0962, 46.2738),
    'urmia':       (37.5527, 45.0761),
    'bushehr':     (28.9234, 50.8203),
    'zanjan':      (36.6736, 48.4787),
    'ilam':        (33.6374, 46.4227),
    'damavand':    (35.7198, 52.0657),
    'ahvaz':       (31.3183, 48.6706),
    'mashhad':     (36.2972, 59.6067),
    'tel aviv':    (32.0853, 34.7818),
    'haifa':       (32.8191, 34.9983),
    'jerusalem':   (31.7683, 35.2137),
    'bat yam':     (32.0169, 34.7506),
    'rehovot':     (31.8969, 34.8119),
    'dubai':       (25.2048, 55.2708),
    'abu dhabi':   (24.4539, 54.3773),
    'doha':        (25.2854, 51.5310),
    'manama':      (26.2285, 50.5860),
    'kuwait':      (29.3759, 47.9774),
    'riyadh':      (24.6877, 46.7219),
    'amman':       (31.9454, 35.9284),
    'baghdad':     (33.3152, 44.3661),
    'beirut':      (33.8938, 35.5018),
    'damascus':    (33.5138, 36.2765),
    'muscat':      (23.6140, 58.5922),
    'cyprus':      (35.1264, 33.4299),
}

COUNTRY_MAP = {
    'tehran': 'Iran', 'isfahan': 'Iran', 'natanz': 'Iran', 'qom': 'Iran',
    'karaj': 'Iran', 'kermanshah': 'Iran', 'fordow': 'Iran', 'arak': 'Iran',
    'minab': 'Iran', 'khorramabad': 'Iran', 'lamerd': 'Iran', 'shiraz': 'Iran',
    'tabriz': 'Iran', 'urmia': 'Iran', 'bushehr': 'Iran', 'zanjan': 'Iran',
    'ilam': 'Iran', 'damavand': 'Iran', 'ahvaz': 'Iran', 'mashhad': 'Iran',
    'tel aviv': 'Israel', 'haifa': 'Israel', 'jerusalem': 'Israel',
    'bat yam': 'Israel', 'rehovot': 'Israel',
    'dubai': 'UAE', 'abu dhabi': 'UAE',
    'doha': 'Qatar', 'manama': 'Bahrain', 'kuwait': 'Kuwait',
    'riyadh': 'Saudi Arabia', 'amman': 'Jordan', 'baghdad': 'Iraq',
    'beirut': 'Lebanon', 'damascus': 'Syria', 'muscat': 'Oman', 'cyprus': 'Cyprus',
}

# ── DXB Flight Scraper ────────────────────────────────────────────────────
AVIONIO_BASE = 'https://www.avionio.com/en/airport/dxb'
AIRLINE_CODES = {
    'EK': 'Emirates', 'FZ': 'flydubai', 'QR': 'Qatar Airways',
    'EY': 'Etihad', 'SV': 'Saudia', 'GF': 'Gulf Air',
    'AI': 'Air India', 'TK': 'Turkish Airlines', 'BA': 'British Airways',
    'LH': 'Lufthansa', 'AF': 'Air France', 'KL': 'KLM',
    'SQ': 'Singapore Airlines', 'CX': 'Cathay Pacific', 'QF': 'Qantas',
    'WY': 'Oman Air', 'MS': 'EgyptAir', 'RJ': 'Royal Jordanian',
    'EW': 'Eurowings', 'U2': 'easyJet', 'FR': 'Ryanair',
    'CY': 'Cyprus Airways', 'TP': 'TAP Air Portugal',
    'AY': 'Finnair', 'SK': 'SAS', 'OS': 'Austrian',
    'IB': 'Iberia', 'VY': 'Vueling', 'W6': 'Wizz Air',
    '6E': 'IndiGo', 'SG': 'SpiceJet', 'IX': 'Air India Express',
    'PK': 'Pakistan International', 'PA': 'Airblue',
    'XY': 'flynas', 'F3': 'Flyadeal',
    'UL': 'SriLankan', 'UX': 'Air Europa', 'HY': 'Uzbekistan Airways',
    'KC': 'Air Astana', 'TG': 'Thai Airways', 'MH': 'Malaysia Airlines',
    'GA': 'Garuda Indonesia', 'PR': 'Philippine Airlines',
    'CA': 'Air China', 'MU': 'China Eastern', 'CZ': 'China Southern',
}

STATUS_COLORS = {
    'cancelled':  '#e63946',
    'canceled':   '#e63946',
    'diverted':   '#ff6b35',
    'delayed':    '#ff9900',
    'boarding':   '#00ccff',
    'departed':   '#2dc653',
    'arrived':    '#2dc653',
    'landed':     '#2dc653',
    'on time':    '#2dc653',
    'estimated':  '#a0c4ff',
    'scheduled':  '#c0c0c0',
    'unknown':    '#666680',
}

# Historical DXB data from documented news (airport was closed/limited Feb 28 - Mar 4)
HISTORICAL_DXB = [
    # Feb 28 — Full shutdown (Iranian missiles hit UAE, airport attacked)
    {"date":"28 Feb 2026","time":"00:00","flight":"ALL","airline":"ALL AIRLINES","destination":"—","iata":"—","direction":"DEP","status":"Suspended","status_color":"#e63946","source":"news","note":"Full airport shutdown — Iranian ballistic missile & drone strikes on UAE"},
    {"date":"28 Feb 2026","time":"00:00","flight":"ALL","airline":"ALL AIRLINES","destination":"—","iata":"—","direction":"ARR","status":"Suspended","status_color":"#e63946","source":"news","note":"DXB hit by Iranian attack. 1,800+ flights cancelled on day 1."},
    # Mar 1 — Still closed
    {"date":"01 Mar 2026","time":"00:00","flight":"ALL","airline":"ALL AIRLINES","destination":"—","iata":"—","direction":"DEP","status":"Suspended","status_color":"#e63946","source":"news","note":"DXB remains closed. Emirates, Etihad, flydubai all grounded. 3,400+ cancellations."},
    {"date":"01 Mar 2026","time":"00:00","flight":"ALL","airline":"ALL AIRLINES","destination":"—","iata":"—","direction":"ARR","status":"Suspended","status_color":"#e63946","source":"news","note":"Airspace restricted. Over 19,000 regional flights disrupted since Feb 28."},
    # Mar 2 — Limited resumption from evening
    {"date":"02 Mar 2026","time":"18:00","flight":"EK REPATRIATION","airline":"Emirates","destination":"Various","iata":"—","direction":"DEP","status":"Limited Ops","status_color":"#ff9900","source":"news","note":"Limited repatriation flights resume from DXB from 18:00 onwards. Emirates freighters also operating."},
    {"date":"02 Mar 2026","time":"18:30","flight":"FZ SELECT","airline":"flydubai","destination":"Select routes","iata":"—","direction":"DEP","status":"Limited Ops","status_color":"#ff9900","source":"news","note":"flydubai resumes select routes as Dubai Airports announces limited resumption."},
    # Mar 3 — Partial operations, ~40 flights
    {"date":"03 Mar 2026","time":"06:00","flight":"EK001","airline":"Emirates","destination":"London Heathrow","iata":"LHR","direction":"DEP","status":"Operated","status_color":"#2dc653","source":"news","note":"Repatriation flight. Emirates operating ~63 flights total this day."},
    {"date":"03 Mar 2026","time":"08:00","flight":"EY101","airline":"Etihad","destination":"Abu Dhabi","iata":"AUH","direction":"ARR","status":"Operated","status_color":"#2dc653","source":"news","note":"Limited Etihad operations. Most Etihad scheduled flights remain suspended until Mar 8."},
    {"date":"03 Mar 2026","time":"10:30","flight":"FZ SELECT","airline":"flydubai","destination":"Multiple","iata":"—","direction":"DEP","status":"Partial","status_color":"#ff9900","note":"flydubai resumes scheduled flights to select destinations. Some routes still impacted by airspace restrictions."},
    # Mar 4 — ~80 flights
    {"date":"04 Mar 2026","time":"Various","flight":"127 TOTAL","airline":"Emirates / flydubai / 20+ others","destination":"Various","iata":"—","direction":"DEP+ARR","status":"Limited Ops","status_color":"#ff9900","source":"news","note":"127 flights scheduled (63 Emirates, 46 flydubai, ~18 others). Etihad/Emirates scheduled flights still suspended until Mar 8."},
]

def scrape_dxb_flights(direction='departures', date_str=None):
    """Scrape DXB flight data from avionio.com. Returns list of flight dicts."""
    url = f'{AVIONIO_BASE}/{direction}'
    if date_str:
        url += f'?date={date_str}'
    data = fetch_url(url, timeout=15, use_browser_headers=True)
    if not data:
        return []
    html = data.decode('utf-8', errors='replace')
    rows = re.findall(r'<tr[^>]*class="tt-r[^"]*"[^>]*>(.*?)</tr>', html, re.DOTALL)
    flights = []
    for row in rows:
        cells = re.findall(r'<td[^>]*>(.*?)</td>', row, re.DOTALL)
        clean = [re.sub(r'<[^>]+>', '', c).strip() for c in cells]
        if len(clean) < 6:
            continue
        time_val   = clean[0] if clean[0] else '—'
        date_val   = clean[1] if len(clean) > 1 else '—'
        iata       = clean[2] if len(clean) > 2 else '—'
        city       = clean[3] if len(clean) > 3 else '—'
        flight_no  = clean[4] if len(clean) > 4 else '—'
        airline    = re.sub(r'\s+\d+$', '', clean[5]).strip() if len(clean) > 5 else '—'
        status_raw = clean[6] if len(clean) > 6 else 'Unknown'

        # Normalise status
        sl = status_raw.lower()
        color = '#c0c0c0'
        for kw, col in STATUS_COLORS.items():
            if kw in sl:
                color = col
                break

        # flight number → airline prefix lookup
        prefix = re.match(r'^([A-Z]{2})', flight_no)
        if prefix and airline == '—':
            airline = AIRLINE_CODES.get(prefix.group(1), airline)

        flights.append({
            "date":         date_val,
            "time":         time_val,
            "flight":       flight_no,
            "airline":      airline,
            "iata":         iata,
            "destination":  city,
            "direction":    "DEP" if direction == "departures" else "ARR",
            "status":       status_raw,
            "status_color": color,
            "source":       "live",
        })
    return flights


def refresh_flights():
    """Fetch today's DXB departures and arrivals, merge with history."""
    today = datetime.now(timezone.utc).strftime('%Y-%m-%d')
    deps = scrape_dxb_flights('departures', today)
    arrs = scrape_dxb_flights('arrivals', today)
    live = deps + arrs

    # Sort live by time
    live.sort(key=lambda x: x.get('time', '00:00'))

    with flight_lock:
        flight_state['live_flights']    = live
        flight_state['last_refresh']    = datetime.now(timezone.utc).strftime('%d %b %Y %H:%M UTC')
        flight_state['dep_count']       = len(deps)
        flight_state['arr_count']       = len(arrs)
        flight_state['cancelled_count'] = sum(1 for f in live if 'cancel' in f['status'].lower())

    print(f"[{datetime.now().strftime('%H:%M:%S')}] DXB flights: {len(deps)} dep, {len(arrs)} arr, "
          f"{flight_state['cancelled_count']} cancelled.")


def flight_loop():
    while True:
        try:
            refresh_flights()
        except Exception as e:
            print(f"Flight loop error: {e}")
        time.sleep(UPDATE_INTERVAL)


# ── Global state ───────────────────────────────────────────────────────────
flight_state = {
    "live_flights":    [],
    "last_refresh":    None,
    "dep_count":       0,
    "arr_count":       0,
    "cancelled_count": 0,
}
flight_lock = threading.Lock()

state = {
    "live_updates":   [],     # new articles parsed from RSS
    "last_refresh":   None,
    "next_refresh":   None,
    "feed_status":    {},
    "article_hashes": set(),  # dedup
}
state_lock = threading.Lock()


BROWSER_HEADERS = {
    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/121.0.0.0 Safari/537.36',
    'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
    'Accept-Language': 'en-US,en;q=0.5',
}

def fetch_url(url, timeout=10, use_browser_headers=False):
    try:
        hdrs = BROWSER_HEADERS if use_browser_headers else {'User-Agent': 'Mozilla/5.0 (NewsMap/1.0)'}
        req = Request(url, headers=hdrs)
        with urlopen(req, timeout=timeout, context=SSL_CTX) as resp:
            return resp.read()
    except Exception as e:
        return None


def parse_rss(xml_bytes):
    """Parse RSS/Atom feed, return list of (title, link, pub_date, summary)."""
    items = []
    try:
        root = ET.fromstring(xml_bytes)
        ns = {'atom': 'http://www.w3.org/2005/Atom'}

        # RSS 2.0
        for item in root.iter('item'):
            title   = item.findtext('title', '').strip()
            link    = item.findtext('link', '').strip()
            pubdate = item.findtext('pubDate', '').strip()
            summary = item.findtext('description', '').strip()
            items.append((title, link, pubdate, summary))

        # Atom
        if not items:
            for entry in root.findall('.//atom:entry', ns) or root.findall('.//{http://www.w3.org/2005/Atom}entry'):
                title   = entry.findtext('{http://www.w3.org/2005/Atom}title', '').strip()
                link_el = entry.find('{http://www.w3.org/2005/Atom}link')
                link    = link_el.get('href', '') if link_el is not None else ''
                pubdate = entry.findtext('{http://www.w3.org/2005/Atom}published', '').strip()
                summary = entry.findtext('{http://www.w3.org/2005/Atom}summary', '').strip()
                items.append((title, link, pubdate, summary))
    except Exception:
        pass
    return items


def is_relevant(title, summary):
    text = (title + ' ' + summary).lower()
    has_conflict = any(k in text for k in ISRAEL_KEYWORDS) and any(k in text for k in IRAN_KEYWORDS)
    has_action   = any(k in text for k in STRIKE_KEYWORDS)
    return has_conflict and has_action


def extract_location(text):
    text_lower = text.lower()
    for loc in sorted(LOCATION_COORDS.keys(), key=len, reverse=True):
        if loc in text_lower:
            return loc
    return None


def extract_number(text, patterns):
    for pat in patterns:
        m = re.search(pat, text, re.IGNORECASE)
        if m:
            try:
                return int(m.group(1).replace(',', ''))
            except Exception:
                pass
    return 0


def guess_actor(title, summary):
    text = (title + ' ' + summary).lower()
    israel_score = sum(1 for k in ISRAEL_KEYWORDS if k in text)
    iran_score   = sum(1 for k in IRAN_KEYWORDS   if k in text)
    # If Iran location targeted → Israel is actor; if Israel location → Iran is actor
    loc = extract_location(text)
    if loc:
        country = COUNTRY_MAP.get(loc, '')
        if country == 'Iran':
            return 'Israel'
        if country in ('Israel', 'UAE', 'Qatar', 'Bahrain', 'Kuwait', 'Jordan', 'Saudi Arabia'):
            return 'Iran'
    return 'Israel' if israel_score >= iran_score else 'Iran'


VEHICLE_PATTERNS = [
    (r'b-?2\b|b2 spirit|stealth bomber', 'B-2 Spirit stealth bomber'),
    (r'b-?1\b|b-?1b\b|lancer bomber', 'B-1B Lancer bomber'),
    (r'f-?35\b', 'F-35 Lightning II'),
    (r'f-?22\b|raptor', 'F-22 Raptor'),
    (r'f-?15\b', 'F-15 Strike Eagle'),
    (r'f-?16\b', 'F-16 Fighting Falcon'),
    (r'f-?18\b|hornet\b', 'F/A-18 Hornet'),
    (r'mq-?9\b|reaper drone', 'MQ-9 Reaper drone'),
    (r'tomahawk', 'Tomahawk cruise missile'),
    (r'lucas drone|one-?way.attack drone', 'LUCAS one-way attack drone'),
    (r'shahed-?136|shahed drone', 'Shahed-136 suicide drone'),
    (r'shahed-?238', 'Shahed-238 jet drone'),
    (r'fattah-?2?|hypersonic', 'Fattah hypersonic missile'),
    (r'qiam|emad|ghadr|sajjil', 'Iranian ballistic missile'),
    (r'ballistic missile', 'Ballistic missile'),
    (r'cruise missile', 'Cruise missile'),
    (r'drone\b|uav\b', 'Drone / UAV'),
    (r'airstrike|air strike|fighter jet|warplane', 'Fighter jet airstrike'),
    (r'gbu-?57|mop\b|bunker.buster', 'GBU-57 MOP bunker buster'),
    (r'jdam|gbu-?31|precision.bomb', 'JDAM precision-guided bomb'),
]

def extract_vehicle(text):
    import re as _re
    text_lower = text.lower()
    found = []
    for pattern, label in VEHICLE_PATTERNS:
        if _re.search(pattern, text_lower):
            if label not in found:
                found.append(label)
    return ' · '.join(found) if found else None


def article_to_event(title, link, pubdate, summary, feed_url):
    text = title + ' ' + summary
    killed  = extract_number(text, [r'(\d+)\s*(?:people\s*)?(?:were\s*)?killed',
                                     r'(\d+)\s*dead', r'death toll.*?(\d+)',
                                     r'(\d+)\s*(?:civilians?|soldiers?|people)\s*killed'])
    wounded = extract_number(text, [r'(\d+)\s*(?:people\s*)?(?:were\s*)?(?:wounded|injured)',
                                     r'(\d+)\s*injur'])
    loc     = extract_location(text)
    if not loc:
        loc = 'Unknown / Regional'
        lat, lng = 32.0, 47.0
    else:
        lat, lng = LOCATION_COORDS[loc]

    country = COUNTRY_MAP.get(loc, 'Unknown')
    actor   = guess_actor(title, summary)

    # Clean summary
    clean_summary = re.sub(r'<[^>]+>', '', summary)[:280]

    vehicle = extract_vehicle(text)

    return {
        "id":          hashlib.md5((title + link).encode()).hexdigest()[:10],
        "date":        datetime.now(timezone.utc).strftime('%Y-%m-%d'),
        "time":        datetime.now(timezone.utc).strftime('%H:%M'),
        "displayDate": datetime.now(timezone.utc).strftime('%d %b %Y, %H:%M UTC'),
        "actor":       actor,
        "location":    loc.title() if loc != 'Unknown / Regional' else 'Regional',
        "country":     country,
        "lat":         lat,
        "lng":         lng,
        "type":        "Live Update",
        "vehicle":     vehicle,
        "killed":      killed,
        "wounded":     wounded,
        "note":        clean_summary,
        "source":      link,
        "headline":    title,
        "isLive":      True,
    }


def refresh_feeds():
    print(f"[{datetime.now().strftime('%H:%M:%S')}] Refreshing feeds...")
    new_events = []
    feed_status = {}

    for feed_url in RSS_FEEDS:
        domain = urlparse(feed_url).netloc
        xml_bytes = fetch_url(feed_url)
        if not xml_bytes:
            feed_status[domain] = "error"
            continue

        items = parse_rss(xml_bytes)
        feed_status[domain] = f"ok ({len(items)} items)"
        matched = 0

        for title, link, pubdate, summary in items:
            h = hashlib.md5((title + link).encode()).hexdigest()
            with state_lock:
                if h in state["article_hashes"]:
                    continue
                state["article_hashes"].add(h)

            if not is_relevant(title, summary):
                continue

            event = article_to_event(title, link, pubdate, summary, feed_url)
            new_events.append(event)
            matched += 1
            print(f"  + [{domain}] {title[:80]}")

        if matched:
            feed_status[domain] += f" → {matched} relevant"

    now = datetime.now(timezone.utc)
    with state_lock:
        state["live_updates"]  = new_events + state["live_updates"]
        state["live_updates"]  = state["live_updates"][:200]  # cap
        state["last_refresh"]  = now.strftime('%d %b %Y %H:%M UTC')
        state["next_refresh"]  = f"in {UPDATE_INTERVAL//60} min"
        state["feed_status"]   = feed_status

    print(f"[{datetime.now().strftime('%H:%M:%S')}] Done. {len(new_events)} new events. Next in {UPDATE_INTERVAL//60}m.")


def feed_loop():
    while True:
        try:
            refresh_feeds()
        except Exception as e:
            print(f"Feed loop error: {e}")
        time.sleep(UPDATE_INTERVAL)


# ── HTTP Handler ───────────────────────────────────────────────────────────
class Handler(BaseHTTPRequestHandler):
    def log_message(self, fmt, *args):
        # Only log non-API requests
        if '/api/' not in args[0] if args else True:
            print(f"  {self.address_string()} {fmt % args}")

    def send_json(self, data, status=200):
        body = json.dumps(data, ensure_ascii=False).encode()
        self.send_response(status)
        self.send_header('Content-Type', 'application/json')
        self.send_header('Access-Control-Allow-Origin', '*')
        self.send_header('Content-Length', len(body))
        self.end_headers()
        self.wfile.write(body)

    def serve_file(self, path, content_type):
        try:
            with open(path, 'rb') as f:
                body = f.read()
            self.send_response(200)
            self.send_header('Content-Type', content_type)
            self.send_header('Content-Length', len(body))
            self.end_headers()
            self.wfile.write(body)
        except FileNotFoundError:
            self.send_response(404)
            self.end_headers()

    def do_GET(self):
        path = self.path.split('?')[0]

        if path == '/' or path == '/index.html':
            self.serve_file(os.path.join(BASE_DIR, 'israel-iran-crisis-map.html'), 'text/html; charset=utf-8')

        elif path == '/israel-iran-crisis-map.html':
            self.serve_file(os.path.join(BASE_DIR, 'israel-iran-crisis-map.html'), 'text/html; charset=utf-8')

        elif path == '/api/flights':
            with flight_lock:
                payload = {
                    "historical":      HISTORICAL_DXB,
                    "live_flights":    flight_state['live_flights'],
                    "last_refresh":    flight_state['last_refresh'],
                    "dep_count":       flight_state['dep_count'],
                    "arr_count":       flight_state['arr_count'],
                    "cancelled_count": flight_state['cancelled_count'],
                    "server_time":     datetime.now(timezone.utc).strftime('%d %b %Y %H:%M UTC'),
                }
            self.send_json(payload)

        elif path == '/api/updates':
            with state_lock:
                payload = {
                    "live_updates":  state["live_updates"],
                    "last_refresh":  state["last_refresh"],
                    "next_refresh":  state["next_refresh"],
                    "feed_status":   state["feed_status"],
                    "update_count":  len(state["live_updates"]),
                    "server_time":   datetime.now(timezone.utc).strftime('%d %b %Y %H:%M:%S UTC'),
                }
            self.send_json(payload)

        elif path == '/api/status':
            with state_lock:
                self.send_json({
                    "last_refresh": state["last_refresh"],
                    "next_refresh": state["next_refresh"],
                    "feeds":        state["feed_status"],
                    "update_count": len(state["live_updates"]),
                })
        else:
            self.send_response(404)
            self.end_headers()


# ── Main ───────────────────────────────────────────────────────────────────
if __name__ == '__main__':
    print(f"Starting Israel–Iran Crisis Map server on port {PORT}...")
    print(f"http://127.0.0.1:{PORT}/israel-iran-crisis-map.html")
    print(f"Feeds refresh every {UPDATE_INTERVAL//60} minutes.")

    # Start background threads
    t = threading.Thread(target=feed_loop, daemon=True)
    t.start()
    tf = threading.Thread(target=flight_loop, daemon=True)
    tf.start()

    server = HTTPServer(('0.0.0.0', PORT), Handler)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nShutting down.")
        server.shutdown()
