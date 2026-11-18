# -*- coding: utf-8 -*-

"""
Czech News Tracker
==================

Collector + Translator + Topic Classifier

Features:
- Collect Czech-language news from multiple RSS feeds
- Focus on Czech politics, security, defense, and foreign affairs
- Translate Czech headlines and summaries into English
- DeepL primary translation with Google Translate fallback
- Deduplicate articles across feeds and previous runs
- Maintain rolling 48-hour news feed
- Maintain permanent historical archive
- Generate topic-specific JSON files
- Retry failed translations
- Preserve compatibility with Russian Media Tracker JSON structure

Output:
    data/articles_latest.json
    data/articles_archive.json
    data/articles_politics.json
    data/articles_security.json
    data/articles_foreign_affairs.json
"""

from __future__ import annotations

import os
import re
import json
import time
import hashlib
import logging
import unicodedata
import calendar

from pathlib import Path
from datetime import datetime, timedelta, timezone
from typing import Dict, List, Optional
from urllib.parse import urlsplit, urlunsplit, parse_qsl, urlencode

import requests
import feedparser

from bs4 import BeautifulSoup
from deep_translator import GoogleTranslator


# ============================================================
# CONFIGURATION
# ============================================================

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s"
)

LOG = logging.getLogger("czech-news")


HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/122.0.0.0 Safari/537.36"
    ),
    "Accept": "application/rss+xml, application/xml, text/xml, */*",
    "Accept-Language": "cs-CZ,cs;q=0.9,en;q=0.7",
}


TIMEOUT = 20
MAX_RETRIES = 3
RETRY_SLEEP = 2

KEEP_HOURS = int(os.getenv("KEEP_HOURS", "48"))

TRANSLATE_LIMIT = int(os.getenv("TRANSLATE_LIMIT", "40"))

DEEPL_API_KEY = os.getenv("DEEPL_API_KEY", "")

DEEPL_API_URL = os.getenv(
    "DEEPL_API_URL",
    "https://api-free.deepl.com/v2/translate"
)

TRANSLATION_PROVIDER = os.getenv(
    "TRANSLATION_PROVIDER",
    "auto"
).lower()

OUT_JSON = Path(
    os.getenv(
        "OUT_JSON",
        "data/articles_latest.json"
    )
)

ARCHIVE_JSON = Path(
    os.getenv(
        "ARCHIVE_JSON",
        "data/articles_archive.json"
    )
)


# ============================================================
# NEWS SOURCES
# ============================================================

SOURCES: Dict[str, Dict] = {

    "iROZHLAS (Domestic)": {
        "feeds": [
            "https://www.irozhlas.cz/rss/irozhlas/section/zpravy-domov",
        ],
    },

    "iROZHLAS (World)": {
        "feeds": [
            "https://www.irozhlas.cz/rss/irozhlas/section/zpravy-svet",
        ],
    },

    "CT24": {
        "feeds": [
            "https://ct24.ceskatelevize.cz/rss/hlavni-zpravy",
        ],
    },

    "Seznam Zpravy": {
        "feeds": [
            "https://www.seznamzpravy.cz/rss",
        ],
    },

    "Aktualne.cz": {
        "feeds": [
            "https://zpravy.aktualne.cz/rss/",
        ],
    },

}


# ============================================================
# TOPIC CLASSIFICATION
# ============================================================

TOPIC_KEYWORDS = {

    "politics": [

        # Government
        "vlada",
        "vladni",
        "premier",
        "predseda vlady",
        "ministr",
        "ministerstvo",
        "kabinet",

        # Parliament
        "parlament",
        "poslanecka snemovna",
        "snemovna",
        "poslanec",
        "poslanci",
        "senat",
        "senator",

        # Political processes
        "volby",
        "volebni",
        "koalice",
        "opozice",
        "politika",
        "politicky",
        "politicka",
        "zakon",
        "legislativa",
        "ustavni",
        "referendum",

        # Czech political parties
        "ano 2011",
        "hnuti ano",
        "ods",
        "stan",
        "spolu",
        "pirati",
        "spd",
        "motoriste",
        "top 09",
        "kdu-csl",

        # Institutions
        "prezident",
        "prazsky hrad",
        "ustavni soud",
        "snemovni",

    ],


    "security": [

        # Defense
        "obrana",
        "obranny",
        "ministerstvo obrany",
        "armada",
        "vojaci",
        "vojensky",
        "vojsko",
        "ozbrojene sily",

        # NATO
        "nato",
        "aliance",
        "severoatlanticka",

        # Defense technology
        "zbrane",
        "zbrojni",
        "munice",
        "raketa",
        "rakety",
        "protivzdusna",
        "dron",
        "bezpilotni",
        "stihacka",
        "letoun",
        "f-35",
        "tank",
        "delostrelectvo",

        # Security
        "bezpecnost",
        "narodni bezpecnost",
        "kyberneticka",
        "kyberneticky",
        "kyberutok",
        "hybridni hrozby",
        "hybridni valka",
        "terorismus",
        "teroristicky",
        "sabotaz",
        "spionaz",
        "rozvedka",
        "kontrarozvedka",
        "tajne sluzby",

        # Czech security institutions
        "bis",
        "vzis",
        "nukib",
        "generalni stab",

        # Military conflict
        "valka",
        "invaze",
        "vojenska operace",
        "utok",
        "fronta",
        "mobilizace",

    ],


    "foreign_affairs": [

        # Diplomacy
        "diplomacie",
        "diplomaticky",
        "zahranicni politika",
        "ministerstvo zahranici",
        "mezinarodni vztahy",
        "velvyslanec",
        "velvyslanectvi",
        "ambasada",
        "jednani",
        "summit",
        "bilateralni",
        "mezinarodni",

        # European Union
        "evropska unie",
        "evropske unie",
        "evropska komise",
        "evropsky parlament",
        "evropska rada",
        "brusel",
        "eu",
        "unijni",

        # International organizations
        "nato",
        "osn",
        "organizace spojenych narodu",
        "visegradska",
        "v4",

        # Countries and regions
        "ukrajina",
        "ukrajinsky",
        "rusko",
        "rusky",
        "slovensko",
        "slovensky",
        "polsko",
        "polsky",
        "nemecko",
        "nemecky",
        "cina",
        "cinsky",
        "spojene staty",
        "usa",
        "washington",
        "izrael",
        "iran",

        # International policy
        "sankce",
        "zahranicni pomoc",
        "vojenska pomoc",
        "mezinarodni obchod",
        "strategicke partnerstvi",

    ],

}


# ============================================================
# CZECH RELEVANCE FILTER
# ============================================================

"""
We want articles about Czechia, not every international
story published by a Czech newspaper.

Stories about Czech domestic politics qualify.

International stories should have a meaningful Czech
connection or concern Czech security and foreign policy.

The filter uses Czech-language keywords and is deliberately
more selective than simply accepting every article.
"""

CZECH_KEYWORDS = [

    # Country
    "cesko",
    "ceska republika",
    "ceske republiky",
    "cesky",
    "ceska",
    "ceske",
    "ceskem",

    # Cities
    "praha",
    "praze",
    "prazsky",

    # Government and politics
    "ceska vlada",
    "vlada",
    "premier",
    "snemovna",
    "poslanci",
    "senat",
    "prezident",
    "ministerstvo",
    "ministr",
    "parlament",

    # Czech institutions
    "prazsky hrad",
    "bis",
    "nukib",
    "armada cr",

    # Czech political organizations
    "ods",
    "stan",
    "hnuti ano",
    "pirati",
    "spd",
    "motoriste",

]


TOPICS = [
    "politics",
    "security",
    "foreign_affairs",
]


# ============================================================
# UTILITIES
# ============================================================

def utcnow():

    return datetime.now(timezone.utc)


def normalize_space(text):

    return " ".join(
        (text or "").split()
    ).strip()


def normalize_text(text):

    text = unicodedata.normalize(
        "NFKD",
        (text or "").lower()
    )

    return "".join(
        character
        for character in text
        if not unicodedata.combining(character)
    )


def keyword_match(text, keyword):

    """
    Match a Czech keyword or stem.

    Word boundaries are enforced at the beginning.
    The end remains open to match Czech inflections.

    Example:
        "ministr" matches "ministra" and "ministrem".
    """

    pattern = r"(?<!\w)" + re.escape(keyword)

    return bool(
        re.search(pattern, text)
    )


def normalize_url(url):

    url = normalize_space(url)

    if not url:
        return ""

    parts = urlsplit(url)

    # Remove common tracking parameters while preserving
    # other query parameters that may identify an article.
    filtered_query = [
        (key, value)
        for key, value in parse_qsl(parts.query)
        if not (
            key.lower().startswith("utm_")
            or key.lower() in (
                "fbclid",
                "gclid",
                "mc_cid",
                "mc_eid",
            )
        )
    ]

    return urlunsplit((
        parts.scheme.lower(),
        parts.netloc.lower(),
        parts.path.rstrip("/") or "/",
        urlencode(filtered_query),
        "",
    ))


def normalize_title(text):

    text = normalize_text(text)

    text = re.sub(
        r"[^\w\s]",
        "",
        text
    )

    return normalize_space(text)


def hash_key(*parts):

    h = hashlib.sha256()

    for part in parts:

        h.update(
            str(part or "").encode(
                "utf-8",
                errors="ignore"
            )
        )

        h.update(b"|")

    return h.hexdigest()


def clean_html(html):

    soup = BeautifulSoup(
        html or "",
        "html.parser"
    )

    return normalize_space(
        soup.get_text(" ", strip=True)
    )


def two_sentence_lead(text):

    text = clean_html(text)

    if not text:
        return ""

    sentences = re.split(
        r"(?<=[.!?])\s+",
        text
    )

    sentences = [
        sentence.strip()
        for sentence in sentences
        if sentence.strip()
    ]

    if len(sentences) >= 2:

        return (
            sentences[0]
            + " "
            + sentences[1]
        )

    return text[:400].rstrip()


# ============================================================
# RSS FETCHING
# ============================================================

def fetch_text(url):

    session = requests.Session()

    session.headers.update(HEADERS)

    for attempt in range(
        1,
        MAX_RETRIES + 1
    ):

        try:

            response = session.get(
                url,
                timeout=TIMEOUT,
                allow_redirects=True
            )

            response.raise_for_status()

            if response.content:

                return response.content

        except requests.RequestException as exc:

            LOG.warning(
                "Fetch failed %s (%s/%s): %s",
                url,
                attempt,
                MAX_RETRIES,
                exc
            )

        if attempt < MAX_RETRIES:
            time.sleep(
                RETRY_SLEEP * attempt
            )

    return None


def parse_date(entry):

    for key in (
        "published_parsed",
        "updated_parsed",
        "created_parsed",
    ):

        value = entry.get(key)

        if value:

            try:

                timestamp = calendar.timegm(
                    value
                )

                return datetime.fromtimestamp(
                    timestamp,
                    timezone.utc
                )

            except (
                ValueError,
                TypeError,
                OverflowError
            ):

                pass

    # Entries without a publication date are skipped.
    # Assigning the current time would incorrectly treat
    # older stories as new articles.

    return None


def collect_from_rss(source_name, feeds):

    rows = []

    for feed_url in feeds:

        content = fetch_text(feed_url)

        if not content:
            continue

        parsed = feedparser.parse(
            content
        )

        if parsed.bozo and not parsed.entries:

            LOG.warning(
                "Invalid RSS feed: %s",
                feed_url
            )

            continue

        feed_rows = []

        for entry in parsed.entries:

            title = clean_html(
                entry.get("title", "")
            )

            url = normalize_url(
                entry.get("link", "")
            )

            summary = (
                entry.get("summary")
                or entry.get("description")
                or ""
            )

            publication_date = parse_date(
                entry
            )

            if not title or not url:
                continue

            if not publication_date:
                continue

            feed_rows.append({

                "source": source_name,

                "url": url,

                "published_utc": (
                    publication_date
                    .astimezone(timezone.utc)
                    .strftime("%Y-%m-%dT%H:%M:%SZ")
                ),

                "title_raw": title,

                "lead_raw": two_sentence_lead(
                    summary
                ),

            })

        if feed_rows:

            rows.extend(feed_rows)

            # As in the Russian collector, additional feeds
            # are fallbacks for the same source.
            break

    return rows


# ============================================================
# TOPIC CLASSIFICATION
# ============================================================

def classify_topics(article):

    title = normalize_text(
        article.get("title_raw", "")
    )

    lead = normalize_text(
        article.get("lead_raw", "")
    )

    scores = {}

    for topic, keywords in TOPIC_KEYWORDS.items():

        title_score = sum(
            3
            for keyword in keywords
            if keyword_match(title, keyword)
        )

        lead_score = sum(
            1
            for keyword in keywords
            if keyword_match(lead, keyword)
        )

        scores[topic] = (
            title_score + lead_score
        )

    labels = [
        topic
        for topic, score in scores.items()
        if score > 0
    ]

    labels.sort(
        key=lambda topic: (
            -scores[topic],
            topic
        )
    )

    primary = (
        labels[0]
        if labels
        else None
    )

    article["topic_scores"] = scores

    article["topics"] = labels

    article["primary_topic"] = primary

    return article


def article_is_czech_related(article):

    title = normalize_text(
        article.get("title_raw", "")
    )

    lead = normalize_text(
        article.get("lead_raw", "")
    )

    text = title + " " + lead

    # Direct Czech relevance
    direct_match = any(
        keyword_match(text, keyword)
        for keyword in CZECH_KEYWORDS
    )

    if direct_match:
        return True

    # Also accept articles from domestic feeds involving
    # Czech political or security institutions.

    source = article.get(
        "source",
        ""
    ).lower()

    if "domestic" in source:

        institutional_terms = [
            "vlada",
            "ministr",
            "poslan",
            "snemovn",
            "senat",
            "prezident",
            "volby",
            "koalic",
            "opozic",
            "armada",
            "bezpecnost",
            "parlament",
        ]

        return any(
            keyword_match(text, term)
            for term in institutional_terms
        )

    return False


def article_is_relevant(article):

    """
    Keep articles that:
    1. Concern Czechia or Czech institutions.
    2. Match at least one desired topic.
    """

    if not article.get("topics"):
        return False

    return article_is_czech_related(
        article
    )


# ============================================================
# TRANSLATION
# ============================================================

TRANSLATION_CACHE = {}


def translate_deepl(text):

    if not DEEPL_API_KEY:

        raise RuntimeError(
            "DeepL API key unavailable"
        )

    response = requests.post(

        DEEPL_API_URL,

        headers={
            "Authorization": (
                f"DeepL-Auth-Key {DEEPL_API_KEY}"
            )
        },

        json={
            "text": [text],
            "source_lang": "CS",
            "target_lang": "EN",
        },

        timeout=30

    )

    response.raise_for_status()

    return response.json()[
        "translations"
    ][0]["text"]


def translate_google(text):

    translator = GoogleTranslator(
        source="cs",
        target="en"
    )

    return translator.translate(
        text
    )


def translate_text(text):

    """
    Returns:
        (translation, provider)

    If translation fails:
        (None, "failed")

    This prevents the original Czech text from being
    mistakenly stored as an English translation.
    """

    text = normalize_space(text)

    if not text:
        return "", "empty"

    if text in TRANSLATION_CACHE:

        return TRANSLATION_CACHE[text]

    if TRANSLATION_PROVIDER == "none":

        return None, "disabled"

    # DeepL first

    if (
        TRANSLATION_PROVIDER in ("auto", "deepl")
        and DEEPL_API_KEY
    ):

        try:

            translated = translate_deepl(
                text
            )

            if translated and translated.strip():

                result = (
                    translated,
                    "deepl"
                )

                TRANSLATION_CACHE[text] = result

                return result

        except Exception as exc:

            LOG.warning(
                "DeepL failed: %s",
                exc
            )

    # Google Translate fallback

    if TRANSLATION_PROVIDER in (
        "auto",
        "google"
    ):

        for attempt in range(2):

            try:

                translated = translate_google(
                    text
                )

                if translated and translated.strip():

                    result = (
                        translated,
                        "google"
                    )

                    TRANSLATION_CACHE[text] = result

                    return result

            except Exception as exc:

                LOG.warning(
                    "Google Translate failed: %s",
                    exc
                )

                if attempt == 0:
                    time.sleep(2)

    return None, "failed"


def enrich_translate(article):

    """
    Translate only missing English fields.
    Preserve successful translations from previous runs.
    """

    title_raw = article.get(
        "title_raw",
        ""
    )

    lead_raw = article.get(
        "lead_raw",
        ""
    )

    title_en = article.get(
        "title_en"
    )

    lead_en = article.get(
        "lead_en"
    )

    providers = []

    if not title_en:

        translated, provider = translate_text(
            title_raw
        )

        if translated:
            title_en = translated

        providers.append(provider)

    if lead_raw and not lead_en:

        translated, provider = translate_text(
            lead_raw
        )

        if translated:
            lead_en = translated

        providers.append(provider)

    article["title_en"] = title_en

    article["lead_en"] = lead_en

    if title_en and (
        lead_en or not lead_raw
    ):

        article["translation_status"] = (
            "translated"
        )

    elif title_en or lead_en:

        article["translation_status"] = (
            "partial"
        )

    else:

        article["translation_status"] = (
            "pending"
        )

    if providers:

        successful = [
            provider
            for provider in providers
            if provider in ("deepl", "google")
        ]

        if successful:

            article["translation_provider"] = (
                successful[-1]
            )

    return article


def needs_translation(article):

    return (
        not article.get("title_en")
        or (
            article.get("lead_raw")
            and not article.get("lead_en")
        )
    )


# ============================================================
# DEDUPLICATION
# ============================================================

def article_fingerprint(article):

    url = normalize_url(
        article.get("url", "")
    )

    if url:

        return hash_key(
            url
        )

    return hash_key(

        normalize_title(
            article.get("title_raw", "")
        ),

        article.get(
            "published_utc",
            ""
        )[:10],

        article.get(
            "source",
            ""
        ),

    )


def choose_better_article(a, b):

    """
    Merge duplicate records without losing
    previously completed translations.
    """

    fields = [
        "title_raw",
        "lead_raw",
        "url",
    ]

    score_a = sum(
        len(a.get(field) or "")
        for field in fields
    )

    score_b = sum(
        len(b.get(field) or "")
        for field in fields
    )

    if score_b > score_a:

        preferred = dict(b)
        other = a

    else:

        preferred = dict(a)
        other = b

    # Preserve successful translations.

    for field in (
        "title_en",
        "lead_en",
        "translation_provider",
    ):

        if not preferred.get(field):

            preferred[field] = other.get(
                field
            )

    if (
        preferred.get("title_en")
        and (
            preferred.get("lead_en")
            or not preferred.get("lead_raw")
        )
    ):

        preferred["translation_status"] = (
            "translated"
        )

    return preferred


def dedupe_articles(rows):

    best = {}

    for article in rows:

        fingerprint = article_fingerprint(
            article
        )

        previous = best.get(
            fingerprint
        )

        if previous is None:

            best[fingerprint] = article

        else:

            best[fingerprint] = (
                choose_better_article(
                    previous,
                    article
                )
            )

    result = list(
        best.values()
    )

    result.sort(
        key=lambda article: article.get(
            "published_utc",
            ""
        ),
        reverse=True
    )

    return result


# ============================================================
# STORAGE
# ============================================================

def load_existing_json(path):

    if not path.exists():
        return []

    try:

        data = json.loads(
            path.read_text(
                encoding="utf-8"
            )
        )

        if isinstance(data, dict):

            return data.get(
                "articles",
                []
            )

        if isinstance(data, list):

            return data

    except Exception as exc:

        LOG.warning(
            "Unable to load %s: %s",
            path,
            exc
        )

    return []


def atomic_write_json(path, payload):

    path.parent.mkdir(
        parents=True,
        exist_ok=True
    )

    temporary = path.with_suffix(
        ".tmp"
    )

    temporary.write_text(

        json.dumps(
            payload,
            ensure_ascii=False,
            indent=2
        ),

        encoding="utf-8"

    )

    temporary.replace(
        path
    )


def prune_latest_window(rows):

    cutoff = utcnow() - timedelta(
        hours=KEEP_HOURS
    )

    kept = []

    for article in rows:

        try:

            published = datetime.strptime(

                article["published_utc"],

                "%Y-%m-%dT%H:%M:%SZ"

            ).replace(
                tzinfo=timezone.utc
            )

            if published >= cutoff:

                kept.append(
                    article
                )

        except (
            ValueError,
            KeyError,
            TypeError
        ):

            continue

    return dedupe_articles(
        kept
    )


def prepare_article(article):

    """
    Normalize article metadata and classify.
    """

    article = dict(article)

    article["fingerprint"] = (
        article_fingerprint(
            article
        )
    )

    if not article.get("id"):

        article["id"] = hash_key(

            article.get(
                "source",
                ""
            ),

            article.get(
                "url",
                ""
            ),

            article.get(
                "published_utc",
                ""
            ),

        )

    article.setdefault(
        "title_en",
        None
    )

    article.setdefault(
        "lead_en",
        None
    )

    article.setdefault(
        "translation_status",
        "pending"
    )

    return classify_topics(
        article
    )


# ============================================================
# MAIN COLLECTOR
# ============================================================

def main():

    now = utcnow()

    timestamp = now.strftime(
        "%Y-%m-%dT%H:%M:%SZ"
    )

    LOG.info(
        "Czech News Tracker starting: %s",
        timestamp
    )

    collected = []

    successful_sources = 0

    # --------------------------------------------------------
    # 1. COLLECT RSS FEEDS
    # --------------------------------------------------------

    for source, config in SOURCES.items():

        LOG.info(
            "Collecting: %s",
            source
        )

        rows = collect_from_rss(
            source,
            config["feeds"]
        )

        LOG.info(
            "%s: %s articles",
            source,
            len(rows)
        )

        if rows:

            successful_sources += 1

        collected.extend(
            rows
        )

    LOG.info(
        "Total collected: %s",
        len(collected)
    )

    # Avoid an empty successful run that could mask
    # the failure of every RSS source.

    if successful_sources == 0:

        LOG.error(
            "All RSS sources failed."
        )

        return 1

    # --------------------------------------------------------
    # 2. LOAD EXISTING DATA
    # --------------------------------------------------------

    existing_latest = load_existing_json(
        OUT_JSON
    )

    existing_archive = load_existing_json(
        ARCHIVE_JSON
    )

    LOG.info(
        "Existing archive: %s articles",
        len(existing_archive)
    )

    # --------------------------------------------------------
    # 3. MERGE AND DEDUPLICATE
    # --------------------------------------------------------

    merged = dedupe_articles(

        existing_archive
        + existing_latest
        + collected

    )

    LOG.info(
        "After deduplication: %s",
        len(merged)
    )

    # --------------------------------------------------------
    # 4. CLASSIFY AND FILTER
    # --------------------------------------------------------

    relevant = []

    for article in merged:

        article = prepare_article(
            article
        )

        if article_is_relevant(
            article
        ):

            relevant.append(
                article
            )

    LOG.info(
        "Relevant Czech articles: %s",
        len(relevant)
    )

    # --------------------------------------------------------
    # 5. TRANSLATE
    # --------------------------------------------------------

    translated_count = 0

    # Prioritize recent articles.

    relevant.sort(

        key=lambda article: article.get(
            "published_utc",
            ""
        ),

        reverse=True

    )

    for article in relevant:

        if translated_count >= TRANSLATE_LIMIT:
            break

        if not needs_translation(
            article
        ):
            continue

        enrich_translate(
            article
        )

        translated_count += 1

    LOG.info(
        "Translation attempts: %s",
        translated_count
    )

    # --------------------------------------------------------
    # 6. BUILD PERMANENT ARCHIVE
    # --------------------------------------------------------

    archive = dedupe_articles(
        relevant
    )

    archive_payload = {

        "updated_at_utc": timestamp,

        "count": len(archive),

        "articles": archive,

    }

    atomic_write_json(
        ARCHIVE_JSON,
        archive_payload
    )

    # --------------------------------------------------------
    # 7. BUILD ROLLING 48-HOUR FEED
    # --------------------------------------------------------

    latest = prune_latest_window(
        archive
    )

    latest_payload = {

        "updated_at_utc": timestamp,

        "keep_hours": KEEP_HOURS,

        "count": len(latest),

        "articles": latest,

    }

    atomic_write_json(
        OUT_JSON,
        latest_payload
    )

    # --------------------------------------------------------
    # 8. GENERATE TOPIC FEEDS
    # --------------------------------------------------------

    for topic in TOPICS:

        subset = [

            article

            for article in latest

            if topic in article.get(
                "topics",
                []
            )

        ]

        topic_payload = {

            "updated_at_utc": timestamp,

            "topic": topic,

            "count": len(subset),

            "articles": subset,

        }

        output_path = Path(
            f"data/articles_{topic}.json"
        )

        atomic_write_json(
            output_path,
            topic_payload
        )

        LOG.info(
            "%s: %s articles",
            topic,
            len(subset)
        )

    # --------------------------------------------------------
    # 9. SUMMARY
    # --------------------------------------------------------

    LOG.info(
        "Collection completed successfully."
    )

    LOG.info(
        "Latest articles: %s",
        len(latest)
    )

    LOG.info(
        "Archived articles: %s",
        len(archive)
    )

    LOG.info(
        "Output: %s",
        OUT_JSON
    )

    LOG.info(
        "Archive: %s",
        ARCHIVE_JSON
    )

    return 0


if __name__ == "__main__":

    raise SystemExit(
        main()
    )
