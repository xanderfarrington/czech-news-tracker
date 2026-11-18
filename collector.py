# -*- coding: utf-8 -*-

"""
Czech News Tracker
==================

Collects, classifies, translates, and archives Czech news.

Sources:
    iROZHLAS Domestic
    iROZHLAS World
    CT24
    Seznam Zpravy
    Aktualne.cz

Topics:
    politics
    security
    foreign_affairs

Translation:
    Argos Translate (Czech -> English)
    Local inference; no external translation API.

Outputs:
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
import calendar
import unicodedata

from pathlib import Path
from datetime import datetime, timedelta, timezone
from urllib.parse import urlsplit, urlunsplit, parse_qsl, urlencode

import requests
import feedparser

from bs4 import BeautifulSoup

import argostranslate.package
import argostranslate.translate


# ============================================================
# CONFIGURATION
# ============================================================

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s"
)

LOG = logging.getLogger("czech-news")

DATA_DIR = Path("data")

KEEP_HOURS = int(os.getenv("KEEP_HOURS", "48"))

# Set to 0 for unlimited translation.
TRANSLATE_LIMIT = int(os.getenv("TRANSLATE_LIMIT", "60"))

TIMEOUT = 20

HEADERS = {
    "User-Agent": "CzechNewsTracker/2.0 (research news monitor)",
    "Accept": "application/rss+xml, application/xml, text/xml, */*",
    "Accept-Language": "cs-CZ,cs;q=0.9,en;q=0.7",
}

TOPICS = (
    "politics",
    "security",
    "foreign_affairs",
)


# ============================================================
# SOURCES
# ============================================================

SOURCES = {

    "iROZHLAS (Domestic)": [
        "https://www.irozhlas.cz/rss/irozhlas/section/zpravy-domov",
    ],

    "iROZHLAS (World)": [
        "https://www.irozhlas.cz/rss/irozhlas/section/zpravy-svet",
    ],

    "CT24": [
        "https://ct24.ceskatelevize.cz/rss/hlavni-zpravy",
    ],

    "Seznam Zpravy": [
        "https://www.seznamzpravy.cz/rss",
    ],

    "Aktualne.cz": [
        "https://zpravy.aktualne.cz/rss/",
    ],

}


# ============================================================
# CLASSIFICATION KEYWORDS
# ============================================================

# Keywords are stored without Czech diacritics.
# Text is normalized before classification.
#
# Prefix matching accommodates Czech grammatical inflections.

TOPIC_KEYWORDS = {

    "politics": [

        # Government
        "vlad",
        "premier",
        "predseda vlady",
        "ministr",
        "kabinet",

        # Parliament
        "parlament",
        "snemovn",
        "poslan",
        "senat",
        "senator",

        # Elections and politics
        "volb",
        "voleb",
        "koalic",
        "opozic",
        "politic",
        "politick",
        "zakon",
        "legislativ",
        "ustavn",
        "referend",

        # Parties
        "hnuti ano",
        "ano 2011",
        "ods",
        "stan",
        "spolu",
        "pirat",
        "spd",
        "motorist",
        "top 09",
        "kdu-csl",

        # Institutions
        "prezident",
        "prazsky hrad",
        "ustavni soud",

    ],

    "security": [

        # Defense
        "obran",
        "armad",
        "vojak",
        "vojensk",
        "vojsk",
        "ozbrojen",

        # NATO
        "nato",
        "severoatlantick",

        # Military technology
        "zbran",
        "zbrojn",
        "munic",
        "raket",
        "protivzdusn",
        "dron",
        "bezpilotn",
        "stihack",
        "letoun",
        "f-35",
        "tank",
        "delostrelectv",

        # Intelligence and security
        "bezpecnost",
        "kyber",
        "hybridni hrozb",
        "teror",
        "sabotaz",
        "spionaz",
        "rozvedk",
        "kontrarozvedk",
        "tajne sluzb",
        "bis",
        "vzis",
        "nukib",

        # Conflict
        "valk",
        "invaz",
        "mobilizac",
        "vojenska operac",

    ],

    "foreign_affairs": [

        # Diplomacy
        "diplomac",
        "diplomat",
        "zahranic",
        "mezinarodn",
        "velvyslan",
        "ambasad",
        "bilateral",
        "summit",

        # EU
        "evropska unie",
        "evropske unie",
        "evropska komise",
        "evropsky parlament",
        "evropska rada",
        "brusel",
        "unijn",

        # International organizations
        "nato",
        "osn",
        "visegrad",
        "v4",

        # Foreign countries
        "ukrajin",
        "rusk",
        "rusko",
        "slovensk",
        "polsk",
        "nemeck",
        "cina",
        "cinsk",
        "spojene staty",
        "washington",
        "izrael",
        "iran",

        # Foreign policy
        "sankc",
        "strategicke partnerstv",
        "vojenska pomoc",

    ],

}


# ============================================================
# CZECH RELEVANCE
# ============================================================

# These are higher-confidence Czech-specific references.
# Generic terms such as "government" or "president"
# are deliberately excluded.

CZECH_KEYWORDS = [

    "cesko",
    "ceska republika",
    "ceske republiky",
    "cesky",
    "ceska",
    "ceske",
    "ceskem",
    "cesku",

    "praha",
    "praze",
    "prazsk",

    "snemovn",
    "prazsky hrad",
    "armada cr",

    "babis",
    "pavel",
    "hnuti ano",
    "ods",
    "kdu-csl",
    "top 09",
    "motorist",

    "ceska televize",
    "cesky rozhlas",

    "nukib",
]


# ============================================================
# HELPERS
# ============================================================

def utcnow():
    return datetime.now(timezone.utc)


def timestamp(dt):
    return dt.astimezone(timezone.utc).strftime(
        "%Y-%m-%dT%H:%M:%SZ"
    )


def normalize_space(text):
    return " ".join(str(text or "").split()).strip()


def normalize_text(text):

    text = unicodedata.normalize(
        "NFKD",
        str(text or "").lower()
    )

    return "".join(
        char for char in text
        if not unicodedata.combining(char)
    )


def matches(text, keyword):

    """
    Match keyword stems at word beginnings.

    Example:
        'ministr' matches 'ministra' and 'ministrem'.
    """

    keyword = normalize_text(keyword)

    return bool(
        re.search(
            r"(?<!\w)" + re.escape(keyword),
            text
        )
    )


def hash_key(text):

    return hashlib.sha256(
        text.encode("utf-8")
    ).hexdigest()


def normalize_url(url):

    parts = urlsplit(normalize_space(url))

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


def clean_html(text):

    return normalize_space(
        BeautifulSoup(
            text or "",
            "html.parser"
        ).get_text(" ", strip=True)
    )


def short_lead(text):

    text = clean_html(text)

    if not text:
        return ""

    sentences = re.split(
        r"(?<=[.!?])\s+",
        text
    )

    return " ".join(
        sentences[:2]
    )[:600]


# ============================================================
# RSS COLLECTION
# ============================================================

SESSION = requests.Session()
SESSION.headers.update(HEADERS)


def fetch_feed(url):

    for attempt in range(3):

        try:

            response = SESSION.get(
                url,
                timeout=TIMEOUT
            )

            response.raise_for_status()

            parsed = feedparser.parse(
                response.content
            )

            if parsed.entries:
                return parsed.entries

            LOG.warning(
                "Feed returned no entries: %s",
                url
            )

        except Exception as exc:

            LOG.warning(
                "RSS error: %s (%s)",
                url,
                exc
            )

        if attempt < 2:
            time.sleep(2 * (attempt + 1))

    return []


def parse_date(entry):

    for key in (
        "published_parsed",
        "updated_parsed",
        "created_parsed",
    ):

        value = entry.get(key)

        if value:

            try:

                return datetime.fromtimestamp(
                    calendar.timegm(value),
                    timezone.utc
                )

            except Exception:
                continue

    return None


def collect_articles():

    articles = []

    successful_sources = 0

    for source, feeds in SOURCES.items():

        entries = []

        for feed in feeds:

            entries = fetch_feed(feed)

            if entries:
                break

        if entries:
            successful_sources += 1

        source_count = 0

        for entry in entries:

            title = clean_html(
                entry.get("title", "")
            )

            url = normalize_url(
                entry.get("link", "")
            )

            published = parse_date(entry)

            if not title or not url or not published:
                continue

            # Skip future-dated entries.
            if published > utcnow() + timedelta(minutes=10):
                continue

            lead = short_lead(
                entry.get("summary")
                or entry.get("description")
                or ""
            )

            articles.append({

                "source": source,

                "url": url,

                "published_utc": timestamp(published),

                "title_raw": title,

                "lead_raw": lead,

            })

            source_count += 1

        LOG.info(
            "%s: %s articles",
            source,
            source_count
        )

    LOG.info(
        "Total collected: %s",
        len(articles)
    )

    if successful_sources == 0:

        raise RuntimeError(
            "All RSS sources failed."
        )

    return articles


# ============================================================
# CLASSIFICATION
# ============================================================

def classify(article):

    title = normalize_text(
        article["title_raw"]
    )

    lead = normalize_text(
        article["lead_raw"]
    )

    text = title + " " + lead

    scores = {}

    for topic, keywords in TOPIC_KEYWORDS.items():

        scores[topic] = (

            3 * sum(
                matches(title, word)
                for word in keywords
            )

            + sum(
                matches(lead, word)
                for word in keywords
            )

        )

    article["topic_scores"] = scores

    article["topics"] = [

        topic

        for topic in TOPICS

        if scores[topic] > 0

    ]

    article["topics"].sort(
        key=lambda topic: -scores[topic]
    )

    article["primary_topic"] = (
        article["topics"][0]
        if article["topics"]
        else None
    )

    # Czech relevance test.
    czech_related = any(
        matches(text, word)
        for word in CZECH_KEYWORDS
    )

    # Domestic Czech political institutions often appear
    # without the explicit word "Czech".
    domestic_terms = [
        "vlada",
        "premier",
        "snemovn",
        "poslan",
        "senat",
        "ministr",
        "volb",
        "koalic",
    ]

    if article["source"] == "iROZHLAS (Domestic)":

        czech_related = czech_related or any(
            matches(text, word)
            for word in domestic_terms
        )

    return bool(
        article["topics"]
        and czech_related
    )


# ============================================================
# ARGOS TRANSLATION
# ============================================================

TRANSLATOR = None

TRANSLATION_CACHE = {}


def load_translator():

    """
    Initialize local Czech -> English translation.

    Download the language model only if not installed.
    """

    global TRANSLATOR

    if TRANSLATOR is not None:
        return

    LOG.info("Initializing Argos Translate...")

    installed = (
        argostranslate.translate.get_installed_languages()
    )

    source = next(
        (lang for lang in installed if lang.code == "cs"),
        None
    )

    target = next(
        (lang for lang in installed if lang.code == "en"),
        None
    )

    if source and target:

        try:
            TRANSLATOR = source.get_translation(target)
        except (ValueError, AttributeError):
            TRANSLATOR = None

    if TRANSLATOR is not None:

        LOG.info("Cached translation model loaded.")
        return

    LOG.info("Downloading Czech-English model...")

    argostranslate.package.update_package_index()

    packages = (
        argostranslate.package.get_available_packages()
    )

    package = next(
        (
            pkg for pkg in packages

            if pkg.from_code == "cs"
            and pkg.to_code == "en"
        ),
        None
    )

    if package is None:

        raise RuntimeError(
            "Czech-English Argos model unavailable."
        )

    model_path = package.download()

    LOG.info("Installing translation model...")

    argostranslate.package.install_from_path(
        model_path
    )

    # Refresh the installed language registry.
    installed = (
        argostranslate.translate.get_installed_languages()
    )

    source = next(
        (lang for lang in installed if lang.code == "cs"),
        None
    )

    target = next(
        (lang for lang in installed if lang.code == "en"),
        None
    )

    if source is None or target is None:

        raise RuntimeError(
            "Argos model installation failed."
        )

    TRANSLATOR = source.get_translation(target)

    if TRANSLATOR is None:

        raise RuntimeError(
            "Unable to initialize Czech-English translator."
        )

    LOG.info("Argos translator ready.")


def translate(text):

    text = normalize_space(text)

    if not text:
        return ""

    if text in TRANSLATION_CACHE:
        return TRANSLATION_CACHE[text]

    if TRANSLATOR is None:

        raise RuntimeError(
            "Translation model is not initialized."
        )

    result = normalize_space(
        TRANSLATOR.translate(text)
    )

    if not result:

        raise RuntimeError(
            "Argos returned an empty translation."
        )

    TRANSLATION_CACHE[text] = result

    return result


def needs_translation(article):

    return (
        not article.get("title_en")
        or (
            article.get("lead_raw")
            and not article.get("lead_en")
        )
    )


def translate_article(article):

    if not article.get("title_en"):

        article["title_en"] = translate(
            article["title_raw"]
        )

    if (
        article.get("lead_raw")
        and not article.get("lead_en")
    ):

        article["lead_en"] = translate(
            article["lead_raw"]
        )

    complete = (
        bool(article.get("title_en"))
        and (
            not article.get("lead_raw")
            or bool(article.get("lead_en"))
        )
    )

    article["translation_status"] = (
        "translated"
        if complete
        else "partial"
    )

    article["translation_provider"] = "argos"

    return article


# ============================================================
# DEDUPLICATION
# ============================================================

def prepare(article):

    article = dict(article)

    url = normalize_url(
        article.get("url", "")
    )

    article["fingerprint"] = hash_key(url)

    article.setdefault(
        "id",
        hash_key(url)
    )

    article.setdefault("title_en", None)
    article.setdefault("lead_en", None)

    article.setdefault(
        "translation_status",
        "pending"
    )

    return article


def merge_articles(articles):

    """
    Deduplicate using normalized URL.

    Preserve translations from previous runs.
    Prefer records with more complete summaries.
    """

    merged = {}

    for raw in articles:

        article = prepare(raw)

        key = article["fingerprint"]

        if key not in merged:

            merged[key] = article
            continue

        old = merged[key]

        if len(article.get("lead_raw", "")) > len(
            old.get("lead_raw", "")
        ):

            old["lead_raw"] = article["lead_raw"]

        for field in (
            "title_en",
            "lead_en",
            "translation_provider",
        ):

            if not old.get(field):
                old[field] = article.get(field)

    return sorted(
        merged.values(),
        key=lambda a: a["published_utc"],
        reverse=True
    )


# ============================================================
# JSON STORAGE
# ============================================================

def read_json(path):

    if not path.exists():
        return []

    content = path.read_text(
        encoding="utf-8"
    ).strip()

    if not content:
        return []

    try:

        data = json.loads(content)

    except json.JSONDecodeError as exc:

        raise RuntimeError(
            f"Invalid JSON in {path}: {exc}"
        ) from exc

    if isinstance(data, list):
        return data

    if isinstance(data, dict):
        return data.get("articles", [])

    raise ValueError(
        f"Unexpected JSON structure: {path}"
    )


def write_json(path, articles, **metadata):

    path.parent.mkdir(
        parents=True,
        exist_ok=True
    )

    payload = {

        "updated_at_utc": timestamp(utcnow()),

        **metadata,

        "count": len(articles),

        "articles": articles,

    }

    temporary = path.with_suffix(".tmp")

    temporary.write_text(
        json.dumps(
            payload,
            ensure_ascii=False,
            indent=2
        ),
        encoding="utf-8"
    )

    temporary.replace(path)


# ============================================================
# MAIN
# ============================================================

def main():

    start = time.monotonic()

    LOG.info("Czech News Tracker starting.")

    LOG.info(
        "Rolling window: %s hours",
        KEEP_HOURS
    )

    LOG.info(
        "Translation limit: %s",
        TRANSLATE_LIMIT or "unlimited"
    )

    # --------------------------------------------------------
    # 1. COLLECT
    # --------------------------------------------------------

    collected = collect_articles()

    # --------------------------------------------------------
    # 2. LOAD HISTORICAL DATA
    # --------------------------------------------------------

    existing = read_json(
        DATA_DIR / "articles_archive.json"
    )

    LOG.info(
        "Previously archived: %s",
        len(existing)
    )

    # --------------------------------------------------------
    # 3. MERGE AND CLASSIFY
    # --------------------------------------------------------

    merged = merge_articles(
        existing + collected
    )

    relevant = []

    for article in merged:

        if classify(article):
            relevant.append(article)

    LOG.info(
        "Relevant articles: %s",
        len(relevant)
    )

    # --------------------------------------------------------
    # 4. TRANSLATE
    # --------------------------------------------------------

    pending = [
        article
        for article in relevant
        if needs_translation(article)
    ]

    LOG.info(
        "Articles awaiting translation: %s",
        len(pending)
    )

    translated_count = 0

    if pending:

        # Fail explicitly if the translation model cannot
        # be initialized, rather than silently writing
        # untranslated articles.

        load_translator()

        # Prioritize recent articles.
        # Oldest pending articles are processed first
        # within the rolling window.

        cutoff = utcnow() - timedelta(
            hours=KEEP_HOURS
        )

        def priority(article):

            published = datetime.strptime(
                article["published_utc"],
                "%Y-%m-%dT%H:%M:%SZ"
            ).replace(tzinfo=timezone.utc)

            return (
                0 if published >= cutoff else 1,
                published
            )

        pending.sort(key=priority)

        for article in pending:

            if (
                TRANSLATE_LIMIT > 0
                and translated_count >= TRANSLATE_LIMIT
            ):
                break

            try:

                translate_article(article)

                translated_count += 1

                if translated_count % 10 == 0:

                    LOG.info(
                        "Translated %s articles",
                        translated_count
                    )

            except Exception as exc:

                LOG.warning(
                    "Translation failed for %s: %s",
                    article["url"],
                    exc
                )

    # --------------------------------------------------------
    # 5. SAVE ARCHIVE
    # --------------------------------------------------------

    archive = merge_articles(relevant)

    write_json(
        DATA_DIR / "articles_archive.json",
        archive
    )

    # --------------------------------------------------------
    # 6. BUILD ROLLING WINDOW
    # --------------------------------------------------------

    cutoff = utcnow() - timedelta(
        hours=KEEP_HOURS
    )

    latest = [

        article

        for article in archive

        if datetime.strptime(
            article["published_utc"],
            "%Y-%m-%dT%H:%M:%SZ"
        ).replace(
            tzinfo=timezone.utc
        ) >= cutoff

    ]

    write_json(
        DATA_DIR / "articles_latest.json",
        latest,
        keep_hours=KEEP_HOURS
    )

    # --------------------------------------------------------
    # 7. SAVE TOPIC FEEDS
    # --------------------------------------------------------

    for topic in TOPICS:

        subset = [

            article

            for article in latest

            if topic in article.get("topics", [])

        ]

        write_json(
            DATA_DIR / f"articles_{topic}.json",
            subset,
            topic=topic
        )

        LOG.info(
            "%s: %s articles",
            topic,
            len(subset)
        )

    # --------------------------------------------------------
    # 8. SUMMARY
    # --------------------------------------------------------

    fully_translated = sum(
        article.get("translation_status") == "translated"
        for article in archive
    )

    LOG.info("Collection complete.")

    LOG.info(
        "Latest articles: %s",
        len(latest)
    )

    LOG.info(
        "Archived articles: %s",
        len(archive)
    )

    LOG.info(
        "New translations: %s",
        translated_count
    )

    LOG.info(
        "Total fully translated: %s",
        fully_translated
    )

    LOG.info(
        "Elapsed: %.1f seconds",
        time.monotonic() - start
    )


if __name__ == "__main__":
    main()
