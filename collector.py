# -*- coding: utf-8 -*-

"""
CZECH NEWS TRACKER — VERSION 3
==============================

Czech political, security, and foreign affairs monitoring.

Features:
- RSS collection from major Czech news outlets
- Context-aware, rule-based relevance filtering
- Three topic categories
- NLLB-200 Czech-to-English translation
- CPU-only batch translation
- Deduplication
- Rolling 48-hour news feeds
- Permanent archive
- Translation caching across runs
- Automatic retranslation of older model outputs

No translation API keys required.

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
from urllib.parse import (
    urlsplit,
    urlunsplit,
    parse_qsl,
    urlencode,
)

import requests
import feedparser
import torch

from bs4 import BeautifulSoup

from transformers import (
    AutoTokenizer,
    AutoModelForSeq2SeqLM,
)


# ============================================================
# CONFIGURATION
# ============================================================

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s"
)

LOG = logging.getLogger("czech-news")


DATA_DIR = Path("data")

KEEP_HOURS = int(
    os.getenv("KEEP_HOURS", "48")
)

TRANSLATE_LIMIT = int(
    os.getenv("TRANSLATE_LIMIT", "60")
)

BATCH_SIZE = int(
    os.getenv("BATCH_SIZE", "4")
)

MODEL_NAME = "facebook/nllb-200-distilled-600M"

TRANSLATION_VERSION = "nllb200-v1"

SOURCE_LANGUAGE = "ces_Latn"
TARGET_LANGUAGE = "eng_Latn"

TIMEOUT = 20

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 "
        "(compatible; CzechNewsTracker/3.0)"
    ),
    "Accept": "application/rss+xml, application/xml, text/xml, */*",
    "Accept-Language": "cs-CZ,cs;q=0.9,en;q=0.7",
}

TOPICS = (
    "politics",
    "security",
    "foreign_affairs",
)


# ============================================================
# NEWS SOURCES
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
# CLASSIFICATION RULES
# ============================================================

"""
Unlike the previous version, merely mentioning Germany,
Russia, or Ukraine does not qualify an article as foreign
affairs.

The classifier looks for:
1. Czech relevance
2. Substantive political/security/foreign-policy indicators
3. Strong exclusion signals for unrelated content

Czech words are normalized before matching.

This remains a rule-based classifier, not a semantic model.
"""


# Direct references to Czechia or Czech institutions.

CZECH_SIGNALS = [

    "cesk",
    "cesko",
    "cesku",

    "praha",
    "praze",
    "prazsk",

    "snemovn",
    "prazsky hrad",

    "armada cr",

    "babis",
    "petr pavel",
    "metnar",
    "macinka",
    "zuna",

    "hnuti ano",
    "ods",
    "kdu-csl",
    "top 09",
    "motoriste",

    "ceska televize",
    "cesky rozhlas",

    "nukib",
]


# Generic Czech political institutions and processes.

POLITICAL_SIGNALS = [

    "vlad",
    "premier",
    "predseda vlady",

    "ministr",
    "ministerstv",
    "kabinet",

    "parlament",
    "snemovn",
    "poslan",

    "senat",
    "senator",

    "volb",
    "voleb",

    "koalic",
    "opozic",

    "politick",
    "zakon",
    "legislativ",

    "ustavn",
    "referend",

    "prezident",

    "rozpoct",
    "verejna politika",

    "ustavni soud",
]


# Specific national security, defense, and military terms.

SECURITY_SIGNALS = [

    "ministerstvo obrany",

    "armad",
    "vojak",
    "vojensk",
    "ozbrojene sily",

    "obran",
    "protivzdusn",

    "zbrojen",
    "zbrojni prumysl",

    "munic",
    "balistick",
    "strel",
    "raket",

    "stihack",
    "f-35",

    "bezpilotn",
    "dron",

    "kybernetick",
    "kyberutok",

    "bezpecnost",
    "bezpecnostni",

    "teror",
    "bombov",

    "spionaz",
    "sabotaz",

    "kontrarozved",
    "zpravodajsk",

    "tajne sluzb",

    "bis",
    "nukib",

    "hybridni hrozb",

    "vojensky konflikt",
    "valecny konflikt",

    "mobilizac",

    "vojenska pomoc",
]


# Stronger indicators of foreign policy and diplomacy.

FOREIGN_POLICY_SIGNALS = [

    "diplomac",
    "diplomat",

    "zahranicni politika",

    "ministerstvo zahranici",

    "mezinarodni vztah",

    "velvyslan",
    "ambasad",

    "bilateral",
    "dohoda mezi staty",

    "mezistatni",

    "summit",

    "evropska unie",
    "evropske unie",

    "evropska komise",
    "evropsky parlament",
    "evropska rada",

    "brusel",

    "nato",
    "severoatlantick",

    "osn",

    "sankc",
    "embarg",

    "zahranicni pomoc",

    "strategicke partnerstv",

    "koalice ochotnych",

    "mezinarodni spoluprace",

    "mezinarodni jednani",
]


# Geopolitical indicators.
#
# These provide supporting evidence, but cannot qualify
# an article for foreign affairs on their own.

GEOPOLITICAL_SIGNALS = [

    "ukrajin",
    "rusko",
    "rusk",

    "cina",
    "cinsk",

    "spojene staty",
    "washington",

    "nemeck",
    "slovensk",
    "polsk",

    "izrael",
    "iran",

    "valka",
    "invaze",

    "geopolit",
]


# Additional indicators for cross-border political decisions.

CROSS_BORDER_POLICY_SIGNALS = [

    "viz",
    "zakaz vstupu",
    "vstup do ceska",

    "hranice",
    "migrac",

    "sankc",
    "embarg",

    "mezinarodni dohoda",

    "setkani s",
    "jednani s",

    "kancler",
    "prezident",
    "premier",

    "zahranicni ministr",

    "vojenska pomoc",
]


# Exclude clearly unrelated content.
#
# A strong, specific policy or security signal can override
# an exclusion when the article has substantive relevance.

EXCLUSION_SIGNALS = [

    # Sports
    "tenis",
    "fotbal",
    "hokej",
    "sportovn",
    "sportovec",
    "sportovkyne",

    "wta",
    "atp",
    "liga mistru",

    "turnaj",
    "golf",
    "deblist",

    # Entertainment and culture
    "divadeln",
    "festival",
    "koncert",

    "hudebn",
    "filmov",

    "herec",
    "herecka",

    "celebr",
    "reality show",

    # Lifestyle
    "recept",
    "vareni",

    "moda",
    "kosmetik",

    "horoskop",
    "celebrity",
]


# Very specific terms that can override a content exclusion.

HIGH_CONFIDENCE_SIGNALS = [

    "ministerstvo obrany",
    "ministerstvo zahranici",

    "protivzdusna obrana",

    "balistick",
    "vojenska pomoc",

    "bezpecnostni informacni sluzba",

    "bombove vyhruzk",
    "teroristick",

    "kyberneticky utok",
    "spionaz",
    "sabotaz",

    "sankce",
    "zakaz vstupu",

    "vladni narizeni",
    "verejna zakazka",
    "zakon",
    "legislativ",

    "diplomaticka jednani",
]


# ============================================================
# GENERAL HELPERS
# ============================================================

def utcnow():
    return datetime.now(timezone.utc)


def timestamp(dt):

    return dt.astimezone(timezone.utc).strftime(
        "%Y-%m-%dT%H:%M:%SZ"
    )


def normalize_space(text):

    return " ".join(
        str(text or "").split()
    ).strip()


def normalize_text(text):

    text = unicodedata.normalize(
        "NFKD",
        str(text or "").lower()
    )

    return "".join(
        character
        for character in text
        if not unicodedata.combining(character)
    )


def matches(text, keyword):

    keyword = normalize_text(keyword)

    pattern = (
        r"(?<!\w)"
        + re.escape(keyword)
    )

    return bool(
        re.search(pattern, text)
    )


def count_matches(text, keywords):

    return sum(
        matches(text, keyword)
        for keyword in keywords
    )


def hash_key(text):

    return hashlib.sha256(
        text.encode("utf-8")
    ).hexdigest()


def normalize_url(url):

    parts = urlsplit(
        normalize_space(url)
    )

    query = [

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
        urlencode(query),
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
                "Empty RSS feed: %s",
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

    for field in (
        "published_parsed",
        "updated_parsed",
        "created_parsed",
    ):

        value = entry.get(field)

        if value:

            try:

                return datetime.fromtimestamp(
                    calendar.timegm(value),
                    timezone.utc
                )

            except (
                ValueError,
                TypeError,
                OverflowError
            ):

                pass

    return None


def collect_articles():

    articles = []
    successful_sources = 0

    for source, feeds in SOURCES.items():

        entries = []

        for feed in feeds:

            # Collect all configured feeds rather than
            # treating additional feeds as fallbacks.

            entries.extend(
                fetch_feed(feed)
            )

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
# IMPROVED CLASSIFICATION
# ============================================================

def classify(article):

    title = normalize_text(
        article.get("title_raw", "")
    )

    lead = normalize_text(
        article.get("lead_raw", "")
    )

    text = title + " " + lead

    source = article.get("source", "")

    # --------------------------------------------------------
    # 1. CZECH RELEVANCE
    # --------------------------------------------------------

    czech_score = (

        3 * count_matches(
            title,
            CZECH_SIGNALS
        )

        + count_matches(
            lead,
            CZECH_SIGNALS
        )

    )

    # Domestic feed provides additional Czech context,
    # but does not automatically qualify an article.

    domestic_source = (
        source == "iROZHLAS (Domestic)"
    )

    domestic_institution = (
        count_matches(
            text,
            POLITICAL_SIGNALS
        ) > 0
    )

    czech_related = (
        czech_score > 0
        or (
            domestic_source
            and domestic_institution
        )
    )

    # --------------------------------------------------------
    # 2. TOPIC SIGNALS
    # --------------------------------------------------------

    political_score = (

        3 * count_matches(
            title,
            POLITICAL_SIGNALS
        )

        + count_matches(
            lead,
            POLITICAL_SIGNALS
        )

    )

    security_score = (

        3 * count_matches(
            title,
            SECURITY_SIGNALS
        )

        + count_matches(
            lead,
            SECURITY_SIGNALS
        )

    )

    foreign_policy_score = (

        3 * count_matches(
            title,
            FOREIGN_POLICY_SIGNALS
        )

        + count_matches(
            lead,
            FOREIGN_POLICY_SIGNALS
        )

    )

    geopolitical_score = (

        2 * count_matches(
            title,
            GEOPOLITICAL_SIGNALS
        )

        + count_matches(
            lead,
            GEOPOLITICAL_SIGNALS
        )

    )

    cross_border_score = count_matches(
        text,
        CROSS_BORDER_POLICY_SIGNALS
    )

    # --------------------------------------------------------
    # 3. EXCLUSION FILTER
    # --------------------------------------------------------

    exclusion_score = count_matches(
        text,
        EXCLUSION_SIGNALS
    )

    high_confidence = count_matches(
        text,
        HIGH_CONFIDENCE_SIGNALS
    ) > 0

    # Dedicated sports pages are ordinarily excluded.
    # Policy reporting about athletes or visas can survive
    # when accompanied by a high-confidence policy signal.

    sport_url = "/sport" in article.get(
        "url",
        ""
    ).lower()

    if (
        sport_url
        and not high_confidence
    ):
        return False

    # Exclude unrelated culture, entertainment, and sports.

    if (
        exclusion_score > 0
        and not high_confidence
    ):
        return False

    # --------------------------------------------------------
    # 4. CLASSIFY
    # --------------------------------------------------------

    scores = {

        "politics": political_score,

        "security": security_score,

        "foreign_affairs": foreign_policy_score,

    }

    topics = []

    if czech_related:

        # Politics:
        # Must concern actual political institutions,
        # government decisions, elections, or policy.

        if political_score >= 3:

            topics.append(
                "politics"
            )

        # Security:
        # Require a strong title indicator or multiple
        # supporting signals.

        if security_score >= 3:

            topics.append(
                "security"
            )

        # Foreign affairs:
        # A country reference alone is insufficient.

        if (
            foreign_policy_score >= 3
            or (
                geopolitical_score >= 3
                and cross_border_score >= 1
            )
        ):

            topics.append(
                "foreign_affairs"
            )

    # --------------------------------------------------------
    # 5. STORE RESULTS
    # --------------------------------------------------------

    topics.sort(
        key=lambda topic: (
            -scores[topic],
            topic
        )
    )

    article["topic_scores"] = scores

    article["topics"] = topics

    article["primary_topic"] = (
        topics[0]
        if topics
        else None
    )

    article["czech_related"] = czech_related

    article["classification_version"] = "v3"

    return bool(topics)


# ============================================================
# NLLB TRANSLATION
# ============================================================

TOKENIZER = None
MODEL = None

TRANSLATION_CACHE = {}


def load_translator():

    """
    Load NLLB-200 distilled 600M.

    The model is downloaded on first use and subsequently
    loaded from the Hugging Face cache.

    CPU-only inference.
    """

    global TOKENIZER, MODEL

    if MODEL is not None:
        return

    LOG.info(
        "Initializing NLLB-200 translator..."
    )

    torch.set_num_threads(2)

    TOKENIZER = AutoTokenizer.from_pretrained(
        MODEL_NAME,
        src_lang=SOURCE_LANGUAGE
    )

    MODEL = AutoModelForSeq2SeqLM.from_pretrained(
        MODEL_NAME
    )

    MODEL.to("cpu")
    MODEL.eval()

    LOG.info(
        "NLLB-200 Czech-English translator ready."
    )


def translate_batch(texts):

    """
    Translate a batch of Czech strings to English.

    Returns translated strings in the same order.

    Uses NLLB language tokens to force English output.
    """

    if MODEL is None or TOKENIZER is None:

        raise RuntimeError(
            "Translation model not initialized."
        )

    texts = [
        normalize_space(text)
        for text in texts
    ]

    if not texts:
        return []

    inputs = TOKENIZER(
        texts,
        return_tensors="pt",
        padding=True,
        truncation=True,
        max_length=512
    )

    target_id = TOKENIZER.convert_tokens_to_ids(
        TARGET_LANGUAGE
    )

    with torch.inference_mode():

        outputs = MODEL.generate(

            **inputs,

            forced_bos_token_id=target_id,

            max_new_tokens=256,

            num_beams=3,

            early_stopping=True,

        )

    translated = TOKENIZER.batch_decode(
        outputs,
        skip_special_tokens=True
    )

    return [
        normalize_space(text)
        for text in translated
    ]


def needs_translation(article):

    """
    Retranslate records from older translation engines.

    This automatically replaces previous Argos and MarianMT
    translations without requiring the archive to be deleted.
    """

    return (
        article.get("translation_version")
        != TRANSLATION_VERSION
        or not article.get("title_en")
        or (
            article.get("lead_raw")
            and not article.get("lead_en")
        )
    )


def translate_articles(articles):

    """
    Translate article headlines and summaries in batches.

    Only translates missing or outdated records.

    Each article uses one combined model input batch entry
    for its headline and one for its summary.
    """

    pending = [
        article
        for article in articles
        if needs_translation(article)
    ]

    LOG.info(
        "Articles requiring translation: %s",
        len(pending)
    )

    if not pending:
        return 0

    # Prioritize recent articles.

    cutoff = utcnow() - timedelta(
        hours=KEEP_HOURS
    )

    def priority(article):

        published = datetime.strptime(
            article["published_utc"],
            "%Y-%m-%dT%H:%M:%SZ"
        ).replace(
            tzinfo=timezone.utc
        )

        return (
            0 if published >= cutoff else 1,
            published
        )

    pending.sort(
        key=priority
    )

    if TRANSLATE_LIMIT > 0:

        pending = pending[:TRANSLATE_LIMIT]

    load_translator()

    translated_count = 0

    for start in range(
        0,
        len(pending),
        BATCH_SIZE
    ):

        batch = pending[
            start:start + BATCH_SIZE
        ]

        # Each article has two fields.

        texts = []
        mapping = []

        for article in batch:

            for field in (
                "title_raw",
                "lead_raw"
            ):

                text = article.get(field, "")

                if text:

                    texts.append(text)

                    mapping.append(
                        (article, field)
                    )

        if not texts:
            continue

        try:

            translated = translate_batch(
                texts
            )

            if len(translated) != len(mapping):
                raise RuntimeError(
                    "Translation output count mismatch."
                )

            # Collect outputs before modifying articles.

            staged = {}

            for (
                (article, field),
                english
            ) in zip(mapping, translated):

                if not english:
                    raise RuntimeError(
                        "Empty translation returned."
                    )

                staged.setdefault(
                    id(article),
                    {}
                )[field] = english

            for article in batch:

                result = staged.get(
                    id(article),
                    {}
                )

                title_en = result.get(
                    "title_raw"
                )

                lead_en = result.get(
                    "lead_raw"
                )

                if not title_en:
                    continue

                if (
                    article.get("lead_raw")
                    and not lead_en
                ):
                    continue

                article["title_en"] = title_en

                article["lead_en"] = lead_en

                article["translation_provider"] = "nllb200"

                article["translation_version"] = (
                    TRANSLATION_VERSION
                )

                article["translation_status"] = (
                    "translated"
                )

                translated_count += 1

            LOG.info(
                "Translated %s / %s articles",
                translated_count,
                len(pending)
            )

        except Exception as exc:

            LOG.warning(
                "Batch translation failed: %s",
                exc
            )

            # Preserve previous translations for retry.
            # Do not falsely mark old translations as NLLB.

    return translated_count


# ============================================================
# DEDUPLICATION
# ============================================================

def prepare(article):

    article = dict(article)

    url = normalize_url(
        article.get("url", "")
    )

    article["fingerprint"] = hash_key(
        url
    )

    article.setdefault(
        "id",
        hash_key(url)
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

    return article


def merge_articles(articles):

    """
    Deduplicate by normalized URL.

    Preserve translations and prefer longer original leads.
    """

    merged = {}

    for raw in articles:

        article = prepare(raw)

        key = article["fingerprint"]

        if key not in merged:

            merged[key] = article

            continue

        old = merged[key]

        if len(
            article.get("lead_raw", "")
        ) > len(
            old.get("lead_raw", "")
        ):

            old["lead_raw"] = article[
                "lead_raw"
            ]

        # Preserve the newest available translation version.

        old_version = old.get(
            "translation_version"
        )

        new_version = article.get(
            "translation_version"
        )

        if (
            new_version == TRANSLATION_VERSION
            and old_version != TRANSLATION_VERSION
        ):

            for field in (
                "title_en",
                "lead_en",
                "translation_status",
                "translation_provider",
                "translation_version",
            ):

                old[field] = article.get(
                    field
                )

        else:

            for field in (
                "title_en",
                "lead_en",
            ):

                if not old.get(field):
                    old[field] = article.get(field)

            if not old.get("translation_version"):
                old["translation_version"] = new_version

            if not old.get("translation_provider"):
                old["translation_provider"] = article.get(
                    "translation_provider"
                )

    return sorted(
        merged.values(),
        key=lambda article: article.get(
            "published_utc",
            ""
        ),
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

    data = json.loads(
        content
    )

    if isinstance(data, list):
        return data

    if isinstance(data, dict):

        articles = data.get(
            "articles",
            []
        )

        if isinstance(articles, list):
            return articles

    raise ValueError(
        f"Invalid JSON structure: {path}"
    )


def write_json(path, articles, **metadata):

    path.parent.mkdir(
        parents=True,
        exist_ok=True
    )

    payload = {

        "updated_at_utc": timestamp(
            utcnow()
        ),

        **metadata,

        "count": len(articles),

        "articles": articles,

    }

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

    temporary.replace(path)


# ============================================================
# MAIN
# ============================================================

def main():

    start = time.monotonic()

    LOG.info(
        "Czech News Tracker v3 starting."
    )

    LOG.info(
        "Translation: NLLB-200 distilled 600M"
    )

    LOG.info(
        "Rolling window: %s hours",
        KEEP_HOURS
    )

    # --------------------------------------------------------
    # 1. COLLECT RSS ARTICLES
    # --------------------------------------------------------

    collected = collect_articles()

    # --------------------------------------------------------
    # 2. LOAD HISTORICAL ARCHIVE
    # --------------------------------------------------------

    existing = read_json(
        DATA_DIR / "articles_archive.json"
    )

    LOG.info(
        "Existing archive: %s articles",
        len(existing)
    )

    # --------------------------------------------------------
    # 3. MERGE AND DEDUPLICATE
    # --------------------------------------------------------

    merged = merge_articles(
        existing + collected
    )

    LOG.info(
        "Unique articles: %s",
        len(merged)
    )

    # --------------------------------------------------------
    # 4. CLASSIFY AND FILTER
    # --------------------------------------------------------

    relevant = []

    for article in merged:

        if classify(article):

            relevant.append(
                article
            )

    LOG.info(
        "Relevant articles: %s",
        len(relevant)
    )

    # --------------------------------------------------------
    # 5. TRANSLATE
    # --------------------------------------------------------

    translated_count = translate_articles(
        relevant
    )

    # --------------------------------------------------------
    # 6. SAVE ARCHIVE
    # --------------------------------------------------------

    archive = merge_articles(
        relevant
    )

    write_json(
        DATA_DIR / "articles_archive.json",
        archive
    )

    # --------------------------------------------------------
    # 7. BUILD ROLLING 48-HOUR FEED
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
    # 8. BUILD TOPIC FEEDS
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
    # 9. SUMMARY
    # --------------------------------------------------------

    fully_translated = sum(
        article.get("translation_version")
        == TRANSLATION_VERSION
        for article in archive
    )

    LOG.info(
        "Collection complete."
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
        "New NLLB translations: %s",
        translated_count
    )

    LOG.info(
        "Total NLLB-translated articles: %s",
        fully_translated
    )

    LOG.info(
        "Elapsed: %.1f seconds",
        time.monotonic() - start
    )


if __name__ == "__main__":
    main()
