"""
COMPUTE units for Discovery Shopping.

Hermetic functions for quiz generation, product fetching, review
aggregation, and explainable ranking.
Input: params dict. Output: result dict.
"""

import re
import time
import hashlib
from typing import Any, Dict, List
from datetime import datetime

try:
    import requests
    HAS_REQUESTS = True
except ImportError:
    HAS_REQUESTS = False

try:
    from bs4 import BeautifulSoup
    HAS_BS4 = True
except ImportError:
    HAS_BS4 = False

import warnings
warnings.filterwarnings("ignore", message=".*duckduckgo_search.*renamed.*")

try:
    from ddgs import DDGS
    HAS_DDGS = True
except ImportError:
    try:
        from duckduckgo_search import DDGS
        HAS_DDGS = True
    except ImportError:
        HAS_DDGS = False


# =========================================================================
# QUIZ GENERATION
# =========================================================================

QUIZ_TEMPLATES = {
    "headphones": [
        {"id": "q1", "text": "Primary use?",
         "options": ["Music", "Gaming", "Calls", "Mixed"]},
        {"id": "q2", "text": "Form factor?",
         "options": ["Over-ear", "On-ear", "In-ear", "Earbuds"]},
        {"id": "q3", "text": "Noise canceling?",
         "options": ["Essential", "Nice-to-have", "Not needed"]},
        {"id": "q4", "text": "Budget range?",
         "options": ["<$50", "$50-150", "$150-300", "$300+"]},
        {"id": "q5", "text": "Wired or wireless?",
         "options": ["Wireless only", "Wired only", "Either"]}
    ],
    "laptops": [
        {"id": "q1", "text": "Primary use?",
         "options": ["Work", "Gaming", "Creative", "General"]},
        {"id": "q2", "text": "Screen size?",
         "options": ["13-14in", "15-16in", "17in+"]},
        {"id": "q3", "text": "Portability?",
         "options": ["Ultra-light", "Balanced", "Desktop replacement"]},
        {"id": "q4", "text": "Budget range?",
         "options": ["<$500", "$500-1000", "$1000-2000", "$2000+"]},
        {"id": "q5", "text": "OS preference?",
         "options": ["Windows", "macOS", "Linux", "No preference"]}
    ],
    "shoes": [
        {"id": "q1", "text": "Primary use?",
         "options": ["Running", "Walking", "Training", "Casual", "Dress"]},
        {"id": "q2", "text": "Terrain?",
         "options": ["Road", "Trail", "Gym", "Office"]},
        {"id": "q3", "text": "Foot width?",
         "options": ["Narrow", "Standard", "Wide", "Not sure"]},
        {"id": "q4", "text": "Budget range?",
         "options": ["<$75", "$75-125", "$125-200", "$200+"]},
        {"id": "q5", "text": "Waterproof?",
         "options": ["Essential", "Nice-to-have", "Not needed"]}
    ],
    "default": [
        {"id": "q1", "text": "What matters most?",
         "options": ["Price", "Quality", "Features", "Brand"]},
        {"id": "q2", "text": "Budget range?",
         "options": ["Budget", "Mid-range", "Premium", "No limit"]},
        {"id": "q3", "text": "Purchase urgency?",
         "options": ["ASAP", "This week", "This month", "Researching"]}
    ]
}


def generateQuiz(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate quiz questions for a product category."""
    cat = params.get("category", "").lower()
    qs = QUIZ_TEMPLATES.get(cat, QUIZ_TEMPLATES["default"])
    return {
        "questions": qs,
        "idx": 0,
        "question_count": len(qs),
        "has_category": True,
        "quiz_complete": False,
        "is_last_question": len(qs) <= 1,
        "error": None,
        "has_error": False
    }


def recordAnswer(params: Dict[str, Any]) -> Dict[str, Any]:
    """Record user's answer and advance quiz index."""
    ans = params.get("quiz_answers") or {}
    qid = params.get("question_id", "")
    answer = params.get("answer", "")
    idx = params.get("current_idx", 0)
    qCount = params.get("question_count", 0)

    ans[qid] = answer
    newIdx = idx + 1
    complete = newIdx >= qCount
    isLast = newIdx >= qCount - 1

    return {
        "answers": ans,
        "idx": newIdx,
        "quiz_complete": complete,
        "is_last_question": isLast
    }


def extractPreferences(params: Dict[str, Any]) -> Dict[str, Any]:
    """Extract preferences from quiz answers."""
    qs = params.get("quiz_questions") or []
    ans = params.get("quiz_answers") or {}

    prefs = {}
    for q in qs:
        qid = q.get("id", "")
        if qid in ans:
            key = q.get("text", "").lower().replace("?", "").replace(" ", "_")
            prefs[key] = ans[qid]

    prefs["price_weight"] = 0.3
    prefs["quality_weight"] = 0.3
    prefs["features_weight"] = 0.2
    prefs["reviews_weight"] = 0.2

    budget = ans.get("q4", "")
    if "<$" in budget or "Budget" in budget:
        prefs["price_weight"] = 0.5
        prefs["quality_weight"] = 0.2

    return {"preferences": prefs}


# =========================================================================
# PRODUCT FETCHING
# =========================================================================

SKIP_DOMAINS = [
    "stackexchange.com", "stackoverflow.com", "wikipedia.org",
    "dictionary.com", "merriam-webster.com", "wiktionary.org",
    "thesaurus.com", "vocabulary.com", "yourdictionary.com",
    "grammarly.com/blog", "quora.com", "jlaforums.com",
    "craigslist.org", "kijiji.ca", "gumtree.com", "offerup.com",
    "letgo.com", "mercari.com", "poshmark.com", "pinterest.com",
    "facebook.com", "twitter.com", "instagram.com", "tiktok.com",
    "linkedin.com"
]

SKIP_TITLES = [
    "vs. \"", "vs \"", "versus", "grammar", "english language",
    "articles -", "usage -", "word choice", "phrase meaning",
    "what is the difference", "which is correct", "for sale -",
    "jla forums", "recent posts", "page "
]

UA = ("Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
      "AppleWebKit/537.36 (KHTML, like Gecko) "
      "Chrome/120.0.0.0 Safari/537.36")


def _ddgSearch(query: str, n: int = 10, retries: int = 2) -> List[Dict]:
    """DuckDuckGo search. Hermetic: query -> results list."""
    results = []

    if HAS_DDGS:
        for attempt in range(retries):
            try:
                with DDGS(timeout=10) as ddgs:
                    for r in ddgs.text(query, max_results=n):
                        results.append({
                            "title": r.get("title", ""),
                            "url": r.get("href", ""),
                            "snippet": r.get("body", "")
                        })
                if results:
                    return results
                if attempt < retries - 1:
                    time.sleep(0.5)
            except Exception:
                if attempt < retries - 1:
                    time.sleep(1)

    if not HAS_REQUESTS:
        return results

    try:
        url = f"https://html.duckduckgo.com/html/?q="
        url += requests.utils.quote(query)
        resp = requests.get(url, headers={"User-Agent": UA}, timeout=8)
        resp.raise_for_status()

        if HAS_BS4:
            soup = BeautifulSoup(resp.text, "html.parser")
            for r in soup.select(".result")[:n]:
                titleEl = r.select_one(".result__title")
                snippetEl = r.select_one(".result__snippet")
                aTag = r.select_one("a.result__a")
                href = ""
                if aTag:
                    href = aTag.get("href", "")
                    if "uddg=" in href:
                        m = re.search(r'uddg=([^&]+)', href)
                        if m:
                            import urllib.parse
                            href = urllib.parse.unquote(m.group(1))
                title = titleEl.get_text(strip=True) if titleEl else ""
                snip = snippetEl.get_text(strip=True) if snippetEl else ""
                if title and href:
                    results.append({
                        "title": title, "url": href, "snippet": snip
                    })
    except Exception:
        pass

    return results


def _webSearch(query: str, n: int = 10) -> List[Dict]:
    """Web search with fallback. Hermetic: query -> results list."""
    results = _ddgSearch(query, n)
    if results:
        return results

    if not HAS_REQUESTS:
        return []

    try:
        url = f"https://www.google.com/search?q="
        url += f"{requests.utils.quote(query)}&num={n}"
        resp = requests.get(url, headers={"User-Agent": UA}, timeout=10)
        resp.raise_for_status()

        if HAS_BS4:
            soup = BeautifulSoup(resp.text, "html.parser")
            for g in soup.select("div.g")[:n]:
                titleEl = g.select_one("h3")
                linkEl = g.select_one("a")
                snippetEl = g.select_one("div.VwiC3b")
                if titleEl and linkEl:
                    href = linkEl.get("href", "")
                    snip = snippetEl.get_text(strip=True) if snippetEl else ""
                    results.append({
                        "title": titleEl.get_text(strip=True),
                        "url": href,
                        "snippet": snip
                    })
    except Exception:
        pass

    return results


def _parsePrice(text: str) -> float:
    """Extract price from text."""
    m = re.search(r'\$[\d,]+\.?\d*', text)
    if m:
        s = m.group().replace('$', '').replace(',', '')
        try:
            return float(s)
        except ValueError:
            pass
    return 0.0


def _extractRating(text: str) -> float:
    """Extract rating from text."""
    m = re.search(r'(\d\.?\d?)\s*(?:out of|/)\s*5', text.lower())
    if m:
        try:
            return float(m.group(1))
        except ValueError:
            pass
    m = re.search(r'(\d\.?\d?)\s*stars?', text.lower())
    if m:
        try:
            return float(m.group(1))
        except ValueError:
            pass
    return 4.0


def _buildQuery(cat: str, prefs: Dict) -> str:
    """Build search query from category and preferences."""
    terms = [f"best {cat} to buy 2025"]
    budget = prefs.get("budget_range", "")
    if budget:
        bl = budget.lower()
        if "budget" in bl or "<$" in budget:
            terms.append("under $100 affordable")
        elif "premium" in bl or "$200" in budget or "no limit" in bl:
            terms.append("premium high-end")
        elif "mid" in bl:
            terms.append("$50-150")
    terms.append("product review buying guide")
    return " ".join(terms[:8])


def _filterResults(results: List[Dict], limit: int) -> List[Dict]:
    """Filter out non-product results."""
    filtered = []
    for r in results:
        urlLow = r["url"].lower()
        titleLow = r["title"].lower()
        if any(d in urlLow for d in SKIP_DOMAINS):
            continue
        if any(p in titleLow for p in SKIP_TITLES):
            continue
        filtered.append(r)
    return filtered[:limit]


def fetchProducts(params: Dict[str, Any]) -> Dict[str, Any]:
    """Fetch products via web search. Hermetic: params -> result."""
    cat = params.get("category", "").lower()
    prefs = params.get("preferences") or {}
    offset = params.get("fetch_offset") or 0
    limit = params.get("fetch_limit") or 10
    existing = params.get("existing_products") or []
    existingLinks = params.get("existing_affiliate_links") or {}

    if not cat:
        return {
            "products": existing,
            "affiliate_links": existingLinks,
            "has_products": len(existing) > 0,
            "fetch_offset": offset,
            "fetch_total": len(existing),
            "has_more_products": False,
            "has_error": True,
            "error": "No category specified"
        }

    query = _buildQuery(cat, prefs)
    if offset > 0:
        query += f" page {(offset // limit) + 1}"

    results = _webSearch(query, n=limit)

    if not results or len(results) < 3:
        altQs = [
            f"best {cat} 2025 amazon reviews",
            f"{cat} buyer's guide top picks 2025",
        ]
        for aq in altQs[:2]:
            newRes = _webSearch(aq, n=limit)
            if newRes:
                urls = {r["url"] for r in results}
                for r in newRes:
                    if r["url"] not in urls:
                        results.append(r)
                        urls.add(r["url"])
                if len(results) >= limit:
                    break

    results = _filterResults(results, limit)

    batch = []
    for i, sr in enumerate(results):
        pid = hashlib.md5(sr["url"].encode()).hexdigest()[:8]
        title = sr["title"]
        snippet = sr["snippet"]
        price = _parsePrice(snippet) or _parsePrice(title)
        rating = _extractRating(snippet)
        name = re.sub(
            r'\s*[-|]\s*(Amazon|eBay|Walmart|Best Buy|Target).*$',
            '', title, flags=re.I
        )
        name = name[:60]
        batch.append({
            "id": f"g_{pid}_{offset + i}",
            "name": name or f"{cat.title()} Product {offset + i + 1}",
            "brand": "Various",
            "price": price if price > 0 else 99.99,
            "rating": rating,
            "review_count": 100,
            "features": [cat, "Search Result"],
            "url": sr["url"],
            "snippet": snippet[:200],
            "in_stock": True,
            "source": "Web Search"
        })

    products = existing + batch
    links = dict(existingLinks)
    for p in batch:
        links[p["id"]] = p.get("url", "")

    newOffset = offset + len(batch)
    hasMore = len(batch) >= limit and newOffset < 50

    return {
        "products": products,
        "affiliate_links": links,
        "has_products": len(products) > 0,
        "fetch_offset": newOffset,
        "fetch_total": newOffset + (limit if hasMore else 0),
        "has_more_products": hasMore,
        "has_error": False,
        "error": None
    }


# =========================================================================
# REVIEW AGGREGATION
# =========================================================================

POS_WORDS = [
    "best", "great", "excellent", "comfortable", "durable",
    "fast", "lightweight", "responsive", "stable", "cushioned"
]
NEG_WORDS = ["heavy", "expensive", "narrow", "stiff", "uncomfortable"]


def aggregateReviews(params: Dict[str, Any]) -> Dict[str, Any]:
    """Aggregate review insights from snippets. Hermetic: params -> result."""
    products = params.get("products") or []
    reviews = {}

    for p in products:
        pid = p.get("id", "")
        snippet = p.get("snippet", "")
        url = p.get("url", "")
        textLow = snippet.lower()

        pros = []
        cons = []
        for w in POS_WORDS:
            if w in textLow and len(pros) < 3:
                pros.append(w.capitalize())
        for w in NEG_WORDS:
            if w in textLow and len(cons) < 3:
                cons.append(w.capitalize())

        sources = []
        m = re.search(r'https?://(?:www\.)?([^/]+)', url)
        if m:
            sources.append(m.group(1))

        reviews[pid] = {
            "volume": 100,
            "recency": datetime.now().strftime("%Y-%m"),
            "avg_rating": _extractRating(snippet),
            "pros": pros if pros else ["See full review"],
            "cons": cons if cons else ["See full review"],
            "topics": {},
            "sources": sources
        }

    return {"reviews": reviews, "has_error": False, "error": None}


# =========================================================================
# RANKING
# =========================================================================

def _parseBudget(budget: str) -> float:
    """Parse budget string to max price."""
    if "$300+" in budget or "Premium" in budget or "No limit" in budget:
        return 500.0
    if "$150-300" in budget:
        return 300.0
    if "$50-150" in budget or "Mid-range" in budget:
        return 150.0
    if "<$50" in budget or "Budget" in budget:
        return 50.0
    return 200.0


def rankProducts(params: Dict[str, Any]) -> Dict[str, Any]:
    """Rank products with transparent scoring. Hermetic: params -> result."""
    products = params.get("products") or []
    prefs = params.get("preferences") or {}
    reviews = params.get("reviews") or {}

    pw = prefs.get("price_weight", 0.3)
    qw = prefs.get("quality_weight", 0.3)
    fw = prefs.get("features_weight", 0.2)
    rw = prefs.get("reviews_weight", 0.2)
    budget = prefs.get("budget_range", "$50-150")
    maxPrice = _parseBudget(budget)

    rankings = []
    for p in products:
        pid = p["id"]
        rv = reviews.get(pid, {})

        priceScore = max(0, 1 - (p["price"] / maxPrice)
                         ) if maxPrice > 0 else 0.5
        qualScore = p.get("rating", 0) / 5.0
        featScore = min(1.0, len(p.get("features", [])) / 5.0)
        revScore = min(1.0, rv.get("volume", 0) / 5000)
        revScore *= rv.get("avg_rating", 0) / 5.0

        total = pw * priceScore + qw * qualScore + fw * featScore + rw * revScore

        reasons = []
        if priceScore > 0.7:
            reasons.append(f"Good value at ${p['price']:.0f}")
        if qualScore > 0.85:
            reasons.append(f"Highly rated ({p['rating']}/5)")
        if rv.get("volume", 0) > 1000:
            reasons.append(f"Well-reviewed ({rv['volume']} reviews)")
        if p.get("in_stock"):
            reasons.append("In stock")
        else:
            reasons.append("Currently unavailable")
            total *= 0.8

        formPref = prefs.get("form_factor", "")
        if formPref and formPref.lower() in p.get("form", "").lower():
            reasons.append(f"Matches your {formPref} preference")
            total *= 1.15

        wirePref = prefs.get("wired_or_wireless", "")
        if "wireless" in wirePref.lower() and p.get("wireless"):
            reasons.append("Wireless as preferred")
            total *= 1.1
        elif "wired" in wirePref.lower() and not p.get("wireless"):
            reasons.append("Wired as preferred")
            total *= 1.1

        rankings.append({
            "product_id": pid,
            "product_name": p["name"],
            "score": round(total, 3),
            "price": p["price"],
            "rating": p["rating"],
            "reasons": reasons,
            "breakdown": {
                "price": round(priceScore, 2),
                "quality": round(qualScore, 2),
                "features": round(featScore, 2),
                "reviews": round(revScore, 2)
            }
        })

    rankings.sort(key=lambda x: x["score"], reverse=True)

    return {
        "rankings": rankings,
        "has_rankings": len(rankings) > 0,
        "has_error": False,
        "error": None
    }


# =========================================================================
# COMPARISON
# =========================================================================

def _bestFor(prod: dict, rev: dict) -> str:
    """Determine best use case for product."""
    topics = rev.get("topics", {})
    if not topics:
        return "General use"
    top = max(topics.items(), key=lambda x: x[1])[0]
    return top.replace("_", " ").title()


def _determineWinners(prods: list) -> dict:
    """Determine best product per dimension."""
    winners = {}
    if len(prods) < 2:
        return winners

    prices = [
        (p["id"], float(p["values"]["Price"].replace("$", "")))
        for p in prods
    ]
    winners["Price"] = min(prices, key=lambda x: x[1])[0]

    ratings = [
        (p["id"], float(p["values"]["Rating"].split("/")[0]))
        for p in prods
    ]
    winners["Rating"] = max(ratings, key=lambda x: x[1])[0]

    return winners


def compareProducts(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate side-by-side comparison. Hermetic: params -> result."""
    pids = params.get("product_ids", [])
    products = params.get("products", [])
    reviews = params.get("reviews", {})

    selected = [p for p in products if p["id"] in pids]
    if len(selected) < 2:
        return {"comparison": {"error": "Need at least 2 products"}}

    dims = ["Price", "Rating", "Features", "Pros", "Cons", "Best for"]
    comparison = {"products": [], "dimensions": dims}

    for p in selected:
        pid = p["id"]
        rv = reviews.get(pid, {})
        comparison["products"].append({
            "id": pid,
            "name": p["name"],
            "values": {
                "Price": f"${p['price']:.2f}",
                "Rating": f"{p['rating']}/5 ({rv.get('volume', 0)} reviews)",
                "Features": ", ".join(p.get("features", [])[:3]),
                "Pros": ", ".join(rv.get("pros", [])[:2]),
                "Cons": ", ".join(rv.get("cons", [])[:2]),
                "Best for": _bestFor(p, rv)
            }
        })

    comparison["winners"] = _determineWinners(comparison["products"])
    return {"comparison": comparison}


# =========================================================================
# ALERTS
# =========================================================================

def addAlert(params: Dict[str, Any]) -> Dict[str, Any]:
    """Add price or restock alert. Hermetic: params -> result."""
    alerts = params.get("alerts") or []
    pid = params.get("product_id", "")
    atype = params.get("alert_type", "price")

    alerts.append({
        "product_id": pid,
        "type": atype,
        "created": datetime.now().isoformat(),
        "active": True
    })

    return {"alerts": alerts}


# =========================================================================
# RESET
# =========================================================================

def reset(params: Dict[str, Any]) -> Dict[str, Any]:
    """Reset all state. Hermetic: params -> result."""
    return {
        "category": None,
        "quiz_questions": None,
        "quiz_answers": None,
        "preferences": None,
        "products": None,
        "reviews": None,
        "rankings": None,
        "comparison": None,
        "selected_product": None,
        "alerts": [],
        "current_question_idx": 0,
        "quiz_question_count": 0,
        "has_category": False,
        "quiz_complete": False,
        "is_last_question": False,
        "has_products": False,
        "has_rankings": False,
        "has_selection": False,
        "has_error": False,
        "fetch_offset": 0,
        "fetch_total": 0,
        "has_more_products": False
    }


# =========================================================================
# REGISTRY
# =========================================================================

COMPUTE_REGISTRY = {
    "shop:generate_quiz": generateQuiz,
    "shop:record_answer": recordAnswer,
    "shop:extract_preferences": extractPreferences,
    "shop:fetch_products": fetchProducts,
    "shop:aggregate_reviews": aggregateReviews,
    "shop:rank_products": rankProducts,
    "shop:compare_products": compareProducts,
    "shop:add_alert": addAlert,
    "shop:reset": reset,
}
