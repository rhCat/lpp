"""
COMPUTE units for Discovery Shopping

Hermetic functions for quiz generation, product fetching, review
aggregation, and explainable ranking.
Input: params dict. Output: result dict.
"""

import time
import json
import re
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

# Try new ddgs package first, fall back to old duckduckgo_search
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
        {"id": "q1", "text": "Primary use?", "options": [
            "Music", "Gaming", "Calls", "Mixed"]},
        {"id": "q2", "text": "Form factor?", "options": [
            "Over-ear", "On-ear", "In-ear", "Earbuds"]},
        {"id": "q3", "text": "Noise canceling?", "options": [
            "Essential", "Nice-to-have", "Not needed"]},
        {"id": "q4", "text": "Budget range?", "options": [
            "<$50", "$50-150", "$150-300", "$300+"]},
        {"id": "q5", "text": "Wired or wireless?", "options": [
            "Wireless only", "Wired only", "Either"]}
    ],
    "laptops": [
        {"id": "q1", "text": "Primary use?", "options": [
            "Work", "Gaming", "Creative", "General"]},
        {"id": "q2", "text": "Screen size?",
            "options": ["13-14in", "15-16in", "17in+"]},
        {"id": "q3", "text": "Portability?", "options": [
            "Ultra-light", "Balanced", "Desktop replacement"]},
        {"id": "q4", "text": "Budget range?", "options": [
            "<$500", "$500-1000", "$1000-2000", "$2000+"]},
        {"id": "q5", "text": "OS preference?", "options": [
            "Windows", "macOS", "Linux", "No preference"]}
    ],
    "shoes": [
        {"id": "q1", "text": "Primary use?", "options": [
            "Running", "Walking", "Training", "Casual", "Dress"]},
        {"id": "q2", "text": "Terrain?", "options": [
            "Road", "Trail", "Gym", "Office"]},
        {"id": "q3", "text": "Foot width?", "options": [
            "Narrow", "Standard", "Wide", "Not sure"]},
        {"id": "q4", "text": "Budget range?", "options": [
            "<$75", "$75-125", "$125-200", "$200+"]},
        {"id": "q5", "text": "Waterproof?", "options": [
            "Essential", "Nice-to-have", "Not needed"]}
    ],
    "default": [
        {"id": "q1", "text": "What matters most?", "options": [
            "Price", "Quality", "Features", "Brand"]},
        {"id": "q2", "text": "Budget range?", "options": [
            "Budget", "Mid-range", "Premium", "No limit"]},
        {"id": "q3", "text": "Purchase urgency?", "options": [
            "ASAP", "This week", "This month", "Researching"]}
    ]
}


def generate_quiz(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate quiz questions for a product category."""
    category = params.get("category", "").lower()
    questions = QUIZ_TEMPLATES.get(category, QUIZ_TEMPLATES["default"])
    return {
        "questions": questions,
        "idx": 0,
        "question_count": len(questions),
        "has_category": True,
        "quiz_complete": False,
        "is_last_question": len(questions) <= 1,  # True if only 1 question
        "error": None,
        "has_error": False
    }


def record_answer(params: Dict[str, Any]) -> Dict[str, Any]:
    """Record user's answer and advance quiz index."""
    answers = params.get("quiz_answers") or {}
    qid = params.get("question_id", "")
    answer = params.get("answer", "")
    idx = params.get("current_idx", 0)
    question_count = params.get("question_count", 0)

    answers[qid] = answer
    new_idx = idx + 1
    quiz_complete = new_idx >= question_count
    # is_last_question = True when we're about to answer the last one
    # (for next ANSWER event)
    is_last_question = (new_idx >= question_count - 1)

    return {
        "answers": answers,
        "idx": new_idx,
        "quiz_complete": quiz_complete,
        "is_last_question": is_last_question
    }


def extract_preferences(params: Dict[str, Any]) -> Dict[str, Any]:
    """Extract preferences from quiz answers."""
    questions = params.get("quiz_questions") or []
    answers = params.get("quiz_answers") or {}

    prefs = {}
    for q in questions:
        qid = q.get("id", "")
        if qid in answers:
            # Map question text to preference key
            key = q.get("text", "").lower().replace("?", "").replace(" ", "_")
            prefs[key] = answers[qid]

    # Add default weights
    prefs["price_weight"] = 0.3
    prefs["quality_weight"] = 0.3
    prefs["features_weight"] = 0.2
    prefs["reviews_weight"] = 0.2

    # Adjust weights based on budget answer if present
    budget = answers.get("q4", "")
    if "<$" in budget or "Budget" in budget:
        prefs["price_weight"] = 0.5
        prefs["quality_weight"] = 0.2

    return {"preferences": prefs}


# =========================================================================
# PRODUCT FETCHING (Real Web Search)
# =========================================================================


def _duckduckgo_search(query: str, num_results: int = 10, retries: int = 3) -> List[Dict]:
    """Perform DuckDuckGo search using the duckduckgo_search library.

    Hermetic: takes query string, returns list of result dicts.
    Includes retry logic for rate limiting.
    """
    results = []

    # Try the duckduckgo_search library with retries
    if HAS_DDGS:
        for attempt in range(retries):
            try:
                with DDGS() as ddgs:
                    for r in ddgs.text(query, max_results=num_results):
                        results.append({
                            "title": r.get("title", ""),
                            "url": r.get("href", ""),
                            "snippet": r.get("body", "")
                        })
                if results:
                    return results
                # If no results, wait and retry
                if attempt < retries - 1:
                    time.sleep(1 + attempt)  # Increasing delay
            except Exception as e:
                print(f"[DDGS Attempt {attempt+1}] {e}")
                if attempt < retries - 1:
                    time.sleep(2 + attempt * 2)  # Longer delay on error

    # Fallback: try HTML scraping (less reliable)
    if not HAS_REQUESTS:
        return results

    headers = {
        "User-Agent": "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
                      "AppleWebKit/537.36 (KHTML, like Gecko) "
                      "Chrome/120.0.0.0 Safari/537.36"
    }

    results = []
    try:
        # Use DuckDuckGo HTML version
        url = f"https://html.duckduckgo.com/html/?q={requests.utils.quote(query)}"
        resp = requests.get(url, headers=headers, timeout=15)
        resp.raise_for_status()

        if HAS_BS4:
            soup = BeautifulSoup(resp.text, "html.parser")
            # DuckDuckGo HTML results are in .result class
            for result in soup.select(".result")[:num_results]:
                title_el = result.select_one(".result__title")
                link_el = result.select_one(".result__url")
                snippet_el = result.select_one(".result__snippet")

                # Get actual URL from link
                a_tag = result.select_one("a.result__a")
                href = ""
                if a_tag:
                    href = a_tag.get("href", "")
                    # DuckDuckGo wraps URLs, extract the actual URL
                    if "uddg=" in href:
                        match = re.search(r'uddg=([^&]+)', href)
                        if match:
                            import urllib.parse
                            href = urllib.parse.unquote(match.group(1))

                title = title_el.get_text(strip=True) if title_el else ""
                snippet = snippet_el.get_text(strip=True) if snippet_el else ""

                if title and href:
                    results.append({
                        "title": title,
                        "url": href,
                        "snippet": snippet
                    })
    except Exception as e:
        print(f"[Search Error] {e}")

    return results


def _google_search(query: str, num_results: int = 10) -> List[Dict]:
    """Perform search and extract product-like results.

    Hermetic: takes query string, returns list of result dicts.
    Tries DuckDuckGo first (more reliable), falls back to Google.
    """
    # Try DuckDuckGo first
    results = _duckduckgo_search(query, num_results)
    if results:
        return results

    # Fallback to Google (may be blocked)
    if not HAS_REQUESTS:
        return []

    headers = {
        "User-Agent": "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
                      "AppleWebKit/537.36 (KHTML, like Gecko) "
                      "Chrome/120.0.0.0 Safari/537.36"
    }

    try:
        url = f"https://www.google.com/search?q={requests.utils.quote(query)}&num={num_results}"
        resp = requests.get(url, headers=headers, timeout=10)
        resp.raise_for_status()

        if HAS_BS4:
            soup = BeautifulSoup(resp.text, "html.parser")
            for g in soup.select("div.g")[:num_results]:
                title_el = g.select_one("h3")
                link_el = g.select_one("a")
                snippet_el = g.select_one("div.VwiC3b")

                if title_el and link_el:
                    href = link_el.get("href", "")
                    results.append({
                        "title": title_el.get_text(strip=True),
                        "url": href,
                        "snippet": snippet_el.get_text(strip=True) if snippet_el else ""
                    })
    except Exception:
        pass

    return results


def _parse_price(text: str) -> float:
    """Extract price from text string."""
    match = re.search(r'\$[\d,]+\.?\d*', text)
    if match:
        price_str = match.group().replace('$', '').replace(',', '')
        try:
            return float(price_str)
        except ValueError:
            pass
    return 0.0


def _extract_rating(text: str) -> float:
    """Extract rating from text (e.g., '4.5 out of 5')."""
    match = re.search(r'(\d\.?\d?)\s*(?:out of|/)\s*5', text.lower())
    if match:
        try:
            return float(match.group(1))
        except ValueError:
            pass
    match = re.search(r'(\d\.?\d?)\s*stars?', text.lower())
    if match:
        try:
            return float(match.group(1))
        except ValueError:
            pass
    return 4.0  # Default rating


def _build_search_query(category: str, prefs: Dict) -> str:
    """Build search query from category and preferences."""
    terms = [f"best {category}"]

    # Add preference-based terms
    for key, val in prefs.items():
        if isinstance(val, str) and val and key not in ("price_weight", "quality_weight"):
            if "budget" in key.lower():
                terms.append(val)
            elif val.lower() not in ("not needed", "not sure", "no preference"):
                terms.append(val)

    terms.append("buy")
    return " ".join(terms[:6])  # Limit query length


def fetch_products(params: Dict[str, Any]) -> Dict[str, Any]:
    """Fetch products via Google Search.

    Hermetic: input params dict, output result dict.
    Uses real search to find products matching category and preferences.
    """
    category = params.get("category", "").lower()
    prefs = params.get("preferences") or {}

    # Pagination params
    offset = params.get("fetch_offset") or 0
    limit = params.get("fetch_limit") or 10
    existing = params.get("existing_products") or []
    existing_links = params.get("existing_affiliate_links") or {}

    if not category:
        return {
            "products": existing,
            "affiliate_links": existing_links,
            "has_products": len(existing) > 0,
            "fetch_offset": offset,
            "fetch_total": len(existing),
            "has_more_products": False,
            "has_error": True,
            "error": "No category specified"
        }

    # Build search query
    query = _build_search_query(category, prefs)

    # For pagination, modify query
    if offset > 0:
        query += f" page {(offset // limit) + 1}"

    # Perform search with multiple query variations
    search_results = _google_search(query, num_results=limit)

    # Try alternative queries if no results
    if not search_results:
        alt_queries = [
            f"best {category} to buy 2025",
            f"{category} reviews recommendations",
            f"top rated {category} buy online",
            f"{category} shopping guide"
        ]
        for alt_q in alt_queries:
            search_results = _google_search(alt_q, num_results=limit)
            if search_results:
                break
            time.sleep(0.5)  # Brief delay between attempts

    # Convert search results to product format
    batch = []
    for i, sr in enumerate(search_results):
        pid = hashlib.md5(sr["url"].encode()).hexdigest()[:8]

        # Extract product info from title/snippet
        title = sr["title"]
        snippet = sr["snippet"]

        # Try to extract price and rating from snippet
        price = _parse_price(snippet) or _parse_price(title)
        rating = _extract_rating(snippet)

        # Clean up title (remove site names)
        name = re.sub(
            r'\s*[-|]\s*(Amazon|eBay|Walmart|Best Buy|Target).*$', '', title, flags=re.I)
        name = name[:60]  # Truncate long names

        product = {
            "id": f"g_{pid}_{offset + i}",
            "name": name or f"{category.title()} Product {offset + i + 1}",
            "brand": "Various",
            "price": price if price > 0 else 99.99,
            "rating": rating,
            "review_count": 100,  # Unknown from search
            "features": [category, "Search Result"],
            "url": sr["url"],
            "snippet": snippet[:200],
            "in_stock": True,
            "source": "Web Search"
        }
        batch.append(product)

    # Merge with existing
    products = existing + batch

    # Generate affiliate links (placeholder)
    links = dict(existing_links)
    for p in batch:
        original_url = p.get("url", "")
        # In production, would use proper affiliate link generation
        links[p["id"]] = original_url

    new_offset = offset + len(batch)
    # Estimate more results available if we got a full batch
    has_more = len(batch) >= limit and new_offset < 50

    return {
        "products": products,
        "affiliate_links": links,
        "has_products": len(products) > 0,
        "fetch_offset": new_offset,
        "fetch_total": new_offset + (limit if has_more else 0),
        "has_more_products": has_more,
        "has_error": False,
        "error": None
    }


# =========================================================================
# REVIEW AGGREGATION (Real Web Search)
# =========================================================================


def _search_reviews(product_name: str) -> Dict:
    """Search for product reviews via Google.

    Hermetic: takes product name, returns review summary dict.
    """
    if not HAS_REQUESTS or not product_name:
        return _default_review()

    query = f"{product_name} review pros cons"
    results = _google_search(query, num_results=5)

    if not results:
        return _default_review()

    # Aggregate info from search snippets
    all_text = " ".join(r.get("snippet", "") for r in results)
    sources = []

    for r in results:
        url = r.get("url", "")
        if "amazon" in url.lower():
            sources.append("Amazon")
        elif "reddit" in url.lower():
            sources.append("Reddit")
        elif "youtube" in url.lower():
            sources.append("YouTube")
        elif "wirecutter" in url.lower():
            sources.append("Wirecutter")
        else:
            # Extract domain
            match = re.search(r'https?://(?:www\.)?([^/]+)', url)
            if match:
                sources.append(match.group(1)[:20])

    # Extract potential pros (positive words near "pro" or positive sentiment)
    pros = []
    cons = []

    # Simple keyword extraction
    pos_words = ["great", "excellent", "good", "best", "comfortable", "quality",
                 "durable", "fast", "easy", "value", "reliable", "sturdy"]
    neg_words = ["bad", "poor", "cheap", "slow", "uncomfortable", "fragile",
                 "expensive", "loud", "heavy", "complicated", "unreliable"]

    text_lower = all_text.lower()
    for word in pos_words:
        if word in text_lower and len(pros) < 3:
            pros.append(word.capitalize())
    for word in neg_words:
        if word in text_lower and len(cons) < 3:
            cons.append(word.capitalize())

    # Extract rating if found
    rating = _extract_rating(all_text)

    return {
        "volume": len(results) * 100,
        "recency": datetime.now().strftime("%Y-%m"),
        "avg_rating": rating,
        "pros": pros if pros else ["See reviews"],
        "cons": cons if cons else ["See reviews"],
        "topics": {},
        "sources": list(set(sources))[:5]
    }


def _default_review() -> Dict:
    """Return default review structure."""
    return {
        "volume": 0,
        "recency": "N/A",
        "avg_rating": 0,
        "pros": [],
        "cons": [],
        "topics": {},
        "sources": []
    }


def aggregate_reviews(params: Dict[str, Any]) -> Dict[str, Any]:
    """Aggregate review insights from search snippets.

    Hermetic: input params dict, output result dict.
    Extracts review insights from product snippets (already fetched).
    """
    products = params.get("products") or []

    reviews = {}
    for p in products:
        pid = p.get("id", "")
        name = p.get("name", "")
        snippet = p.get("snippet", "")
        url = p.get("url", "")

        # Extract insights from existing snippet instead of new search
        # This is much faster and doesn't hit rate limits
        pros = []
        cons = []

        text_lower = snippet.lower()
        pos_words = ["best", "great", "excellent", "comfortable", "durable",
                     "fast", "lightweight", "responsive", "stable", "cushioned"]
        neg_words = ["heavy", "expensive", "narrow", "stiff", "uncomfortable"]

        for word in pos_words:
            if word in text_lower and len(pros) < 3:
                pros.append(word.capitalize())
        for word in neg_words:
            if word in text_lower and len(cons) < 3:
                cons.append(word.capitalize())

        # Extract source domain
        sources = []
        match = re.search(r'https?://(?:www\.)?([^/]+)', url)
        if match:
            sources.append(match.group(1))

        reviews[pid] = {
            "volume": 100,  # Estimated
            "recency": datetime.now().strftime("%Y-%m"),
            "avg_rating": _extract_rating(snippet),
            "pros": pros if pros else ["See full review"],
            "cons": cons if cons else ["See full review"],
            "topics": {},
            "sources": sources
        }

    return {"reviews": reviews, "has_error": False, "error": None}


# =========================================================================
# RANKING WITH EXPLAINABILITY
# =========================================================================

def rank_products(params: Dict[str, Any]) -> Dict[str, Any]:
    """Rank products with transparent scoring and explanations."""
    products = params.get("products") or []
    prefs = params.get("preferences") or {}
    reviews = params.get("reviews") or {}

    pw = prefs.get("price_weight", 0.3)
    qw = prefs.get("quality_weight", 0.3)
    fw = prefs.get("features_weight", 0.2)
    rw = prefs.get("reviews_weight", 0.2)

    # Extract budget range
    budget = prefs.get("budget_range", "$50-150")
    max_price = _parse_budget(budget)

    rankings = []
    for p in products:
        pid = p["id"]
        rv = reviews.get(pid, {})

        # Calculate component scores (0-1)
        price_score = max(
            0, 1 - (p["price"] / max_price)) if max_price > 0 else 0.5
        quality_score = p.get("rating", 0) / 5.0
        feature_score = min(1.0, len(p.get("features", [])) / 5.0)
        review_score = min(1.0, rv.get("volume", 0) / 5000) * \
            rv.get("avg_rating", 0) / 5.0

        # Weighted total
        total = (pw * price_score + qw * quality_score +
                 fw * feature_score + rw * review_score)

        # Build explanation
        reasons = []
        if price_score > 0.7:
            reasons.append(f"Good value at ${p['price']:.0f}")
        if quality_score > 0.85:
            reasons.append(f"Highly rated ({p['rating']}/5)")
        if rv.get("volume", 0) > 1000:
            reasons.append(f"Well-reviewed ({rv['volume']} reviews)")
        if p.get("in_stock"):
            reasons.append("In stock")
        else:
            reasons.append("Currently unavailable")
            total *= 0.8  # Penalize out-of-stock

        # Add preference-specific matches
        form_pref = prefs.get("form_factor", "")
        if form_pref and form_pref.lower() in p.get("form", "").lower():
            reasons.append(f"Matches your {form_pref} preference")
            total *= 1.15  # Boost for matching form factor

        # Check wireless preference
        wireless_pref = prefs.get("wired_or_wireless", "")
        if "wireless" in wireless_pref.lower() and p.get("wireless"):
            reasons.append("Wireless as preferred")
            total *= 1.1
        elif "wired" in wireless_pref.lower() and not p.get("wireless"):
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
                "price": round(price_score, 2),
                "quality": round(quality_score, 2),
                "features": round(feature_score, 2),
                "reviews": round(review_score, 2)
            }
        })

    # Sort by score descending
    rankings.sort(key=lambda x: x["score"], reverse=True)

    return {
        "rankings": rankings,
        "has_rankings": len(rankings) > 0,
        "has_error": False,
        "error": None
    }


def _parse_budget(budget: str) -> float:
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


# =========================================================================
# COMPARISON
# =========================================================================

def compare_products(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate side-by-side comparison."""
    pids = params.get("product_ids", [])
    products = params.get("products", [])
    reviews = params.get("reviews", {})
    prefs = params.get("preferences", {})

    # Find requested products
    selected = [p for p in products if p["id"] in pids]
    if len(selected) < 2:
        return {"comparison": {"error": "Need at least 2 products"}}

    # Build comparison matrix
    comparison = {
        "products": [],
        "dimensions": ["Price", "Rating", "Features", "Pros", "Cons", "Best for"]
    }

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
                "Best for": _best_for(p, rv)
            }
        })

    # Determine winner per dimension
    comparison["winners"] = _determine_winners(comparison["products"])

    return {"comparison": comparison}


def _best_for(product: dict, reviews: dict) -> str:
    """Determine what use case product is best for."""
    topics = reviews.get("topics", {})
    if not topics:
        return "General use"
    top_topic = max(topics.items(), key=lambda x: x[1])[0]
    return top_topic.replace("_", " ").title()


def _determine_winners(products: list) -> dict:
    """Determine best product per dimension."""
    winners = {}
    if len(products) < 2:
        return winners

    # Price winner (lowest)
    prices = [(p["id"], float(p["values"]["Price"].replace("$", "")))
              for p in products]
    winners["Price"] = min(prices, key=lambda x: x[1])[0]

    # Rating winner (highest)
    ratings = [(p["id"], float(p["values"]["Rating"].split("/")[0]))
               for p in products]
    winners["Rating"] = max(ratings, key=lambda x: x[1])[0]

    return winners


# =========================================================================
# ALERTS
# =========================================================================

def add_alert(params: Dict[str, Any]) -> Dict[str, Any]:
    """Add price or restock alert."""
    alerts = params.get("alerts") or []
    pid = params.get("product_id", "")
    atype = params.get("alert_type", "price")  # price | restock

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
    """Reset all state."""
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
    "shop:generate_quiz": generate_quiz,
    "shop:record_answer": record_answer,
    "shop:extract_preferences": extract_preferences,
    "shop:fetch_products": fetch_products,
    "shop:aggregate_reviews": aggregate_reviews,
    "shop:rank_products": rank_products,
    "shop:compare_products": compare_products,
    "shop:add_alert": add_alert,
    "shop:reset": reset,
}
