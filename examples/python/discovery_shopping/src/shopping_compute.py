"""
COMPUTE units for Discovery Shopping

Hermetic functions for quiz generation, product fetching, review
aggregation, and explainable ranking.
Input: params dict. Output: result dict.
"""

import json
from typing import Any, Dict, List
from datetime import datetime


# =========================================================================
# QUIZ GENERATION
# =========================================================================

QUIZ_TEMPLATES = {
    "headphones": [
        {"id": "q1", "text": "Primary use?", "options": ["Music", "Gaming", "Calls", "Mixed"]},
        {"id": "q2", "text": "Form factor?", "options": ["Over-ear", "On-ear", "In-ear", "Earbuds"]},
        {"id": "q3", "text": "Noise canceling?", "options": ["Essential", "Nice-to-have", "Not needed"]},
        {"id": "q4", "text": "Budget range?", "options": ["<$50", "$50-150", "$150-300", "$300+"]},
        {"id": "q5", "text": "Wired or wireless?", "options": ["Wireless only", "Wired only", "Either"]}
    ],
    "laptops": [
        {"id": "q1", "text": "Primary use?", "options": ["Work", "Gaming", "Creative", "General"]},
        {"id": "q2", "text": "Screen size?", "options": ["13-14in", "15-16in", "17in+"]},
        {"id": "q3", "text": "Portability?", "options": ["Ultra-light", "Balanced", "Desktop replacement"]},
        {"id": "q4", "text": "Budget range?", "options": ["<$500", "$500-1000", "$1000-2000", "$2000+"]},
        {"id": "q5", "text": "OS preference?", "options": ["Windows", "macOS", "Linux", "No preference"]}
    ],
    "default": [
        {"id": "q1", "text": "What matters most?", "options": ["Price", "Quality", "Features", "Brand"]},
        {"id": "q2", "text": "Budget range?", "options": ["Budget", "Mid-range", "Premium", "No limit"]},
        {"id": "q3", "text": "Purchase urgency?", "options": ["ASAP", "This week", "This month", "Researching"]}
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
# PRODUCT FETCHING (Mock - replace with real API calls)
# =========================================================================

MOCK_PRODUCTS = {
    "headphones": [
        {
            "id": "hp001", "name": "SoundPro X1", "brand": "AudioTech",
            "price": 149.99, "rating": 4.5, "review_count": 1250,
            "features": ["ANC", "40h battery", "Bluetooth 5.2"],
            "form": "Over-ear", "wireless": True, "in_stock": True
        },
        {
            "id": "hp002", "name": "BassMax 300", "brand": "BeatWave",
            "price": 79.99, "rating": 4.2, "review_count": 3420,
            "features": ["Deep bass", "25h battery", "Foldable"],
            "form": "Over-ear", "wireless": True, "in_stock": True
        },
        {
            "id": "hp003", "name": "ClearCall Pro", "brand": "VoiceTech",
            "price": 199.99, "rating": 4.7, "review_count": 890,
            "features": ["ANC", "Mic boom", "USB-C", "Teams certified"],
            "form": "Over-ear", "wireless": True, "in_stock": False
        },
        {
            "id": "hp004", "name": "Budget Buds", "brand": "ValueAudio",
            "price": 29.99, "rating": 3.8, "review_count": 8900,
            "features": ["IPX4", "6h battery", "Touch controls"],
            "form": "Earbuds", "wireless": True, "in_stock": True
        },
        {
            "id": "hp005", "name": "Studio Reference", "brand": "ProSound",
            "price": 349.99, "rating": 4.9, "review_count": 420,
            "features": ["Hi-Res", "Wired", "Replaceable pads"],
            "form": "Over-ear", "wireless": False, "in_stock": True
        }
    ]
}


def fetch_products(params: Dict[str, Any]) -> Dict[str, Any]:
    """Fetch products from feeds/APIs (mock implementation)."""
    category = params.get("category", "").lower()
    prefs = params.get("preferences", {})

    products = MOCK_PRODUCTS.get(category, [])
    if not products:
        return {
            "products": [],
            "affiliate_links": {},
            "has_products": False,
            "has_error": True,
            "error": f"No products for: {category}"
        }

    # Generate affiliate links
    links = {}
    for p in products:
        links[p["id"]] = f"https://shop.example.com/aff/{p['id']}?ref=discovery"

    return {
        "products": products,
        "affiliate_links": links,
        "has_products": True,
        "has_error": False,
        "error": None
    }


# =========================================================================
# REVIEW AGGREGATION
# =========================================================================

MOCK_REVIEWS = {
    "hp001": {
        "volume": 1250, "recency": "2025-12", "avg_rating": 4.5,
        "pros": ["Great ANC", "Comfortable", "Long battery"],
        "cons": ["Bulky", "No wired option"],
        "topics": {"sound": 0.85, "comfort": 0.78, "battery": 0.92},
        "sources": ["Amazon", "BestBuy", "Reddit"]
    },
    "hp002": {
        "volume": 3420, "recency": "2025-12", "avg_rating": 4.2,
        "pros": ["Punchy bass", "Affordable", "Portable"],
        "cons": ["Weak mids", "Plastic build"],
        "topics": {"bass": 0.95, "value": 0.88, "durability": 0.65},
        "sources": ["Amazon", "Walmart"]
    },
    "hp003": {
        "volume": 890, "recency": "2025-11", "avg_rating": 4.7,
        "pros": ["Crystal clear calls", "Premium build", "All-day comfort"],
        "cons": ["Expensive", "Overkill for music"],
        "topics": {"calls": 0.96, "comfort": 0.89, "work": 0.91},
        "sources": ["Amazon", "Microsoft Store"]
    },
    "hp004": {
        "volume": 8900, "recency": "2025-12", "avg_rating": 3.8,
        "pros": ["Unbeatable price", "Decent sound", "Compact"],
        "cons": ["Short battery", "Fit issues", "No ANC"],
        "topics": {"value": 0.94, "convenience": 0.75, "sound": 0.62},
        "sources": ["Amazon", "AliExpress"]
    },
    "hp005": {
        "volume": 420, "recency": "2025-10", "avg_rating": 4.9,
        "pros": ["Audiophile grade", "Flat response", "Build quality"],
        "cons": ["Needs amp", "Not portable", "Pricey"],
        "topics": {"accuracy": 0.98, "build": 0.95, "professional": 0.92},
        "sources": ["Amazon", "Sweetwater", "Head-Fi"]
    }
}


def aggregate_reviews(params: Dict[str, Any]) -> Dict[str, Any]:
    """Aggregate review insights from multiple sources."""
    products = params.get("products", [])

    reviews = {}
    for p in products:
        pid = p.get("id", "")
        reviews[pid] = MOCK_REVIEWS.get(pid, {
            "volume": 0, "recency": "N/A", "avg_rating": 0,
            "pros": [], "cons": [], "topics": {}, "sources": []
        })

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
        price_score = max(0, 1 - (p["price"] / max_price)) if max_price > 0 else 0.5
        quality_score = p.get("rating", 0) / 5.0
        feature_score = min(1.0, len(p.get("features", [])) / 5.0)
        review_score = min(1.0, rv.get("volume", 0) / 5000) * rv.get("avg_rating", 0) / 5.0

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
    prices = [(p["id"], float(p["values"]["Price"].replace("$", ""))) for p in products]
    winners["Price"] = min(prices, key=lambda x: x[1])[0]

    # Rating winner (highest)
    ratings = [(p["id"], float(p["values"]["Rating"].split("/")[0])) for p in products]
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
        "has_error": False
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
