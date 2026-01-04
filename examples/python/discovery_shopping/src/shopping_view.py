"""
View rendering for Discovery Shopping.

Hermetic view functions: state + context -> HTML string.
No side effects, pure transformations.
"""

from typing import Any, Dict

# HTML Template (no emojis per coding style)
BASE_HTML = """<!DOCTYPE html>
<html>
<head>
    <title>Discovery Shopping</title>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <style>
        * {{ box-sizing: border-box; }}
        body {{
            font-family: -apple-system, sans-serif;
            max-width: 800px;
            margin: 0 auto;
            padding: 20px;
            background: #f5f5f5;
            color: #333;
        }}
        h1, h2, p {{ color: #333; }}
        .state {{
            background: #4CAF50;
            color: white;
            padding: 8px 16px;
            border-radius: 20px;
            display: inline-block;
            margin-bottom: 20px;
        }}
        .card {{
            background: white;
            border-radius: 12px;
            padding: 20px;
            margin: 15px 0;
            box-shadow: 0 2px 8px rgba(0,0,0,0.1);
            color: #333;
        }}
        .product {{
            padding: 12px 0;
            border-bottom: 1px solid #eee;
            color: #333;
        }}
        .product:last-child {{ border-bottom: none; }}
        .price {{ color: #4CAF50; font-weight: 600; }}
        .score {{
            background: #e3f2fd;
            padding: 4px 8px;
            border-radius: 8px;
            font-size: 0.85em;
            color: #1976D2;
        }}
        .reasons {{ color: #666; font-size: 0.9em; }}
        button {{
            background: #2196F3;
            color: white;
            border: none;
            padding: 10px 20px;
            border-radius: 8px;
            cursor: pointer;
            margin: 5px;
        }}
        button:hover {{ background: #1976D2; }}
        button.secondary {{ background: #757575; }}
        button.success {{ background: #4CAF50; }}
        .quiz-btn {{
            display: block;
            width: 100%;
            text-align: left;
            background: #f9f9f9;
            margin: 5px 0;
            color: #333;
        }}
        .quiz-btn:hover {{ background: #e3f2fd; }}
        input[type="text"] {{
            width: 100%;
            padding: 12px;
            border: 1px solid #ddd;
            border-radius: 8px;
            font-size: 16px;
            margin: 10px 0;
            color: #333;
            background: white;
        }}
        table {{ width: 100%; border-collapse: collapse; color: #333; }}
        th, td {{
            padding: 10px;
            text-align: left;
            border-bottom: 1px solid #eee;
            color: #333;
        }}
        .winner {{ color: #4CAF50; font-weight: 600; }}
        .error {{ background: #ffebee; color: #c62828; }}
        a {{ color: #2196F3; }}
        .loading-overlay {{
            display: none;
            position: fixed;
            top: 0;
            left: 0;
            width: 100%;
            height: 100%;
            background: rgba(0,0,0,0.6);
            z-index: 9999;
            justify-content: center;
            align-items: center;
            flex-direction: column;
        }}
        .loading-overlay.active {{ display: flex; }}
        .spinner {{
            width: 60px;
            height: 60px;
            border: 5px solid rgba(255,255,255,0.3);
            border-top-color: #4CAF50;
            border-radius: 50%;
            animation: spin 1s linear infinite;
        }}
        @keyframes spin {{ to {{ transform: rotate(360deg); }} }}
        .loading-text {{
            color: white;
            font-size: 1.2em;
            margin-top: 20px;
            text-align: center;
        }}
        .loading-subtext {{
            color: rgba(255,255,255,0.7);
            font-size: 0.9em;
            margin-top: 8px;
        }}
    </style>
</head>
<body>
    <div class="loading-overlay" id="loadingOverlay">
        <div class="spinner"></div>
        <div class="loading-text">Searching...</div>
        <div class="loading-subtext">This may take a moment</div>
    </div>
    <h1>Discovery Shopping</h1>
    <div class="state">{state}</div>
    {content}
    <script>
        document.querySelectorAll('form').forEach(form => {{
            form.addEventListener('submit', function(e) {{
                const event = form.querySelector('input[name="event"]');
                if (event) {{
                    const val = event.value.toUpperCase();
                    const overlay = document.getElementById('loadingOverlay');
                    const text = overlay.querySelector('.loading-text');
                    const sub = overlay.querySelector('.loading-subtext');
                    if (val === 'SELECT_CATEGORY') {{
                        text.textContent = 'Searching products...';
                        sub.textContent = 'Finding the best deals';
                        overlay.classList.add('active');
                    }} else if (val === 'FETCH_MORE') {{
                        text.textContent = 'Loading more...';
                        sub.textContent = 'Fetching additional results';
                        overlay.classList.add('active');
                    }} else if (['DONE','ANSWER','SKIP_QUIZ'].includes(val)) {{
                        text.textContent = 'Processing...';
                        sub.textContent = 'Please wait';
                        overlay.classList.add('active');
                    }} else if (val === 'VIEW') {{
                        text.textContent = 'Loading details...';
                        sub.textContent = 'Fetching product info';
                        overlay.classList.add('active');
                    }}
                }}
            }});
        }});
    </script>
</body>
</html>"""


def _hidden(name: str, value: str) -> str:
    """Generate hidden input field."""
    return f'<input type="hidden" name="{name}" value="{value}">'


def _btn(text: str, cls: str = "") -> str:
    """Generate button element."""
    c = f' class="{cls}"' if cls else ""
    return f'<button type="submit"{c}>{text}</button>'


def _form(event: str, content: str, inline: bool = False) -> str:
    """Generate form with event."""
    style = ' style="display:inline"' if inline else ""
    return (f'<form method="POST"{style}>'
            f'{_hidden("event", event)}{content}</form>')


def renderIdle(ctx: Dict[str, Any]) -> str:
    """Render idle state - category selection."""
    return '''<div class="card"><h2>Select Category</h2>
        <form method="POST">
        <input type="hidden" name="event" value="SELECT_CATEGORY">
        <input type="text" name="category"
               placeholder="headphones, laptops..." required>
        <button type="submit" class="success">Start</button>
        </form></div>'''


def renderQuizzing(ctx: Dict[str, Any]) -> str:
    """Render quizzing state - preference questions."""
    qs = ctx.get("quiz_questions", [])
    idx = min(ctx.get("current_question_idx", 0), len(qs) - 1)
    q = qs[idx] if qs else {}
    opts = "".join(
        f'<button type="submit" name="answer" value="{o}" '
        f'class="quiz-btn">{o}</button>'
        for o in q.get("options", [])
    )
    return f'''<div class="card">
        <h2>Q{idx+1}/{len(qs)}: {q.get("text", "")}</h2>
        <form method="POST">
        {_hidden("event", "ANSWER")}
        {_hidden("question_id", q.get("id", ""))}
        {opts}</form>
        {_form("SKIP_QUIZ", _btn("Skip", "secondary"))}
        </div>'''


def renderFetching(ctx: Dict[str, Any]) -> str:
    """Render fetching state - product search progress."""
    count = len(ctx.get("products", []) or [])
    total = ctx.get("fetch_total", count) or count
    offset = ctx.get("fetch_offset", count) or count
    hasMore = ctx.get("has_more_products", False)
    pct = int(offset / total * 100) if total > 0 else 100

    resetBtn = _form("RESET", _btn("Start Over", "secondary"), inline=True)

    if count == 0 and not hasMore:
        return f'''<div class="card"><h2>No Products Found</h2>
            <p>Try a different search term or category.</p>
            {_form("RESET", _btn("Try Again", "success"))}
            </div>'''

    progress = f'''<div style="background:#e0e0e0;border-radius:8px;
        overflow:hidden;margin:10px 0;">
        <div style="background:#4CAF50;height:24px;width:{pct}%;
        transition:width 0.3s;"></div></div>
        <p>Found {count} products</p>'''

    if hasMore:
        return f'''<div class="card"><h2>Searching Products...</h2>
            {progress}
            {_form("FETCH_MORE", _btn("Load More"), inline=True)}
            {_form("DONE", _btn(f"Continue with {count}", "success"),
                   inline=True)}
            {resetBtn}</div>'''
    else:
        return f'''<div class="card"><h2>Search Complete!</h2>
            {progress}
            {_form("DONE", _btn("Analyze Reviews", "success"), inline=True)}
            {resetBtn}</div>'''


def renderAnalyzing(ctx: Dict[str, Any]) -> str:
    """Render analyzing state."""
    return f'''<div class="card"><h2>Reviews analyzed!</h2>
        {_form("DONE", _btn("Next Step", "success"))}</div>'''


def renderRanking(ctx: Dict[str, Any]) -> str:
    """Render ranking state."""
    return f'''<div class="card"><h2>Rankings ready!</h2>
        {_form("DONE", _btn("Next Step", "success"))}</div>'''


def renderBrowsing(ctx: Dict[str, Any]) -> str:
    """Render browsing state - ranked product list."""
    ranks = ctx.get("rankings", [])[:10]
    items = ""
    for i, r in enumerate(ranks, 1):
        name = r.get("product_name", "Product")
        price = r.get("price", 0)
        rating = r.get("rating", 0)
        score = r.get("score", 0)
        reasons = r.get("reasons", [])[:2]
        pid = r.get("product_id", "")
        viewForm = (f'<form method="POST" style="display:inline">'
                    f'{_hidden("event", "VIEW")}'
                    f'{_hidden("product_id", pid)}'
                    f'{_btn("View")}</form>')
        items += f'''<div class="product">
            <strong>{i}. {name}</strong>
            <span class="price">${price:.2f}</span>
            <span class="score">*{rating:.1f} | {score:.2f}</span>
            <div class="reasons">{"; ".join(reasons)}</div>
            {viewForm}</div>'''

    cat = ctx.get("category", "")
    return f'''<div class="card">
        <h2>Top {len(ranks)} Results for "{cat}"</h2>{items}</div>
        <div class="card">
        {_form("NEW_SEARCH", _btn("New Search", "secondary"))}
        </div>'''


def renderDetail(ctx: Dict[str, Any]) -> str:
    """Render detail state - single product view."""
    pid = ctx.get("selected_product", "")
    prod = next(
        (p for p in ctx.get("products", []) if p["id"] == pid), {}
    )
    rev = ctx.get("reviews", {}).get(pid, {})
    link = ctx.get("affiliate_links", {}).get(pid, "")
    snippet = prod.get("snippet", "")
    sources = rev.get("sources", [])

    snippetHtml = (f'<p><strong>Snippet:</strong> <em>{snippet}</em></p>'
                   if snippet else "")
    sourcesHtml = (f'<p><strong>Sources:</strong> {", ".join(sources)}</p>'
                   if sources else "")
    linkHtml = (f'<p><a href="{link}" target="_blank">View Source / Buy</a></p>'
                if link else "")

    alertForm = (f'<form method="POST" style="display:inline">'
                 f'{_hidden("event", "SET_ALERT")}'
                 f'{_hidden("product_id", pid)}'
                 f'{_hidden("alert_type", "price")}'
                 f'{_btn("Alert")}</form>')

    return f'''<div class="card">
        <h2>{prod.get("name", pid)}</h2>
        <p><strong>Price:</strong>
           <span class="price">${prod.get("price", 0):.2f}</span></p>
        <p><strong>Rating:</strong> *{prod.get("rating", 0):.1f}/5</p>
        {snippetHtml}
        <p><strong>Pros:</strong> {", ".join(rev.get("pros", [])) or "N/A"}</p>
        <p><strong>Cons:</strong> {", ".join(rev.get("cons", [])) or "N/A"}</p>
        {sourcesHtml}
        {linkHtml}</div>
        <div class="card">
        {_form("BACK", _btn("Back", "secondary"), inline=True)}
        {alertForm}</div>'''


def renderAlerting(ctx: Dict[str, Any]) -> str:
    """Render alerting state - confirm alert setup."""
    return f'''<div class="card"><h2>Set Alert?</h2>
        {_form("CONFIRM", _btn("Confirm", "success"), inline=True)}
        {_form("CANCEL", _btn("Cancel", "secondary"), inline=True)}
        </div>'''


def renderComparing(ctx: Dict[str, Any]) -> str:
    """Render comparing state - side-by-side comparison."""
    comp = ctx.get("comparison", {})
    prods = comp.get("products", [])
    dims = comp.get("dimensions", [])
    wins = comp.get("winners", {})

    hdrs = "".join(f"<th>{p['name']}</th>" for p in prods)
    rows = ""
    for d in dims:
        cells = ""
        for p in prods:
            cls = ' class="winner"' if wins.get(d) == p["id"] else ""
            val = p.get("values", {}).get(d, "")
            cells += f"<td{cls}>{val}</td>"
        rows += f"<tr><td><strong>{d}</strong></td>{cells}</tr>"

    return f'''<div class="card"><h2>Compare</h2>
        <table><tr><th></th>{hdrs}</tr>{rows}</table></div>
        <div class="card">
        {_form("BACK", _btn("Back", "secondary"))}
        </div>'''


def renderError(ctx: Dict[str, Any]) -> str:
    """Render error state."""
    err = ctx.get("error", "Unknown error")
    return f'''<div class="card error"><h2>Error</h2>
        <p>{err}</p>
        {_form("RETRY", _btn("Retry"))}
        </div>'''


# State -> Renderer mapping
RENDERERS = {
    "idle": renderIdle,
    "quizzing": renderQuizzing,
    "fetching": renderFetching,
    "analyzing": renderAnalyzing,
    "ranking": renderRanking,
    "browsing": renderBrowsing,
    "detail": renderDetail,
    "alerting": renderAlerting,
    "comparing": renderComparing,
    "error": renderError,
}


def renderPage(state: str, ctx: Dict[str, Any]) -> str:
    """
    Render full HTML page for given state and context.

    Hermetic: pure function, no side effects.
    Input: state string, context dict
    Output: HTML string
    """
    renderer = RENDERERS.get(state)
    if renderer:
        content = renderer(ctx)
    else:
        content = f'<div class="card">State: {state}</div>'
    return BASE_HTML.format(state=state, content=content)
