#!/usr/bin/env python3
"""
Discovery Shopping - Interactive CLI + Web App

Fit-first product discovery with explainable matching.
"""

import sys
import json
import importlib.util
from pathlib import Path
from http.server import HTTPServer, BaseHTTPRequestHandler
from urllib.parse import parse_qs, urlparse

sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent / "src"))

from frame_py.compiler import compile_blueprint  # noqa: E402
from src import COMPUTE_REGISTRY  # noqa: E402

HERE = Path(__file__).parent


def compile_and_load(blueprint_json: str, registry: dict):
    """Compile blueprint and return operator with COMPUTE registry."""
    out = HERE / "results" / f"{Path(blueprint_json).stem}_compiled.py"
    out.parent.mkdir(exist_ok=True)
    compile_blueprint(blueprint_json, str(out))
    spec = importlib.util.spec_from_file_location("op", out)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    reg = {tuple(k.split(":")): fn for k, fn in registry.items()}
    return mod.create_operator(reg)


def main():
    blueprint = str(HERE / "discovery_shopping.json")
    op = compile_and_load(blueprint, COMPUTE_REGISTRY)

    print("\n🛒 Discovery Shopping - Fit-First Product Discovery")
    print("=" * 50)
    print("Commands: <event> [args] | state | ctx | quit\n")

    while True:
        state = op.state
        prompt = f"[{state}] > "
        try:
            line = input(prompt).strip()
        except (EOFError, KeyboardInterrupt):
            print("\nGoodbye!")
            break

        if not line:
            continue
        if line == "quit":
            break
        if line == "state":
            print(f"Current state: {op.state}")
            continue
        if line == "ctx":
            print(json.dumps(op.context, indent=2, default=str))
            continue

        parts = line.split(maxsplit=1)
        event = parts[0].upper()
        payload = {}

        if len(parts) > 1:
            try:
                payload = json.loads(parts[1])
            except json.JSONDecodeError:
                payload = {"value": parts[1]}

        result = op.dispatch(event, payload)
        success, new_state, error = result
        if success:
            print(f"→ {op.state}")
            # Show relevant context based on state
            _show_state_info(op)
        if error:
            print(f"Error: {error}")


def _show_state_info(op):
    """Show relevant information based on current state."""
    ctx = op.context
    state = op.state

    if state == "quizzing" and ctx.get("quiz_questions"):
        print("\n📋 Quiz Questions:")
        for q in ctx["quiz_questions"]:
            print(f"  {q['id']}: {q['text']}")
            print(f"      Options: {', '.join(q['options'])}")
        print(
            "\n  Answer with: ANSWER {{\"question_id\": "
            "\"q1\", \"answer\": \"Music\"}}"
        )
        print("  Or: SKIP_QUIZ to skip")

    elif state == "fetching" and ctx.get("products"):
        print(f"\n📦 Found {len(ctx['products'])} products")
        print("  Continue with: DONE")

    elif state == "analyzing":
        print("\n🔍 Aggregating review insights...")
        print("  Continue with: DONE")

    elif state == "ranking":
        print("\n🎯 Computing rankings...")
        print("  Continue with: DONE")

    elif state == "browsing" and ctx.get("rankings"):
        print("\n🏆 Product Rankings:")
        for i, r in enumerate(ctx["rankings"][:5], 1):
            print(f"  {i}. {r['product_name']} (${r['price']:.2f})")
            print(f"     Score: {r['score']:.2f} | Rating: {r['rating']}/5")
            print(f"     Why: {'; '.join(r['reasons'][:2])}")
        print("\n  VIEW {\"product_id\": \"hp001\"} - View details")
        print("  COMPARE {\"product_ids\": [\"hp001\", \"hp002\"]} - Compare")

    elif state == "comparing" and ctx.get("comparison"):
        comp = ctx["comparison"]
        print("\n⚖️ Side-by-Side Comparison:")
        for dim in comp.get("dimensions", [])[:4]:
            print(f"\n  {dim}:")
            for p in comp.get("products", []):
                winner = "✓" if comp.get(
                    "winners", {}
                ).get(dim) == p["id"] else " "
                print(
                    f"    {winner} {p['name']}: "
                    f"{p['values'].get(dim, 'N/A')}"
                )
        print("\n  BACK to return to browsing")

    elif state == "detail" and ctx.get("selected_product"):
        pid = ctx["selected_product"]
        print(f"\n📱 Viewing: {pid}")
        if ctx.get("affiliate_links"):
            link = ctx["affiliate_links"].get(pid, "")
            print(f"  Affiliate link: {link}")
        print(
            "\n  SET_ALERT {\"product_id\": \""
            + pid +
            "\", \"alert_type\": \"price\"}"
        )
        print("  COMPARE {\"product_ids\": [\"" + pid + "\", \"hp002\"]}")
        print("  BACK to return")

    elif state == "alerting":
        print("\n🔔 Setting alert...")
        print("  CONFIRM to subscribe | CANCEL to abort")

    elif state == "error":
        print(f"\n❌ Error: {ctx.get('error', 'Unknown')}")
        print("  RETRY to recover")


# =============================================================================
# WEB APP
# =============================================================================

HTML_TEMPLATE = """<!DOCTYPE html>
<html>
<head>
    <title>🛒 Discovery Shopping</title>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <style>
        * { box-sizing: border-box; }
        body { font-family: -apple-system, BlinkMacSystemFont, sans-serif; max-width: 800px; margin: 0 auto; padding: 20px; background: #f5f5f5; }
        h1 { color: #333; }
        .state { background: #4CAF50; color: white; padding: 8px 16px; border-radius: 20px; display: inline-block; margin-bottom: 20px; }
        .card { background: white; border-radius: 12px; padding: 20px; margin: 15px 0; box-shadow: 0 2px 8px rgba(0,0,0,0.1); }
        .product { display: flex; justify-content: space-between; align-items: center; padding: 12px 0; border-bottom: 1px solid #eee; }
        .product:last-child { border-bottom: none; }
        .product-name { font-weight: 600; }
        .product-price { color: #4CAF50; font-weight: 600; }
        .score { background: #e3f2fd; padding: 4px 8px; border-radius: 8px; font-size: 0.85em; }
        .reasons { color: #666; font-size: 0.9em; margin-top: 4px; }
        button { background: #2196F3; color: white; border: none; padding: 10px 20px; border-radius: 8px; cursor: pointer; margin: 5px; font-size: 14px; }
        button:hover { background: #1976D2; }
        button.secondary { background: #757575; }
        button.success { background: #4CAF50; }
        .quiz-option { display: block; width: 100%; text-align: left; background: #f9f9f9; margin: 5px 0; }
        .quiz-option:hover { background: #e3f2fd; }
        input[type="text"] { width: 100%; padding: 12px; border: 1px solid #ddd; border-radius: 8px; font-size: 16px; }
        .form-group { margin: 15px 0; }
        .comparison-table { width: 100%; border-collapse: collapse; }
        .comparison-table th, .comparison-table td { padding: 10px; text-align: left; border-bottom: 1px solid #eee; }
        .winner { color: #4CAF50; font-weight: 600; }
        .error { background: #ffebee; color: #c62828; padding: 15px; border-radius: 8px; }
    </style>
</head>
<body>
    <h1>🛒 Discovery Shopping</h1>
    <div class="state">State: {state}</div>
    {content}
</body>
</html>
"""


def _render_idle():
    return """
    <div class="card">
        <h2>Select a Category</h2>
        <form method="POST" action="/dispatch">
            <input type="hidden" name="event" value="SELECT_CATEGORY">
            <div class="form-group">
                <input type="text" name="category" placeholder="e.g., headphones, laptops" required>
            </div>
            <button type="submit" class="success">Start Discovery →</button>
        </form>
    </div>
    """


def _render_quizzing(ctx):
    questions = ctx.get("quiz_questions", [])
    idx = ctx.get("current_question_idx", 0)
    if idx >= len(questions):
        idx = len(questions) - 1
    q = questions[idx] if questions else {}

    options_html = "".join(
        f'<button type="submit" name="answer" value="{opt}" class="quiz-option">{opt}</button>'
        for opt in q.get("options", [])
    )

    return f"""
    <div class="card">
        <h2>Question {idx + 1} of {len(questions)}</h2>
        <p style="font-size: 1.2em; margin: 20px 0;">{q.get('text', '')}</p>
        <form method="POST" action="/dispatch">
            <input type="hidden" name="event" value="ANSWER">
            <input type="hidden" name="question_id" value="{q.get('id', '')}">
            {options_html}
        </form>
        <form method="POST" action="/dispatch" style="margin-top: 20px;">
            <input type="hidden" name="event" value="SKIP_QUIZ">
            <button type="submit" class="secondary">Skip Quiz →</button>
        </form>
    </div>
    """


def _render_loading(ctx, message):
    return f"""
    <div class="card">
        <h2>{message}</h2>
        <form method="POST" action="/dispatch">
            <input type="hidden" name="event" value="DONE">
            <button type="submit" class="success">Continue →</button>
        </form>
    </div>
    """


def _render_browsing(ctx):
    rankings = ctx.get("rankings", [])[:5]
    products_html = ""
    for i, r in enumerate(rankings, 1):
        products_html += f"""
        <div class="product">
            <div>
                <div class="product-name">{i}. {r['product_name']}</div>
                <div class="reasons">{'; '.join(r['reasons'][:2])}</div>
            </div>
            <div style="text-align: right;">
                <div class="product-price">${r['price']:.2f}</div>
                <div class="score">Score: {r['score']:.2f} | ⭐ {r['rating']}</div>
                <form method="POST" action="/dispatch" style="display: inline;">
                    <input type="hidden" name="event" value="VIEW">
                    <input type="hidden" name="product_id" value="{r['product_id']}">
                    <button type="submit" style="margin-top: 8px;">View</button>
                </form>
            </div>
        </div>
        """

    return f"""
    <div class="card">
        <h2>🏆 Top Matches</h2>
        {products_html}
    </div>
    <div class="card">
        <form method="POST" action="/dispatch">
            <input type="hidden" name="event" value="NEW_SEARCH">
            <button type="submit" class="secondary">New Search</button>
        </form>
    </div>
    """


def _render_detail(ctx):
    pid = ctx.get("selected_product", "")
    products = ctx.get("products", [])
    product = next((p for p in products if p["id"] == pid), {})
    reviews = ctx.get("reviews", {}).get(pid, {})
    link = ctx.get("affiliate_links", {}).get(pid, "")

    return f"""
    <div class="card">
        <h2>{product.get('name', pid)}</h2>
        <p><strong>Brand:</strong> {product.get('brand', 'N/A')}</p>
        <p><strong>Price:</strong> <span class="product-price">${product.get('price', 0):.2f}</span></p>
        <p><strong>Rating:</strong> ⭐ {product.get('rating', 0)}/5 ({product.get('review_count', 0)} reviews)</p>
        <p><strong>Features:</strong> {', '.join(product.get('features', []))}</p>
        <p><strong>Pros:</strong> {', '.join(reviews.get('pros', []))}</p>
        <p><strong>Cons:</strong> {', '.join(reviews.get('cons', []))}</p>
        {f'<p><a href="{link}" target="_blank">🔗 Buy Now (Affiliate)</a></p>' if link else ''}
    </div>
    <div class="card">
        <form method="POST" action="/dispatch" style="display: inline;">
            <input type="hidden" name="event" value="BACK">
            <button type="submit" class="secondary">← Back</button>
        </form>
        <form method="POST" action="/dispatch" style="display: inline;">
            <input type="hidden" name="event" value="SET_ALERT">
            <input type="hidden" name="product_id" value="{pid}">
            <input type="hidden" name="alert_type" value="price">
            <button type="submit">🔔 Set Price Alert</button>
        </form>
    </div>
    """


def _render_comparing(ctx):
    comp = ctx.get("comparison", {})
    products = comp.get("products", [])
    dims = comp.get("dimensions", [])
    winners = comp.get("winners", {})

    if not products:
        return '<div class="card error">No comparison data</div>'

    headers = "".join(f"<th>{p['name']}</th>" for p in products)
    rows = ""
    for dim in dims:
        cells = ""
        for p in products:
            val = p.get("values", {}).get(dim, "N/A")
            is_winner = winners.get(dim) == p["id"]
            cls = ' class="winner"' if is_winner else ''
            cells += f"<td{cls}>{'✓ ' if is_winner else ''}{val}</td>"
        rows += f"<tr><td><strong>{dim}</strong></td>{cells}</tr>"

    return f"""
    <div class="card">
        <h2>⚖️ Comparison</h2>
        <table class="comparison-table">
            <tr><th></th>{headers}</tr>
            {rows}
        </table>
    </div>
    <div class="card">
        <form method="POST" action="/dispatch">
            <input type="hidden" name="event" value="BACK">
            <button type="submit" class="secondary">← Back to Results</button>
        </form>
    </div>
    """


def _render_alerting(ctx):
    return """
    <div class="card">
        <h2>🔔 Set Alert</h2>
        <p>You'll be notified when the price drops or item is back in stock.</p>
        <form method="POST" action="/dispatch" style="display: inline;">
            <input type="hidden" name="event" value="CONFIRM">
            <button type="submit" class="success">Confirm Alert</button>
        </form>
        <form method="POST" action="/dispatch" style="display: inline;">
            <input type="hidden" name="event" value="CANCEL">
            <button type="submit" class="secondary">Cancel</button>
        </form>
    </div>
    """


def _render_error(ctx):
    return f"""
    <div class="card error">
        <h2>❌ Error</h2>
        <p>{ctx.get('error', 'Unknown error')}</p>
        <form method="POST" action="/dispatch">
            <input type="hidden" name="event" value="RETRY">
            <button type="submit">Retry</button>
        </form>
    </div>
    """


class ShoppingHandler(BaseHTTPRequestHandler):
    op = None  # Set by serve_web()

    def log_message(self, format, *args):
        pass  # Suppress default logging

    def do_GET(self):
        self._render_page()

    def do_POST(self):
        length = int(self.headers.get("Content-Length", 0))
        body = self.rfile.read(length).decode("utf-8")
        params = parse_qs(body)

        event = params.get("event", [""])[0].upper()
        payload = {}

        # Build payload from form params
        for key in ["category", "product_id", "question_id", "answer", "alert_type", "product_ids"]:
            if key in params:
                val = params[key][0]
                if key == "product_ids":
                    val = val.split(",")
                payload[key] = val

        if event:
            ShoppingHandler.op.dispatch(event, payload)

        # Redirect back to home
        self.send_response(303)
        self.send_header("Location", "/")
        self.end_headers()

    def _render_page(self):
        op = ShoppingHandler.op
        state = op.state
        ctx = op.context

        if state == "idle":
            content = _render_idle()
        elif state == "quizzing":
            content = _render_quizzing(ctx)
        elif state == "fetching":
            content = _render_loading(ctx, "📦 Fetching products...")
        elif state == "analyzing":
            content = _render_loading(ctx, "🔍 Analyzing reviews...")
        elif state == "ranking":
            content = _render_loading(ctx, "🎯 Computing rankings...")
        elif state == "browsing":
            content = _render_browsing(ctx)
        elif state == "detail":
            content = _render_detail(ctx)
        elif state == "comparing":
            content = _render_comparing(ctx)
        elif state == "alerting":
            content = _render_alerting(ctx)
        elif state == "error":
            content = _render_error(ctx)
        else:
            content = f"<div class='card'>Unknown state: {state}</div>"

        html = HTML_TEMPLATE.format(state=state, content=content)

        self.send_response(200)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.end_headers()
        self.wfile.write(html.encode("utf-8"))


def serve_web(port=10001):
    """Run web server on specified port."""
    blueprint = str(HERE / "discovery_shopping.json")
    ShoppingHandler.op = compile_and_load(blueprint, COMPUTE_REGISTRY)

    server = HTTPServer(("0.0.0.0", port), ShoppingHandler)
    print(f"\n🛒 Discovery Shopping Web App")
    print(f"   Running at http://localhost:{port}")
    print("   Press Ctrl+C to stop\n")

    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nShutting down...")
        server.shutdown()


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "web":
        port = int(sys.argv[2]) if len(sys.argv) > 2 else 10001
        serve_web(port)
    else:
        main()
