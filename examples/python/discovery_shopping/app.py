#!/usr/bin/env python3
"""
Discovery Shopping - Web App

Quick web interface on port 10001.
Usage: python app.py
"""

from src import COMPUTE_REGISTRY
from frame_py.compiler import compile_blueprint
import sys
from pathlib import Path
from http.server import HTTPServer, BaseHTTPRequestHandler
from urllib.parse import parse_qs
import importlib.util

sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent / "src"))


HERE = Path(__file__).parent
PORT = 10001


def compile_and_load():
    """Compile blueprint and return operator."""
    blueprint = str(HERE / "discovery_shopping.json")
    out = HERE / "results" / "discovery_shopping_compiled.py"
    out.parent.mkdir(exist_ok=True)
    compile_blueprint(blueprint, str(out))
    spec = importlib.util.spec_from_file_location("op", out)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    reg = {tuple(k.split(":")): fn for k, fn in COMPUTE_REGISTRY.items()}
    return mod.create_operator(reg)


HTML = """<!DOCTYPE html>
<html>
<head>
    <title>🛒 Discovery Shopping</title>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <style>
        * {{ box-sizing: border-box; }}
        body {{ font-family: -apple-system, sans-serif; max-width: 800px; margin: 0 auto; padding: 20px; background: #f5f5f5; color: #333; }}
        h1 {{ color: #333; }}
        h2 {{ color: #333; }}
        p {{ color: #333; }}
        .state {{ background: #4CAF50; color: white; padding: 8px 16px; border-radius: 20px; display: inline-block; margin-bottom: 20px; }}
        .card {{ background: white; border-radius: 12px; padding: 20px; margin: 15px 0; box-shadow: 0 2px 8px rgba(0,0,0,0.1); color: #333; }}
        .product {{ padding: 12px 0; border-bottom: 1px solid #eee; color: #333; }}
        .product:last-child {{ border-bottom: none; }}
        .price {{ color: #4CAF50; font-weight: 600; }}
        .score {{ background: #e3f2fd; padding: 4px 8px; border-radius: 8px; font-size: 0.85em; color: #1976D2; }}
        .reasons {{ color: #666; font-size: 0.9em; }}
        button {{ background: #2196F3; color: white; border: none; padding: 10px 20px; border-radius: 8px; cursor: pointer; margin: 5px; }}
        button:hover {{ background: #1976D2; }}
        button.secondary {{ background: #757575; }}
        button.success {{ background: #4CAF50; }}
        .quiz-btn {{ display: block; width: 100%; text-align: left; background: #f9f9f9; margin: 5px 0; color: #333; }}
        .quiz-btn:hover {{ background: #e3f2fd; }}
        input[type="text"] {{ width: 100%; padding: 12px; border: 1px solid #ddd; border-radius: 8px; font-size: 16px; margin: 10px 0; color: #333; background: white; }}
        table {{ width: 100%; border-collapse: collapse; color: #333; }}
        th, td {{ padding: 10px; text-align: left; border-bottom: 1px solid #eee; color: #333; }}
        .winner {{ color: #4CAF50; font-weight: 600; }}
        .error {{ background: #ffebee; color: #c62828; }}
        a {{ color: #2196F3; }}
    </style>
</head>
<body>
    <h1>🛒 Discovery Shopping</h1>
    <div class="state">{state}</div>
    {content}
</body>
</html>"""


class Handler(BaseHTTPRequestHandler):
    op = None

    def log_message(self, *args):
        pass

    def do_GET(self):
        self._render()

    def do_POST(self):
        length = int(self.headers.get("Content-Length", 0))
        body = self.rfile.read(length).decode()
        params = parse_qs(body)

        event = params.get("event", [""])[0].upper()
        payload = {}
        for k in ["category", "product_id", "question_id", "answer", "alert_type"]:
            if k in params:
                payload[k] = params[k][0]
        if "product_ids" in params:
            payload["product_ids"] = params["product_ids"][0].split(",")

        if event:
            Handler.op.dispatch(event, payload)

        self.send_response(303)
        self.send_header("Location", "/")
        self.end_headers()

    def _render(self):
        ctx = Handler.op.context
        state = Handler.op.state
        content = self._content(state, ctx)
        html = HTML.format(state=state, content=content)
        self.send_response(200)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.end_headers()
        self.wfile.write(html.encode())

    def _content(self, state, ctx):
        if state == "idle":
            return '''<div class="card"><h2>Select Category</h2>
                <form method="POST"><input type="hidden" name="event" value="SELECT_CATEGORY">
                <input type="text" name="category" placeholder="headphones, laptops..." required>
                <button type="submit" class="success">Start →</button></form></div>'''

        if state == "quizzing":
            qs = ctx.get("quiz_questions", [])
            idx = min(ctx.get("current_question_idx", 0), len(qs) - 1)
            q = qs[idx] if qs else {}
            opts = "".join(
                f'<button type="submit" name="answer" value="{o}" class="quiz-btn">{o}</button>' for o in q.get("options", []))
            return f'''<div class="card"><h2>Q{idx+1}/{len(qs)}: {q.get("text","")}</h2>
                <form method="POST"><input type="hidden" name="event" value="ANSWER">
                <input type="hidden" name="question_id" value="{q.get("id","")}">
                {opts}</form>
                <form method="POST"><input type="hidden" name="event" value="SKIP_QUIZ">
                <button type="submit" class="secondary">Skip →</button></form></div>'''

        if state in ("fetching", "analyzing", "ranking"):
            if state == "fetching":
                count = len(ctx.get("products", []))
                total = ctx.get("fetch_total", count)
                offset = ctx.get("fetch_offset", count)
                has_more = ctx.get("has_more_products", False)
                pct = int(offset / total * 100) if total > 0 else 100

                progress = f'''<div style="background:#e0e0e0;border-radius:8px;overflow:hidden;margin:10px 0;">
                    <div style="background:#4CAF50;height:24px;width:{pct}%;transition:width 0.3s;"></div></div>
                    <p>📦 Fetched {offset}/{total} products ({pct}%)</p>'''

                if has_more:
                    return f'''<div class="card"><h2>🔍 Searching Products...</h2>{progress}
                        <form method="POST" style="display:inline"><input type="hidden" name="event" value="FETCH_MORE">
                        <button type="submit">Load Next 50 →</button></form>
                        <form method="POST" style="display:inline"><input type="hidden" name="event" value="DONE">
                        <button type="submit" class="success">Continue with {count} →</button></form></div>'''
                else:
                    return f'''<div class="card"><h2>✅ Search Complete!</h2>{progress}
                        <form method="POST"><input type="hidden" name="event" value="DONE">
                        <button type="submit" class="success">Analyze Reviews →</button></form></div>'''
            else:
                msg = {"analyzing": "🔍 Reviews analyzed!",
                       "ranking": "🎯 Rankings ready!"}[state]
                return f'''<div class="card"><h2>{msg}</h2>
                    <form method="POST"><input type="hidden" name="event" value="DONE">
                    <button type="submit" class="success">Next Step →</button></form></div>'''

        if state == "browsing":
            ranks = ctx.get("rankings", [])[:10]
            items = ""
            for i, r in enumerate(ranks, 1):
                name = r.get("product_name", "Product")
                price = r.get("price", 0)
                rating = r.get("rating", 0)
                score = r.get("score", 0)
                reasons = r.get("reasons", [])[:2]
                pid = r.get("product_id", "")
                items += f'''<div class="product"><strong>{i}. {name}</strong> 
                    <span class="price">${price:.2f}</span> <span class="score">⭐{rating:.1f} | {score:.2f}</span>
                    <div class="reasons">{"; ".join(reasons)}</div>
                    <form method="POST" style="display:inline"><input type="hidden" name="event" value="VIEW">
                    <input type="hidden" name="product_id" value="{pid}">
                    <button type="submit">View</button></form></div>'''
            return f'''<div class="card"><h2>🏆 Top {len(ranks)} Results for "{ctx.get("category","")}"</h2>{items}</div>
                <div class="card"><form method="POST"><input type="hidden" name="event" value="NEW_SEARCH">
                <button type="submit" class="secondary">New Search</button></form></div>'''

        if state == "detail":
            pid = ctx.get("selected_product", "")
            prod = next(
                (p for p in ctx.get("products", []) if p["id"] == pid), {})
            rev = ctx.get("reviews", {}).get(pid, {})
            link = ctx.get("affiliate_links", {}).get(pid, "")
            snippet = prod.get("snippet", "")
            source = prod.get("source", "")
            sources = rev.get("sources", [])
            return f'''<div class="card"><h2>{prod.get("name", pid)}</h2>
                <p><strong>Price:</strong> <span class="price">${prod.get("price",0):.2f}</span></p>
                <p><strong>Rating:</strong> ⭐{prod.get("rating",0):.1f}/5</p>
                {f'<p><strong>Snippet:</strong> <em>{snippet}</em></p>' if snippet else ""}
                <p><strong>Pros:</strong> {", ".join(rev.get("pros",[])) or "N/A"}</p>
                <p><strong>Cons:</strong> {", ".join(rev.get("cons",[])) or "N/A"}</p>
                {f'<p><strong>Review Sources:</strong> {", ".join(sources)}</p>' if sources else ""}
                {f'<p><a href="{link}" target="_blank">🔗 View Source / Buy</a></p>' if link else ""}</div>
                <div class="card"><form method="POST" style="display:inline"><input type="hidden" name="event" value="BACK">
                <button type="submit" class="secondary">← Back</button></form>
                <form method="POST" style="display:inline"><input type="hidden" name="event" value="SET_ALERT">
                <input type="hidden" name="product_id" value="{pid}"><input type="hidden" name="alert_type" value="price">
                <button type="submit">🔔 Alert</button></form></div>'''

        if state == "alerting":
            return '''<div class="card"><h2>🔔 Set Alert?</h2>
                <form method="POST" style="display:inline"><input type="hidden" name="event" value="CONFIRM">
                <button type="submit" class="success">Confirm</button></form>
                <form method="POST" style="display:inline"><input type="hidden" name="event" value="CANCEL">
                <button type="submit" class="secondary">Cancel</button></form></div>'''

        if state == "comparing":
            comp = ctx.get("comparison", {})
            prods = comp.get("products", [])
            dims = comp.get("dimensions", [])
            wins = comp.get("winners", {})
            hdrs = "".join(f"<th>{p['name']}</th>" for p in prods)
            rows = "".join(f"<tr><td><strong>{d}</strong></td>" + "".join(
                f'<td class="{"winner" if wins.get(d)==p["id"] else ""}">{p.get("values",{}).get(d,"")}</td>' for p in prods
            ) + "</tr>" for d in dims)
            return f'''<div class="card"><h2>⚖️ Compare</h2><table><tr><th></th>{hdrs}</tr>{rows}</table></div>
                <div class="card"><form method="POST"><input type="hidden" name="event" value="BACK">
                <button type="submit" class="secondary">← Back</button></form></div>'''

        if state == "error":
            return f'''<div class="card error"><h2>❌ Error</h2><p>{ctx.get("error","Unknown")}</p>
                <form method="POST"><input type="hidden" name="event" value="RETRY">
                <button type="submit">Retry</button></form></div>'''

        return f'<div class="card">State: {state}</div>'


def main():
    Handler.op = compile_and_load()
    server = HTTPServer(("0.0.0.0", PORT), Handler)
    print(f"\n🛒 Discovery Shopping")
    print(f"   http://localhost:{PORT}")
    print("   Ctrl+C to stop\n")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nStopped.")


if __name__ == "__main__":
    main()
