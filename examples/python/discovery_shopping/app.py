#!/usr/bin/env python3
"""
Discovery Shopping - Web App

Minimal HTTP wrapper for L++ operator.
Usage: python app.py
"""

from src.shopping_view import renderPage
from src import COMPUTE_REGISTRY
from frame_py.compiler import compile_blueprint
import sys
import uuid
import importlib.util
from pathlib import Path
from http.server import HTTPServer, BaseHTTPRequestHandler
from urllib.parse import parse_qs
from http.cookies import SimpleCookie

sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent / "src"))


HERE = Path(__file__).parent
PORT = 10001
MAX_SESSIONS = 100
SESSIONS = {}


def compileAndLoad():
    """Compile blueprint and return module + registry."""
    blueprint = str(HERE / "discovery_shopping.json")
    out = HERE / "results" / "discovery_shopping_compiled.py"
    out.parent.mkdir(exist_ok=True)
    compile_blueprint(blueprint, str(out))
    spec = importlib.util.spec_from_file_location("op", out)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    reg = {tuple(k.split(":")): fn for k, fn in COMPUTE_REGISTRY.items()}
    return mod, reg


def getOperator(sessionId: str, mod, reg):
    """Get or create operator for session."""
    global SESSIONS
    if sessionId not in SESSIONS:
        if len(SESSIONS) >= MAX_SESSIONS:
            keys = list(SESSIONS.keys())[:MAX_SESSIONS // 2]
            for k in keys:
                del SESSIONS[k]
        SESSIONS[sessionId] = mod.create_operator(reg)
    return SESSIONS[sessionId]


class Handler(BaseHTTPRequestHandler):
    """HTTP handler - dispatches events to L++ operator."""
    mod = None
    reg = None

    def log_message(self, *args):
        pass

    def _getSession(self):
        """Extract session ID from cookie."""
        cookie = SimpleCookie(self.headers.get("Cookie", ""))
        if "session" in cookie:
            return cookie["session"].value
        return str(uuid.uuid4())

    def _getOp(self):
        """Get operator for current session."""
        sid = self._getSession()
        return sid, getOperator(sid, Handler.mod, Handler.reg)

    def do_GET(self):
        """Render current state."""
        sid, op = self._getOp()
        html = renderPage(op.state, op.context)
        self.send_response(200)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Set-Cookie", f"session={sid}; Path=/; HttpOnly")
        self.end_headers()
        self.wfile.write(html.encode())

    def do_POST(self):
        """Dispatch event to operator."""
        length = int(self.headers.get("Content-Length", 0))
        body = self.rfile.read(length).decode()
        params = parse_qs(body)

        event = params.get("event", [""])[0].upper()
        payload = {}
        for k in ["category", "product_id", "question_id",
                  "answer", "alert_type"]:
            if k in params:
                payload[k] = params[k][0]
        if "product_ids" in params:
            payload["product_ids"] = params["product_ids"][0].split(",")

        sid, op = self._getOp()
        if event:
            op.dispatch(event, payload)

        self.send_response(303)
        self.send_header("Location", "/")
        self.send_header("Set-Cookie", f"session={sid}; Path=/; HttpOnly")
        self.end_headers()


def main():
    """Start web server."""
    Handler.mod, Handler.reg = compileAndLoad()
    server = HTTPServer(("0.0.0.0", PORT), Handler)
    print(f"\nDiscovery Shopping")
    print(f"  http://localhost:{PORT}")
    print(f"  Sessions: {MAX_SESSIONS} max")
    print("  Ctrl+C to stop\n")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nStopped.")


if __name__ == "__main__":
    main()
