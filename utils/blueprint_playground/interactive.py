#!/usr/bin/env python3
"""
L++ Blueprint Playground - Interactive Web Server

A minimal CLI that serves an interactive web-based blueprint editor and simulator.
All logic lives in blueprints + COMPUTE units. This is just a thin server.
"""

import sys
import json
import argparse
import webbrowser
from pathlib import Path
from http.server import HTTPServer, SimpleHTTPRequestHandler
from urllib.parse import parse_qs, urlparse
import importlib.util

# Import from src package
from src import PLAY_REGISTRY

HERE = Path(__file__).parent
TEMPLATE_PATH = HERE / "templates" / "playground.html"


def compile_and_load(blueprint_json: str, registry: dict):
    """Compile blueprint and return operator with given COMPUTE registry."""
    sys.path.insert(0, str(HERE.parent.parent / "src"))
    from frame_py.compiler import compile_blueprint

    out = HERE / "results" / f"{Path(blueprint_json).stem}_compiled.py"
    out.parent.mkdir(exist_ok=True)
    compile_blueprint(blueprint_json, str(out))

    # Load compiled operator
    spec = importlib.util.spec_from_file_location("op", out)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)

    # Convert "ns:name" -> (ns, name)
    reg = {tuple(k.split(":")): fn for k, fn in registry.items()}
    return mod.create_operator(reg)


class PlaygroundHandler(SimpleHTTPRequestHandler):
    """HTTP handler for the playground server."""

    def __init__(self, *args, playground_html=None, **kwargs):
        self.playground_html = playground_html
        super().__init__(*args, **kwargs)

    def log_message(self, format, *args):
        """Suppress default logging, use custom format."""
        print(f"  [{self.address_string()}] {args[0]}")

    def do_GET(self):
        """Handle GET requests."""
        parsed = urlparse(self.path)
        path = parsed.path

        if path == "/" or path == "/playground" or path == "/index.html":
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.end_headers()
            self.wfile.write(self.playground_html.encode("utf-8"))
            return

        if path == "/api/health":
            self.send_json({"status": "ok"})
            return

        # Serve static files from results directory
        if path.startswith("/results/"):
            file_path = HERE / path[1:]
            if file_path.exists():
                self.send_response(200)
                self.send_header("Content-Type", "application/json")
                self.end_headers()
                with open(file_path, "rb") as f:
                    self.wfile.write(f.read())
                return

        self.send_error(404)

    def do_POST(self):
        """Handle POST requests for API endpoints."""
        parsed = urlparse(self.path)
        path = parsed.path

        # Read body
        content_length = int(self.headers.get("Content-Length", 0))
        body = self.rfile.read(content_length).decode("utf-8") if content_length else "{}"

        try:
            params = json.loads(body)
        except json.JSONDecodeError:
            self.send_json({"error": "Invalid JSON"}, status=400)
            return

        # API endpoints
        if path == "/api/validate":
            result = PLAY_REGISTRY["play:validate_blueprint"](params)
            self.send_json(result)
            return

        if path == "/api/validate_json":
            result = PLAY_REGISTRY["play:validate_json"](params)
            self.send_json(result)
            return

        if path == "/api/format":
            result = PLAY_REGISTRY["play:format_blueprint"](params)
            self.send_json(result)
            return

        if path == "/api/diagram":
            result = PLAY_REGISTRY["play:generate_diagram"](params)
            self.send_json(result)
            return

        if path == "/api/init_sim":
            result = PLAY_REGISTRY["play:init_simulation"](params)
            self.send_json(result)
            return

        if path == "/api/dispatch":
            result = PLAY_REGISTRY["play:dispatch_event"](params)
            self.send_json(result)
            return

        if path == "/api/events":
            result = PLAY_REGISTRY["play:get_available_events"](params)
            self.send_json(result)
            return

        if path == "/api/share":
            result = PLAY_REGISTRY["play:encode_share_url"](params)
            self.send_json(result)
            return

        if path == "/api/import":
            result = PLAY_REGISTRY["play:decode_share_url"](params)
            self.send_json(result)
            return

        if path == "/api/load":
            result = PLAY_REGISTRY["play:load_blueprint"](params)
            self.send_json(result)
            return

        if path == "/api/export":
            result = PLAY_REGISTRY["play:export_blueprint"](params)
            self.send_json(result)
            return

        self.send_error(404)

    def send_json(self, data, status=200):
        """Send JSON response."""
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.end_headers()
        self.wfile.write(json.dumps(data).encode("utf-8"))

    def do_OPTIONS(self):
        """Handle CORS preflight."""
        self.send_response(200)
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.end_headers()


def run_server(port: int = 8765, open_browser: bool = True):
    """Start the playground server."""
    # Load HTML template
    if TEMPLATE_PATH.exists():
        with open(TEMPLATE_PATH) as f:
            html = f.read()
    else:
        html = """<!DOCTYPE html>
<html><head><title>L++ Playground</title></head>
<body style="background:#1a1a2e;color:#eee;font-family:sans-serif;padding:40px;">
<h1 style="color:#00d4ff;">L++ Blueprint Playground</h1>
<p>Template not found at: {}</p>
</body></html>""".format(TEMPLATE_PATH)

    # Create handler with template
    def handler(*args, **kwargs):
        return PlaygroundHandler(*args, playground_html=html, **kwargs)

    server = HTTPServer(("localhost", port), handler)

    url = f"http://localhost:{port}"
    print(f"\n  L++ Blueprint Playground")
    print(f"  ========================")
    print(f"  Server running at: {url}")
    print(f"  Press Ctrl+C to stop\n")

    if open_browser:
        webbrowser.open(url)

    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\n  Server stopped.")


def cli_mode():
    """Run in CLI mode for testing compute functions."""
    print("\n  L++ Blueprint Playground - CLI Mode\n")

    # Try to compile the blueprint
    try:
        play = compile_and_load(
            str(HERE / "blueprint_playground.json"),
            PLAY_REGISTRY
        )
        print("  Blueprint compiled successfully")
    except Exception as e:
        print(f"  Compile warning: {e}")
        play = None

    while True:
        try:
            cmd = input("\n> ").strip().split(maxsplit=1)
        except (EOFError, KeyboardInterrupt):
            break

        if not cmd:
            continue

        action = cmd[0].lower()
        arg = cmd[1] if len(cmd) > 1 else None

        if action in ("q", "quit", "exit"):
            break

        elif action == "help":
            print("  Commands:")
            print("    load <path>     Load blueprint from file")
            print("    validate <json> Validate JSON string")
            print("    format <json>   Format JSON string")
            print("    serve [port]    Start web server")
            print("    quit            Exit")

        elif action == "load" and arg:
            result = PLAY_REGISTRY["play:load_blueprint"]({"file_path": arg})
            print(json.dumps(result, indent=2))

        elif action == "validate" and arg:
            result = PLAY_REGISTRY["play:validate_blueprint"](
                {"blueprint_json": arg}
            )
            print(json.dumps(result, indent=2))

        elif action == "format" and arg:
            result = PLAY_REGISTRY["play:format_blueprint"](
                {"json_string": arg}
            )
            print(result.get("formatted", result.get("output")))

        elif action == "serve":
            port = int(arg) if arg else 8765
            run_server(port)
            break

        else:
            print(f"  Unknown command: {action}")

    print("  Goodbye!")


def main():
    parser = argparse.ArgumentParser(
        description="L++ Blueprint Playground - Interactive editor and simulator"
    )
    parser.add_argument(
        "-p", "--port",
        type=int,
        default=8765,
        help="Port for web server (default: 8765)"
    )
    parser.add_argument(
        "-n", "--no-browser",
        action="store_true",
        help="Don't open browser automatically"
    )
    parser.add_argument(
        "-c", "--cli",
        action="store_true",
        help="Run in CLI mode instead of web server"
    )
    parser.add_argument(
        "blueprint",
        nargs="?",
        help="Blueprint file to load on start"
    )

    args = parser.parse_args()

    if args.cli:
        cli_mode()
    else:
        run_server(port=args.port, open_browser=not args.no_browser)


if __name__ == "__main__":
    main()
