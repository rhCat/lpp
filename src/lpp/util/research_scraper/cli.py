#!/usr/bin/env python3
"""Research Scraper CLI - per build_rules.md: < 50 lines."""
from src.scraper_compute import COMPUTE_REGISTRY
from frame_py.compiler import compile_blueprint
from pathlib import Path
import sys
sys.path.insert(0, "../../src")

HERE = Path(__file__).parent


def load():
    import importlib.util
    out = HERE / "results/research_scraper_compiled.py"
    out.parent.mkdir(exist_ok=True)
    compile_blueprint(str(HERE / "research_scraper.json"), str(out))
    spec = importlib.util.spec_from_file_location("op", out)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod.create_operator({tuple(k.split(":")): fn for k, fn in COMPUTE_REGISTRY.items()})


def main():
    op = load()
    cmds = {"arxiv": "SEARCH_ARXIV",
            "scholar": "SEARCH_SCHOLAR", "web": "SEARCH_WEB"}
    print("Commands: arxiv|scholar|web <query> | select <idx> | clear | quit")
    while True:
        try:
            line = input(f"[{op.state}]> ").strip()
        except (EOFError, KeyboardInterrupt):
            break
        if not line:
            continue
        parts, cmd = line.split(maxsplit=1) + [""], line.split()[0].lower()
        arg = parts[1] if len(parts) > 1 else ""
        if cmd == "quit":
            break
        elif cmd in cmds:
            op.dispatch(cmds[cmd], {"query": arg})
            for i, p in enumerate((op.context.get("results") or [])[:10]):
                print(f"  [{i}] {p.get('title', '')[:55]} ({p.get('source')})")
        elif cmd == "select":
            results = op.context.get("results") or []
            idx = int(arg) if arg else 0
            if 0 <= idx < len(results):
                p = results[idx]
                op.dispatch("SELECT", {"id": p.get(
                    "id"), "source": p.get("source")})
                d = op.context.get("detail")
                if d:
                    print(f"Title: {d.get('title')}\nURL: {d.get('url')}")
        elif cmd == "clear":
            op.dispatch("CLEAR", {})


if __name__ == "__main__":
    main()
