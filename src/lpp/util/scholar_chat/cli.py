#!/usr/bin/env python3
"""Scholar Chatbot CLI - per build_rules.md: < 50 lines."""
from src.scholar_compute import COMPUTE_REGISTRY
from frame_py.compiler import compile_blueprint
from pathlib import Path
import sys
sys.path.insert(0, "../../src")
HERE = Path(__file__).parent


def load():
    import importlib.util
    out = HERE / "results/scholar_chat_compiled.py"
    out.parent.mkdir(exist_ok=True)
    compile_blueprint(str(HERE / "scholar_chat.json"), str(out))
    spec = importlib.util.spec_from_file_location("op", out)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod.create_operator({tuple(k.split(":")): fn for k, fn in COMPUTE_REGISTRY.items()})


def main():
    op = load()
    op.dispatch("INIT", {})
    print("ScholarChat: search <query> | select <0,1,2> | ask <question> | back | quit")
    while True:
        try:
            line = input(f"[{op.state}]> ").strip()
        except (EOFError, KeyboardInterrupt):
            break
        if not line:
            continue
        parts = line.split(maxsplit=1)
        cmd, arg = parts[0].lower(), parts[1] if len(parts) > 1 else ""
        if cmd == "quit":
            break
        elif cmd == "search":
            op.dispatch("SEARCH", {"query": arg})
            op.dispatch("DONE", {})
            for i, p in enumerate((op.context.get("searchResults") or [])[:10]):
                print(f"  [{i}] {p.get('title', '')[:55]} ({p.get('source')})")
        elif cmd == "select":
            indices = [int(x.strip())
                       for x in arg.split(",")] if arg else [0, 1, 2]
            op.dispatch("SELECT", {"indices": indices})
            op.dispatch("DONE", {})
            syn = op.context.get("synthesis", "")
            if syn:
                print(f"\n{syn[:1500]}{'...' if len(syn) > 1500 else ''}\n")
            for q in (op.context.get("followUpQuestions") or []):
                print(f"  Q: {q}")
        elif cmd == "ask":
            op.dispatch("ASK", {"question": arg})
            print(f"\n{op.context.get('synthesis', '')}\n")
        elif cmd == "back":
            op.dispatch("BACK", {})
        elif cmd == "reset":
            op.dispatch("RESET", {})
        err = op.context.get("error")
        if err:
            print(f"  Error: {err}")
            op.dispatch("RETRY", {})


if __name__ == "__main__":
    main()
