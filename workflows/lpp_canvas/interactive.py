#!/usr/bin/env python3
"""L++ Canvas CLI - per build_rules.md: < 50 lines."""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent.parent.parent / "src"))
from src.canvas_compute import COMPUTE_REGISTRY
from frame_py.compiler import compile_blueprint

HERE = Path(__file__).parent


def load():
    import importlib.util
    out = HERE / "results/lpp_canvas_compiled.py"
    out.parent.mkdir(exist_ok=True)
    compile_blueprint(str(HERE / "lpp_canvas.json"), str(out))
    spec = importlib.util.spec_from_file_location("op", out)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    reg = {tuple(k.split(":")): fn for k, fn in COMPUTE_REGISTRY.items()}
    return mod.create_operator(reg)


def main():
    op = load()
    print("L++ Canvas: new | load <path> | select <node> | edit | validate |")
    print("            analyze | simulate | cluster | review | generate | quit")
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
        elif cmd == "new":
            op.dispatch("NEW", {})
        elif cmd == "load":
            op.dispatch("LOAD", {"blueprint_path": arg})
        elif cmd == "select":
            t, n = (arg.split() + ["state"])[:2]
            op.dispatch("SELECT", {"selected_node": t, "selected_type": n})
        elif cmd == "validate":
            op.dispatch("VALIDATE", {})
            print(f"TLC: {'PASS' if op.context.get('tlc_passed') else 'FAIL'}")
        elif cmd == "analyze":
            op.dispatch("ANALYZE", {})
            print(f"Paths: {op.context.get('path_count')}, States: {op.context.get('state_count')}")
        elif cmd == "simulate":
            op.dispatch("SIMULATE", {})
        elif cmd == "step":
            op.dispatch("STEP", {"prompt": arg})
        elif cmd == "cluster":
            op.dispatch("CLUSTER", {})
        elif cmd == "review":
            op.dispatch("REVIEW", {})
        elif cmd == "generate":
            op.dispatch("GENERATE", {})
        elif cmd == "done":
            op.dispatch("DONE", {})
        elif cmd == "context":
            for k, v in op.context.items():
                if v is not None:
                    print(f"  {k}: {str(v)[:60]}")


if __name__ == "__main__":
    main()
