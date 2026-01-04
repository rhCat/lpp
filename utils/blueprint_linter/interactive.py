#!/usr/bin/env python3
"""
L++ Blueprint Linter - Interactive Shell

A minimal CLI that drives compiled L++ operators for linting blueprints.
All logic lives in blueprints + COMPUTE units. This is just a thin caller.
"""

import sys
import json
from pathlib import Path
from src import LINT_REGISTRY
from frame_py.compiler import compile_blueprint

HERE = Path(__file__).parent


def compile_and_load(blueprint_json: str, registry: dict):
    """Compile blueprint and return operator with given COMPUTE registry."""
    import importlib.util

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


def main():
    print("\n  L++ Blueprint Linter\n")

    # Load compiled linter operator
    linter = compile_and_load(
        str(HERE / "blueprint_linter.json"), LINT_REGISTRY)

    # CLI arg - auto load and lint
    if len(sys.argv) > 1:
        bpPath = sys.argv[1]
        linter.dispatch("LOAD", {"path": bpPath})
        if linter.state == "loaded":
            linter.dispatch("LINT_ALL")

    ICONS = {
        "idle": "[.]",
        "loaded": "[+]",
        "linting": "[~]",
        "complete": "[v]",
        "error": "[!]"
    }

    while True:
        ctx = linter.context

        # Status line
        summary = ctx.get("summary", {})
        if linter.state == "complete":
            errC = summary.get("error", 0)
            warnC = summary.get("warning", 0)
            status = f"E:{errC} W:{warnC}"
        else:
            status = linter.state

        bpName = ctx.get("blueprint", {}).get("name", "none")
        print(f"\n  {ICONS.get(linter.state, '[?]')} {status} | {bpName}")

        # Show report if complete
        if linter.state == "complete" and ctx.get("report"):
            print(f"\n{ctx['report']}")

        # Show error if any
        if ctx.get("error"):
            print(f"\n  Error: {ctx['error']}")

        try:
            cmd = input("\n> ").strip().split(maxsplit=1)
        except (EOFError, KeyboardInterrupt):
            break

        if not cmd:
            continue

        action, arg = cmd[0].lower(), cmd[1] if len(cmd) > 1 else None

        # Command dispatch
        if action in ("q", "quit", "exit"):
            break
        elif action == "help":
            print("  Commands:")
            print("    load <path>   - Load a blueprint for linting")
            print("    lint          - Run all lint checks")
            print("    self          - Lint the linter itself")
            print("    report        - Show the lint report")
            print("    findings      - Show detailed findings")
            print("    metrics       - Show complexity metrics")
            print("    state         - Show full context state")
            print("    unload        - Unload current blueprint")
            print("    clear         - Clear error state")
            print("    quit          - Exit")
        elif action == "load" and arg:
            linter.dispatch("LOAD", {"path": arg})
        elif action == "self":
            linter.dispatch("LOAD", {"path": str(
                HERE / "blueprint_linter.json")})
            if linter.state == "loaded":
                linter.dispatch("LINT_ALL")
        elif action == "lint":
            linter.dispatch("LINT_ALL")
        elif action == "report":
            if ctx.get("report"):
                print(f"\n{ctx['report']}")
            else:
                print("  No report available. Run 'lint' first.")
        elif action == "findings":
            findings = ctx.get("findings", [])
            if findings:
                for f in findings:
                    sev = f.get("severity", "?")[0].upper()
                    code = f.get("code", "?")
                    msg = f.get("message", "")
                    print(f"  [{sev}] {code}: {msg}")
            else:
                print("  No findings.")
        elif action == "metrics":
            metrics = ctx.get("metrics", {})
            if metrics:
                print("  Metrics:")
                for k, v in metrics.items():
                    print(f"    {k}: {v}")
            else:
                print("  No metrics available.")
        elif action == "state":
            print(json.dumps(ctx, indent=2, default=str))
        elif action == "unload":
            linter.dispatch("UNLOAD")
        elif action == "clear":
            linter.dispatch("CLEAR")
        elif action == "back":
            linter.dispatch("BACK")
        else:
            print(f"  Unknown command: {action}")
            print("  Type 'help' for available commands.")

    print("  Goodbye!")


if __name__ == "__main__":
    main()
