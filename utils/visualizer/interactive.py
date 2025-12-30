#!/usr/bin/env python3
"""
L++ Visualizer - Interactive Shell

A minimal CLI that drives compiled L++ operators.
All logic lives in blueprints + COMPUTE units. This is just a thin caller.
"""

import sys
import json
from pathlib import Path
# Import from src package (handles sys.path setup)
from src import VIZ_REGISTRY, README_REGISTRY
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
    print("\n🔮 L++ Visualizer\n")

    # Load compiled operators
    viz = compile_and_load(str(HERE / "visualizer.json"), VIZ_REGISTRY)
    rdm = compile_and_load(
        str(HERE / "readme_generator.json"), README_REGISTRY)

    # CLI arg
    if len(sys.argv) > 1:
        viz.dispatch("LOAD", {"path": sys.argv[1]})

    ICONS = {"idle": "📂", "loaded": "✅", "viewing": "🔍", "error": "❌"}

    while True:
        print(f"\n  {ICONS.get(viz.state, '❓')} [{viz.state}] {viz.display()}")
        if viz.state == "viewing" and viz.context.get("output"):
            print(f"\n{viz.context['output']}")

        try:
            cmd = input("\n> ").strip().split(maxsplit=1)
        except (EOFError, KeyboardInterrupt):
            break

        if not cmd:
            continue

        action, arg = cmd[0].lower(), cmd[1] if len(cmd) > 1 else None

        # Simple command -> event dispatch
        if action in ("q", "quit"):
            break
        elif action == "help":
            print(
                "  load <path> "
                "| self | calc | view | graph | table | mermaid"
            )
            print(
                "  export <path> | select <id> | +/- | "
                "gates | actions | back | state"
            )
        elif action == "load" and arg:
            viz.dispatch("LOAD", {"path": arg})
        elif action == "self":
            viz.dispatch("LOAD", {"path": str(HERE / "visualizer.json")})
        elif action == "calc":
            viz.dispatch("LOAD", {"path": str(
                HERE.parent / "math_compute" / "math_compute.json")})
        elif action == "view":
            viz.dispatch("VIEW")
        elif action == "graph":
            viz.dispatch("VIEW_GRAPH")
        elif action == "table":
            viz.dispatch("VIEW_TABLE")
        elif action == "mermaid":
            viz.dispatch("VIEW_MERMAID")
        elif action == "export" and viz.context.get("blueprint"):
            path = arg or f"./{viz.context['blueprint']['id']}_README.md"
            rdm._state, rdm.context = "init", {}
            rdm.dispatch(
                "GENERATE", {
                    "blueprint": viz.context["blueprint"],
                    "path": path
                }
            )
            for _ in range(5):
                rdm.dispatch("NEXT")
            print(f"  📄 {rdm.context.get('result', 'done')}")
        elif action == "select" and arg:
            viz.dispatch("SELECT", {"node_id": arg})
        elif action == "+":
            viz.dispatch("ZOOM_IN")
        elif action == "-":
            viz.dispatch("ZOOM_OUT")
        elif action == "gates":
            viz.dispatch("TOGGLE_GATES")
        elif action == "actions":
            viz.dispatch("TOGGLE_ACTIONS")
        elif action == "back":
            viz.dispatch("BACK")
        elif action == "unload":
            viz.dispatch("UNLOAD")
        elif action == "state":
            print(json.dumps(viz.context, indent=2, default=str))
        else:
            print(f"  Unknown: {action}")

    print("  Goodbye!")


if __name__ == "__main__":
    main()
