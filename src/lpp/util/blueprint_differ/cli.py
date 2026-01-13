#!/usr/bin/env python3
"""
L++ Blueprint Differ - Interactive Shell

A minimal CLI that drives compiled L++ operators for diffing/merging blueprints.
All logic lives in blueprints + COMPUTE units. This is just a thin caller.
"""

import sys
import json
from pathlib import Path
from src import DIFF_REGISTRY
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
    print("\n  L++ Blueprint Diff & Merge Tool\n")

    # Load compiled differ operator
    differ = compile_and_load(
        str(HERE / "blueprint_differ.json"), DIFF_REGISTRY
    )

    # CLI args - auto diff if two paths provided
    if len(sys.argv) >= 3:
        leftPath = sys.argv[1]
        rightPath = sys.argv[2]
        differ.dispatch("LOAD_LEFT", {"path": leftPath})
        if differ.state == "left_loaded":
            differ.dispatch("LOAD_RIGHT", {"path": rightPath})
        if differ.state == "ready":
            differ.dispatch("DIFF_ALL")

    ICONS = {
        "idle": "[.]",
        "left_loaded": "[<]",
        "ready": "[=]",
        "diffing": "[~]",
        "diff_complete": "[v]",
        "merging": "[M]",
        "merge_complete": "[+]",
        "conflict": "[!]",
        "error": "[X]"
    }

    while True:
        ctx = differ.context

        # Status line
        state = differ.state
        icon = ICONS.get(state, "[?]")

        if state == "diff_complete":
            summary = ctx.get("diff_result", {}).get("summary", {})
            status = (f"+{summary.get('added', 0)} "
                      f"-{summary.get('removed', 0)} "
                      f"~{summary.get('modified', 0)}")
        elif state == "conflict":
            conflicts = ctx.get("conflicts", [])
            status = f"{len(conflicts)} conflicts"
        elif state == "merge_complete":
            status = f"merged ({ctx.get('merge_strategy', 'auto')})"
        else:
            status = state

        leftName = ctx.get("path_left", "none")
        if leftName and len(leftName) > 30:
            leftName = "..." + leftName[-27:]
        rightName = ctx.get("path_right", "none")
        if rightName and len(rightName) > 30:
            rightName = "..." + rightName[-27:]

        print(f"\n  {icon} {status}")
        if ctx.get("path_left"):
            print(f"      L: {leftName}")
        if ctx.get("path_right"):
            print(f"      R: {rightName}")

        # Show formatted diff if available
        if state == "diff_complete" and ctx.get("formatted_diff"):
            print(f"\n{ctx['formatted_diff']}")

        # Show conflicts if in conflict state
        if state == "conflict":
            conflicts = ctx.get("conflicts", [])
            print("\n  Conflicts:")
            for i, c in enumerate(conflicts):
                print(f"    {i+1}. [{c['element_type']}] {c['key']}")
                print(f"       {c.get('reason', '')}")

        # Show export path if available
        if ctx.get("export_path"):
            print(f"\n  Exported to: {ctx['export_path']}")

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
            print_help()
        elif action == "left" and arg:
            differ.dispatch("LOAD_LEFT", {"path": arg})
        elif action == "right" and arg:
            differ.dispatch("LOAD_RIGHT", {"path": arg})
        elif action == "base" and arg:
            differ.dispatch("LOAD_BASE", {"path": arg})
        elif action == "diff":
            differ.dispatch("DIFF_ALL")
        elif action == "summary":
            differ.dispatch("SHOW_SUMMARY")
        elif action == "unified":
            differ.dispatch("SHOW_UNIFIED")
        elif action == "patch":
            differ.dispatch("SHOW_PATCH")
            if ctx.get("json_patch"):
                print("\n  JSON Patch (RFC 6902):")
                print(ctx.get("formatted_diff", ""))
        elif action == "merge":
            differ.dispatch("MERGE")
            # Auto-continue if no conflicts
            if differ.state == "merging":
                newCtx = differ.context
                if not newCtx.get("conflicts"):
                    differ.dispatch("MERGE_AUTO")
                else:
                    differ.dispatch("CONFLICT_DETECTED")
        elif action == "merge_left":
            differ.dispatch("MERGE_LEFT")
        elif action == "merge_right":
            differ.dispatch("MERGE_RIGHT")
        elif action == "take_left":
            differ.dispatch("TAKE_LEFT")
        elif action == "take_right":
            differ.dispatch("TAKE_RIGHT")
        elif action == "export" and arg:
            differ.dispatch("EXPORT", {"path": arg})
        elif action == "show":
            if ctx.get("formatted_diff"):
                print(f"\n{ctx['formatted_diff']}")
            elif ctx.get("merged_blueprint"):
                print("\n  Merged Blueprint:")
                print(json.dumps(ctx["merged_blueprint"], indent=2))
            else:
                print("  No diff or merged result available.")
        elif action == "merged":
            if ctx.get("merged_blueprint"):
                print("\n  Merged Blueprint:")
                print(json.dumps(ctx["merged_blueprint"], indent=2))
            else:
                print("  No merged blueprint available.")
        elif action == "state":
            print(f"\n  State: {differ.state}")
            print(json.dumps(ctx, indent=2, default=str))
        elif action == "reset":
            differ.dispatch("RESET")
        elif action == "back":
            differ.dispatch("BACK")
        elif action == "clear":
            differ.dispatch("CLEAR")
        elif action == "self":
            # Diff the differ against itself (should show no changes)
            differ.dispatch("LOAD_LEFT",
                            {"path": str(HERE / "blueprint_differ.json")})
            if differ.state == "left_loaded":
                differ.dispatch("LOAD_RIGHT",
                                {"path": str(HERE / "blueprint_differ.json")})
            if differ.state == "ready":
                differ.dispatch("DIFF_ALL")
        else:
            print(f"  Unknown command: {action}")
            print("  Type 'help' for available commands.")

    print("  Goodbye!")


def print_help():
    print("""
  Commands:
    Loading:
      left <path>     - Load left (base) blueprint
      right <path>    - Load right (target) blueprint
      base <path>     - Load common ancestor for 3-way merge

    Diffing:
      diff            - Compute semantic diff
      summary         - Show diff summary
      unified         - Show unified diff format
      patch           - Show JSON patch (RFC 6902)
      show            - Display current diff/merge result

    Merging:
      merge           - Start merge (detects conflicts)
      merge_left      - Force merge, prefer left on conflicts
      merge_right     - Force merge, prefer right on conflicts
      take_left       - Resolve conflicts by taking left
      take_right      - Resolve conflicts by taking right
      merged          - Show merged blueprint
      export <path>   - Export merged blueprint to file

    Navigation:
      back            - Go back to previous state
      reset           - Reset to ready state
      clear           - Clear all loaded blueprints
      state           - Show full context state

    Other:
      self            - Diff the differ against itself
      help            - Show this help
      quit            - Exit
""")


if __name__ == "__main__":
    main()
