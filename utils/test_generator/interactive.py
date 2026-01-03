#!/usr/bin/env python3
"""
L++ Test Case Generator - Interactive Shell

A minimal CLI that drives the compiled test generator operator.
All logic lives in blueprints + COMPUTE units. This is just a thin caller.
"""

import sys
import json
from pathlib import Path
from src import TEST_REGISTRY
from frame_py.compiler import compile_blueprint

HERE = Path(__file__).parent


def compile_and_load(blueprint_json: str, registry: dict):
    """Compile blueprint and return operator with given COMPUTE registry."""
    import importlib.util

    out = HERE / "results" / f"{Path(blueprint_json).stem}_compiled.py"
    out.parent.mkdir(exist_ok=True)
    compile_blueprint(blueprint_json, str(out))

    spec = importlib.util.spec_from_file_location("op", out)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)

    reg = {tuple(k.split(":")): fn for k, fn in registry.items()}
    return mod.create_operator(reg)


def print_help():
    """Print available commands."""
    print("""
  Commands:
    load <path>      Load a blueprint to generate tests for
    analyze          Analyze blueprint structure (build graph, find paths)
    generate         Generate all test types
    generate-all     Load, analyze, and generate in one step

    format json      Format tests as L++ JSON test suite
    format pytest    Format tests as Python pytest module
    export <path>    Export formatted tests to file

    coverage         Show coverage report
    paths            Show discovered paths
    tests            Show generated tests (summary)
    state            Show full operator state

    back             Go back to previous state
    reset            Reset to idle state
    help             Show this help
    quit             Exit
""")


def print_coverage(ctx: dict):
    """Print coverage report."""
    cov = ctx.get("coverage_report")
    if not cov:
        print("  No coverage data. Run 'generate' first.")
        return

    print("\n  Coverage Report")
    print("  " + "=" * 50)
    print(f"  Total Tests: {cov['total_tests']}")
    print("\n  By Type:")
    for ttype, count in cov["by_type"].items():
        print(f"    {ttype:20} : {count}")

    print("\n  State Coverage:")
    sc = cov["state_coverage"]
    print(f"    {sc['covered']}/{sc['total']} ({sc['percentage']:.1f}%)")

    print("\n  Transition Coverage:")
    tc = cov["transition_coverage"]
    print(f"    {tc['covered']}/{tc['total']} ({tc['percentage']:.1f}%)")

    print("\n  Gate Coverage:")
    gc = cov["gate_coverage"]
    print(f"    {gc['covered']}/{gc['total']} ({gc['percentage']:.1f}%)")


def print_paths(ctx: dict):
    """Print discovered paths."""
    paths = ctx.get("paths", [])
    if not paths:
        print("  No paths found. Run 'analyze' first.")
        return

    print(f"\n  Discovered Paths ({len(paths)} total)")
    print("  " + "=" * 50)
    for i, p in enumerate(paths[:10]):
        stateStr = " -> ".join(p["states"][:5])
        if len(p["states"]) > 5:
            stateStr += f" ... (+{len(p['states'])-5} more)"
        complete = "[complete]" if p.get("is_complete") else "[partial]"
        print(f"  {i+1:3}. {stateStr} {complete}")

    if len(paths) > 10:
        print(f"\n  ... and {len(paths)-10} more paths")


def print_tests(ctx: dict):
    """Print test summary."""
    tests = ctx.get("all_tests", [])
    if not tests:
        print("  No tests generated. Run 'generate' first.")
        return

    print(f"\n  Generated Tests ({len(tests)} total)")
    print("  " + "=" * 50)

    byType = {}
    for t in tests:
        ttype = t.get("type", "unknown")
        byType.setdefault(ttype, []).append(t)

    for ttype, typeTests in byType.items():
        print(f"\n  {ttype} ({len(typeTests)} tests):")
        for t in typeTests[:3]:
            desc = t.get("description", "")[:50]
            print(f"    - {t['id']}: {desc}")
        if len(typeTests) > 3:
            print(f"    ... and {len(typeTests)-3} more")


def main():
    print("\n  L++ Test Case Generator\n")

    op = compile_and_load(str(HERE / "test_generator.json"), TEST_REGISTRY)

    # CLI arg for initial blueprint
    if len(sys.argv) > 1:
        op.dispatch("LOAD", {"path": sys.argv[1]})

    ICONS = {
        "idle": "[ ]",
        "loaded": "[*]",
        "analyzing": "[~]",
        "generating": "[~]",
        "complete": "[+]",
        "error": "[!]"
    }

    while True:
        icon = ICONS.get(op.state, "[?]")
        bpName = op.context.get("blueprint", {})
        if bpName:
            bpName = bpName.get("name", "?")
        else:
            bpName = "No blueprint"

        testCount = len(op.context.get("all_tests", []) or [])
        print(f"\n  {icon} [{op.state}] {bpName}")
        if testCount:
            print(f"      Tests: {testCount}")

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
            print_help()
        elif action == "load" and arg:
            op.dispatch("LOAD", {"path": arg})
        elif action == "analyze":
            op.dispatch("ANALYZE")
        elif action == "generate":
            op.dispatch("GENERATE")
            op.dispatch("AUTO")  # Auto-combine
        elif action in ("generate-all", "genall"):
            if arg:
                op.dispatch("LOAD", {"path": arg})
            op.dispatch("GENERATE_ALL")
            op.dispatch("AUTO")
        elif action == "format":
            if arg == "json":
                op.dispatch("FORMAT_JSON")
                print("\n  Formatted as JSON")
            elif arg == "pytest":
                op.dispatch("FORMAT_PYTEST")
                print("\n  Formatted as pytest")
            else:
                print("  Usage: format json|pytest")
        elif action == "export" and arg:
            op.dispatch("EXPORT", {"path": arg})
            outPath = op.context.get("output_path")
            if outPath:
                print(f"  Exported to: {outPath}")
            else:
                print("  Export failed. Format tests first.")
        elif action == "coverage":
            print_coverage(op.context)
        elif action == "paths":
            print_paths(op.context)
        elif action == "tests":
            print_tests(op.context)
        elif action == "state":
            ctx = {k: v for k, v in op.context.items()
                   if k not in ("blueprint", "formatted_output")}
            print(json.dumps(ctx, indent=2, default=str))
        elif action == "output":
            out = op.context.get("formatted_output")
            if out:
                print(out[:2000])
                if len(out) > 2000:
                    print(f"\n... ({len(out)} chars total)")
            else:
                print("  No output. Run 'format' first.")
        elif action == "back":
            op.dispatch("BACK")
        elif action == "reset":
            op.dispatch("RESET")
        else:
            print(f"  Unknown command: {action}. Type 'help' for commands.")

    print("  Goodbye!")


if __name__ == "__main__":
    main()
