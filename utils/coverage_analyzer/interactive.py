#!/usr/bin/env python3
"""
L++ Coverage Analyzer - Interactive Shell

A minimal CLI that drives the compiled coverage analyzer operator.
All logic lives in blueprints + COMPUTE units. This is just a thin caller.
"""

import sys
import json
from pathlib import Path
from src import COVERAGE_REGISTRY
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
    load <path>        Load a blueprint to analyze
    start              Start tracking mode
    import <path>      Import trace data from file

  Recording (in tracking mode):
    state <id>         Record state visit
    trans <id>         Record transition taken
    gate <id> [t|f]    Record gate evaluation (t=true, f=false)
    action <id>        Record action execution
    event <name>       Record event dispatch

  Analysis:
    analyze            Compute coverage metrics
    summary            Generate summary report
    detailed           Generate detailed report
    gap                Generate gap analysis report
    all                Generate all reports

  Export:
    html <path>        Export interactive HTML report
    json <path>        Export JSON coverage data

  Other:
    metrics            Show current metrics
    reset              Reset coverage data (keep blueprint)
    unload             Unload blueprint
    state              Show full operator state
    help               Show this help
    quit               Exit
""")


def print_metrics(ctx: dict):
    """Print coverage metrics."""
    metrics = ctx.get("metrics")
    if not metrics:
        print("  No metrics computed. Run 'analyze' first.")
        return

    print("\n  Coverage Metrics")
    print("  " + "=" * 50)
    print(f"  Overall: {metrics['overall_percentage']}%")
    print()
    print(f"  States:      {metrics['state_coverage']['percentage']:5.1f}%  "
          f"({metrics['state_coverage']['covered']}/{metrics['state_coverage']['total']})")
    print(f"  Transitions: {metrics['transition_coverage']['percentage']:5.1f}%  "
          f"({metrics['transition_coverage']['covered']}/{metrics['transition_coverage']['total']})")
    print(f"  Gates:       {metrics['gate_coverage']['percentage']:5.1f}%  "
          f"({metrics['gate_coverage']['covered']}/{metrics['gate_coverage']['total']})")
    print(f"  Actions:     {metrics['action_coverage']['percentage']:5.1f}%  "
          f"({metrics['action_coverage']['covered']}/{metrics['action_coverage']['total']})")
    print(f"  Events:      {metrics['event_coverage']['percentage']:5.1f}%  "
          f"({metrics['event_coverage']['covered']}/{metrics['event_coverage']['total']})")


def main():
    print("\n  L++ Coverage Analyzer\n")

    op = compile_and_load(str(HERE / "coverage_analyzer.json"), COVERAGE_REGISTRY)

    # CLI arg for initial blueprint
    if len(sys.argv) > 1:
        op.dispatch("LOAD", {"path": sys.argv[1]})

    ICONS = {
        "idle": "[ ]",
        "loaded": "[*]",
        "tracking": "[>]",
        "analyzing": "[~]",
        "reporting": "[+]",
        "error": "[!]"
    }

    while True:
        icon = ICONS.get(op.state, "[?]")
        bp = op.context.get("blueprint")
        bpName = bp.get("name", "?") if bp else "No blueprint"

        # Show coverage percentage if available
        metrics = op.context.get("metrics")
        covInfo = ""
        if metrics:
            covInfo = f" | Coverage: {metrics['overall_percentage']}%"

        print(f"\n  {icon} [{op.state}] {bpName}{covInfo}")

        try:
            cmd = input("\n> ").strip().split(maxsplit=2)
        except (EOFError, KeyboardInterrupt):
            break

        if not cmd:
            continue

        action = cmd[0].lower()
        arg = cmd[1] if len(cmd) > 1 else None
        arg2 = cmd[2] if len(cmd) > 2 else None

        if action in ("q", "quit", "exit"):
            break
        elif action == "help":
            print_help()

        # Loading
        elif action == "load" and arg:
            op.dispatch("LOAD", {"path": arg})
        elif action == "start":
            op.dispatch("START")
        elif action == "import" and arg:
            op.dispatch("IMPORT", {"path": arg})

        # Recording
        elif action == "state" and arg:
            op.dispatch("STATE", {"state_id": arg})
            print(f"  Recorded state: {arg}")
        elif action == "trans" and arg:
            op.dispatch("TRANSITION", {"transition_id": arg})
            print(f"  Recorded transition: {arg}")
        elif action == "gate" and arg:
            result = True if arg2 in (None, "t", "true", "1") else False
            op.dispatch("GATE", {"gate_id": arg, "result": result})
            print(f"  Recorded gate: {arg} = {result}")
        elif action == "action" and arg:
            op.dispatch("ACTION", {"action_id": arg})
            print(f"  Recorded action: {arg}")
        elif action == "event" and arg:
            op.dispatch("EVENT", {"event_name": arg})
            print(f"  Recorded event: {arg}")

        # Analysis
        elif action == "analyze":
            op.dispatch("ANALYZE")
            print_metrics(op.context)
        elif action == "summary":
            op.dispatch("SUMMARY")
            report = op.context.get("summary_report")
            if report:
                print(f"\n{report}")
        elif action == "detailed":
            op.dispatch("DETAILED")
            report = op.context.get("detailed_report")
            if report:
                print(f"\n{report}")
        elif action == "gap":
            op.dispatch("GAP")
            report = op.context.get("gap_report")
            if report:
                print(f"\n{report}")
        elif action == "all":
            op.dispatch("ALL_REPORTS")
            for key in ["summary_report", "detailed_report", "gap_report"]:
                report = op.context.get(key)
                if report:
                    print(f"\n{report}")

        # Export
        elif action == "html":
            path = arg or f"./coverage_{op.context.get('blueprint', {}).get('id', 'report')}.html"
            op.dispatch("EXPORT_HTML", {"path": path})
            outPath = op.context.get("export_path")
            if outPath:
                print(f"  Exported HTML to: {outPath}")
            else:
                print("  Export failed. Run 'analyze' first.")
        elif action == "json":
            path = arg or f"./coverage_{op.context.get('blueprint', {}).get('id', 'report')}.json"
            op.dispatch("EXPORT_JSON", {"path": path})
            outPath = op.context.get("export_path")
            if outPath:
                print(f"  Exported JSON to: {outPath}")
            else:
                print("  Export failed. Run 'analyze' first.")

        # Other
        elif action == "metrics":
            print_metrics(op.context)
        elif action == "reset":
            op.dispatch("RESET")
            print("  Coverage data reset")
        elif action == "unload":
            op.dispatch("UNLOAD")
            print("  Blueprint unloaded")
        elif action == "back":
            op.dispatch("BACK")
        elif action == "clear":
            op.dispatch("CLEAR")
        elif action in ("ctx", "context", "state"):
            ctx = {k: v for k, v in op.context.items()
                   if k not in ("blueprint", "html_report", "json_report",
                               "summary_report", "detailed_report", "gap_report")}
            print(json.dumps(ctx, indent=2, default=str))
        elif action == "hits":
            print("\n  State Hits:", op.context.get("state_hits", {}))
            print("  Transition Hits:", op.context.get("transition_hits", {}))
            print("  Gate Hits:", op.context.get("gate_hits", {}))
            print("  Action Hits:", op.context.get("action_hits", {}))
        else:
            print(f"  Unknown command: {action}. Type 'help' for commands.")

    print("  Goodbye!")


if __name__ == "__main__":
    main()
