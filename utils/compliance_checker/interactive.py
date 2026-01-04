#!/usr/bin/env python3
"""
L++ Compliance Checker - Interactive Shell

A minimal CLI that drives the compiled compliance checker operator.
All logic lives in blueprints + COMPUTE units. This is just a thin caller.
"""

import sys
import json
from pathlib import Path

from src import COMPLIANCE_REGISTRY
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


def print_report_summary(report: dict):
    """Print a formatted report summary to console."""
    print("\n" + "=" * 60)
    print(
        f"  COMPLIANCE REPORT: {report.get('blueprint', {}).get('name', 'N/A')}")
    print("=" * 60)

    score = report.get("score", 0)
    status = report.get("status", "N/A")
    statusIcon = "[PASS]" if status == "PASS" else "[WARN]" if status == "WARNING" else "[FAIL]"

    print(f"\n  Score: {score}%  {statusIcon}")

    summary = report.get("summary", {})
    print(f"\n  Total Checks: {summary.get('total_checks', 0)}")
    print(f"  Passed: {summary.get('passed', 0)}")
    print(f"  Failed: {summary.get('failed', 0)}")

    byS = summary.get("by_severity", {})
    print(f"\n  Errors: {byS.get('errors', 0)}")
    print(f"  Warnings: {byS.get('warnings', 0)}")

    # Show errors and warnings
    findingsByS = report.get("findings_by_severity", {})

    if findingsByS.get("error"):
        print("\n  --- ERRORS ---")
        for f in findingsByS["error"][:5]:
            print(f"  [!] {f.get('policy_id')}: {f.get('message')}")
        if len(findingsByS["error"]) > 5:
            print(f"  ... and {len(findingsByS['error']) - 5} more")

    if findingsByS.get("warning"):
        print("\n  --- WARNINGS ---")
        for f in findingsByS["warning"][:5]:
            print(f"  [?] {f.get('policy_id')}: {f.get('message')}")
        if len(findingsByS["warning"]) > 5:
            print(f"  ... and {len(findingsByS['warning']) - 5} more")

    print("\n" + "=" * 60)


def main():
    print("\n  L++ Compliance Checker\n")

    cc = compile_and_load(
        str(HERE / "compliance_checker.json"), COMPLIANCE_REGISTRY)

    # Default policies directory
    defaultPolicies = HERE / "policies"

    # CLI arg for blueprint
    if len(sys.argv) > 1:
        cc.dispatch("LOAD_BLUEPRINT", {"path": sys.argv[1]})

    ICONS = {
        "idle": "[.]",
        "blueprint_loaded": "[B]",
        "ready": "[R]",
        "checking": "[C]",
        "report_ready": "[!]",
        "error": "[X]"
    }

    while True:
        state = cc.state
        ctx = cc.context

        # Status line
        icon = ICONS.get(state, "[?]")
        bpName = ctx.get("blueprint_name", "None")
        polCount = len(ctx.get("policies", []) or [])
        score = ctx.get("score")

        statusLine = f"{icon} {state}"
        if bpName and bpName != "None":
            statusLine += f" | Blueprint: {bpName}"
        if polCount > 0:
            statusLine += f" | Policies: {polCount}"
        if score is not None:
            statusLine += f" | Score: {score}%"

        print(f"\n  {statusLine}")

        if ctx.get("error"):
            print(f"  Error: {ctx['error']}")

        try:
            cmd = input("\n> ").strip().split(maxsplit=1)
        except (EOFError, KeyboardInterrupt):
            break

        if not cmd:
            continue

        action, arg = cmd[0].lower(), cmd[1] if len(cmd) > 1 else None

        if action in ("q", "quit", "exit"):
            break

        elif action == "help":
            print("\n  Commands:")
            print("    load <path>     - Load a blueprint to check")
            print("    policies [dir]  - Load policies (default: ./policies)")
            print("    policy <path>   - Load a single policy file")
            print("    check           - Run compliance check")
            print("    report          - Show report summary")
            print("    export [path]   - Export report (json/md/txt)")
            print("    findings        - Show all findings")
            print("    score           - Show compliance score")
            print("    state           - Show full context state")
            print("    back            - Go back to previous state")
            print("    unload          - Unload blueprint and policies")
            print("    clear           - Clear error state")
            print("    q/quit          - Exit")

        elif action == "load" and arg:
            cc.dispatch("LOAD_BLUEPRINT", {"path": arg})

        elif action == "policies":
            polDir = arg if arg else str(defaultPolicies)
            cc.dispatch("LOAD_POLICIES", {"dir_path": polDir})

        elif action == "policy" and arg:
            cc.dispatch("LOAD_POLICY", {"path": arg})

        elif action == "check":
            cc.dispatch("CHECK")
            # Auto-generate report
            if cc.state == "checking":
                cc.dispatch("AUTO")

        elif action == "report":
            report = ctx.get("report")
            if report:
                print_report_summary(report)
            else:
                print("  No report available. Run 'check' first.")

        elif action == "export":
            if not ctx.get("report"):
                print("  No report to export. Run 'check' first.")
            else:
                path = arg or f"./{ctx.get('blueprint', {}).get('id', 'blueprint')}_compliance.json"
                fmt = "json"
                if path.endswith(".md"):
                    fmt = "md"
                elif path.endswith(".txt"):
                    fmt = "txt"
                cc.dispatch("EXPORT", {"path": path, "format": fmt})
                if ctx.get("export_path"):
                    print(f"  Exported to: {ctx['export_path']}")

        elif action == "findings":
            findings = ctx.get("findings", [])
            if not findings:
                print("  No findings. Run 'check' first.")
            else:
                for f in findings:
                    icon = "[+]" if f.get("passed") else "[-]"
                    sev = f.get("severity", "info")[0].upper()
                    print(
                        f"  {icon}[{sev}] {f.get('policy_id')}: {f.get('message')}")

        elif action == "score":
            score = ctx.get("score")
            if score is not None:
                print(f"  Compliance Score: {score}%")
            else:
                print("  No score available. Run 'check' first.")

        elif action == "state":
            print(json.dumps(ctx, indent=2, default=str))

        elif action == "back":
            cc.dispatch("BACK")

        elif action == "unload":
            cc.dispatch("UNLOAD")

        elif action == "clear":
            cc.dispatch("CLEAR")

        else:
            print(f"  Unknown command: {action}. Type 'help' for commands.")

    print("  Goodbye!")


if __name__ == "__main__":
    main()
