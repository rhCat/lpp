#!/usr/bin/env python3
"""
L++ Schema Migrator - Interactive Shell

A minimal CLI that drives compiled L++ operators for schema migration.
All logic lives in blueprints + COMPUTE units. This is just a thin caller.
"""

import sys
import json
from pathlib import Path
from src import MIGRATE_REGISTRY
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
    print("\n  L++ Schema Migrator\n")

    # Load compiled migrator operator
    migrator = compile_and_load(
        str(HERE / "schema_migrator.json"), MIGRATE_REGISTRY
    )

    # CLI arg - auto load blueprint
    if len(sys.argv) > 1:
        bpPath = sys.argv[1]
        migrator.dispatch("LOAD", {"path": bpPath})

        # If second arg is --preview or --migrate
        if len(sys.argv) > 2:
            if sys.argv[2] == "--preview":
                migrator.dispatch("PREVIEW_ALL")
            elif sys.argv[2] == "--migrate":
                migrator.dispatch("MIGRATE_ALL")

    ICONS = {
        "idle": "[.]",
        "loaded": "[+]",
        "planning": "[~]",
        "planned": "[P]",
        "migrating": "[M]",
        "validating": "[V]",
        "complete": "[v]",
        "batch_mode": "[B]",
        "error": "[!]"
    }

    while True:
        ctx = migrator.context

        # Status line
        srcVer = ctx.get("source_version", "?")
        tgtVer = ctx.get("target_version", "?")
        bpPath = ctx.get("blueprint_path", "none")

        if migrator.state == "complete":
            dryRun = ctx.get("dry_run_mode", False)
            mode = "preview" if dryRun else "migrated"
            status = f"{srcVer} -> {tgtVer} ({mode})"
        elif migrator.state == "planned":
            planLen = len(ctx.get("migration_plan", []))
            status = f"{srcVer} -> {tgtVer} ({planLen} steps)"
        elif migrator.state == "loaded":
            status = f"schema: {srcVer}"
        else:
            status = migrator.state

        print(f"\n  {ICONS.get(migrator.state, '[?]')} {status}")
        if bpPath and bpPath != "none":
            print(f"      {Path(bpPath).name}")

        # Show report if complete
        if migrator.state == "complete" and ctx.get("report"):
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
            print_help()
        elif action == "load" and arg:
            migrator.dispatch("LOAD", {"path": arg})
        elif action == "self":
            migrator.dispatch("LOAD", {"path": str(HERE / "schema_migrator.json")})
        elif action == "detect":
            if ctx.get("blueprint"):
                print(f"  Detected version: {ctx.get('source_version', '?')}")
            else:
                print("  No blueprint loaded")
        elif action == "list":
            migs = ctx.get("available_migrations", [])
            if migs:
                print("  Available Migrations:")
                for m in migs:
                    print(f"    {m['from']} -> {m['to']}: {m['description']}")
            else:
                print("  No migrations available")
        elif action == "plan":
            if arg:
                migrator.dispatch("PLAN_TO", {"version": f"lpp/v{arg}"})
            else:
                migrator.dispatch("PLAN_LATEST")
        elif action == "preview":
            if migrator.state == "planned":
                migrator.dispatch("DRY_RUN")
            elif migrator.state == "loaded":
                migrator.dispatch("PREVIEW_ALL")
            else:
                print("  Load a blueprint first")
        elif action == "migrate":
            if migrator.state == "planned":
                migrator.dispatch("EXECUTE")
                if migrator.state == "migrating":
                    migrator.dispatch("VALIDATE")
                    if migrator.state == "validating":
                        migrator.dispatch("FINALIZE")
            elif migrator.state == "loaded":
                migrator.dispatch("MIGRATE_ALL")
            else:
                print("  Load a blueprint first")
        elif action == "validate":
            if migrator.state == "migrating":
                migrator.dispatch("VALIDATE")
            else:
                print("  Run 'migrate' first to have a blueprint to validate")
        elif action == "export" and arg:
            migrator.dispatch("EXPORT", {"path": arg})
            if not ctx.get("error"):
                print(f"  Exported to: {arg}")
        elif action == "report":
            if ctx.get("report"):
                print(f"\n{ctx['report']}")
            else:
                print("  No report available. Run 'preview' or 'migrate' first.")
        elif action == "changes":
            changes = ctx.get("migration_changes", [])
            if changes:
                print("  Planned Changes:")
                for ch in changes:
                    print(f"    [{ch.get('type', '?')}] {ch.get('description', '')}")
            else:
                print("  No changes planned")
        elif action == "state":
            print(json.dumps(ctx, indent=2, default=str))
        elif action == "diff":
            # Show diff between original and migrated
            orig = ctx.get("blueprint", {})
            migr = ctx.get("migrated_blueprint", {})
            if orig and migr:
                print("  Original $schema:", orig.get("$schema", "?"))
                print("  Migrated $schema:", migr.get("$schema", "?"))
                _show_diff(orig, migr)
            else:
                print("  No diff available")
        elif action == "batch" and arg:
            # Parse paths from arg (comma or space separated)
            paths = [p.strip() for p in arg.replace(",", " ").split()]
            migrator.dispatch("BATCH", {"paths": paths})
            migrator.dispatch("RUN_BATCH")
        elif action == "back":
            migrator.dispatch("BACK")
        elif action == "unload":
            migrator.dispatch("UNLOAD")
        elif action == "clear":
            migrator.dispatch("CLEAR")
        else:
            print(f"  Unknown command: {action}")
            print("  Type 'help' for available commands.")

    print("  Goodbye!")


def print_help():
    print("  Commands:")
    print("    load <path>      - Load a blueprint for migration")
    print("    self             - Load the schema migrator itself")
    print("    detect           - Show detected schema version")
    print("    list             - List available migrations")
    print("    plan [version]   - Plan migration (to version or latest)")
    print("    preview          - Dry run - show changes without applying")
    print("    migrate          - Apply migration")
    print("    validate         - Validate migrated blueprint")
    print("    export <path>    - Export migrated blueprint to file")
    print("    report           - Show migration report")
    print("    changes          - Show planned changes")
    print("    diff             - Show diff between original and migrated")
    print("    batch <paths>    - Batch migrate multiple blueprints")
    print("    state            - Show full context state")
    print("    back             - Go back to previous state")
    print("    unload           - Unload current blueprint")
    print("    clear            - Clear error state")
    print("    quit             - Exit")


def _show_diff(orig: dict, migr: dict, path: str = "", indent: int = 4):
    """Show simple diff between two dicts."""
    prefix = " " * indent

    # Added fields
    for key in migr:
        if key not in orig:
            print(f"{prefix}+ {path}{key}: {_truncate(migr[key])}")

    # Removed fields
    for key in orig:
        if key not in migr:
            print(f"{prefix}- {path}{key}: {_truncate(orig[key])}")

    # Changed fields
    for key in orig:
        if key in migr and orig[key] != migr[key]:
            # Recurse for dicts
            if isinstance(orig[key], dict) and isinstance(migr[key], dict):
                _show_diff(orig[key], migr[key], f"{path}{key}.", indent)
            else:
                print(f"{prefix}~ {path}{key}:")
                print(f"{prefix}    was: {_truncate(orig[key])}")
                print(f"{prefix}    now: {_truncate(migr[key])}")


def _truncate(val, maxlen=50):
    """Truncate value for display."""
    s = str(val)
    if len(s) > maxlen:
        return s[:maxlen] + "..."
    return s


if __name__ == "__main__":
    main()
