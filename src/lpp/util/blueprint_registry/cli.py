#!/usr/bin/env python3
"""
L++ Blueprint Registry - Interactive Shell

A minimal CLI that drives the compiled L++ Blueprint Registry operator.
All logic lives in blueprints + COMPUTE units. This is just a thin caller.
"""

import sys
import json
from pathlib import Path

# Import from src package (handles sys.path setup)
from src import BPREG_REGISTRY
from frame_py.compiler import compile_blueprint

HERE = Path(__file__).parent
DEFAULT_REGISTRY = HERE / "registry"


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


def print_results(results: list, title: str = "Results"):
    """Pretty print search/list results."""
    if not results:
        print("  No results found.")
        return

    print(f"\n  {title} ({len(results)} items):")
    print("  " + "-" * 70)
    for r in results:
        dep_mark = "[DEPRECATED] " if r.get("deprecated") else ""
        tags = ", ".join(r.get("tags", [])[:3])
        print(f"  {dep_mark}{r['id']}")
        print(f"    v{r['version']} | {r.get('name', '')}")
        if tags:
            print(f"    Tags: {tags}")
        if r.get("description"):
            print(f"    {r['description'][:60]}...")
        print()


def print_blueprint(bp: dict):
    """Pretty print blueprint details."""
    if not bp:
        print("  No blueprint loaded.")
        return

    meta = bp.get("metadata", {})
    data = bp.get("data")

    print("\n  Blueprint Details:")
    print("  " + "=" * 60)
    print(f"  ID:          {meta.get('name', 'Unknown')}")
    print(f"  Version:     {meta.get('current_version', '?')}")
    print(f"  Owner:       {meta.get('owner', 'unknown')}")
    print(f"  Description: {meta.get('description', 'N/A')[:50]}")
    print(f"  Tags:        {', '.join(meta.get('tags', []))}")
    print(f"  Deprecated:  {meta.get('deprecated', False)}")
    if meta.get("deprecated_reason"):
        print(f"  Reason:      {meta['deprecated_reason']}")
    print(f"  Created:     {meta.get('created_at', 'N/A')}")
    print(f"  Updated:     {meta.get('updated_at', 'N/A')}")
    print(f"  Versions:    {', '.join(meta.get('versions', []))}")
    print(
        f"  Dependencies: {', '.join(meta.get('dependencies', [])) or 'None'}")

    if data:
        print("\n  Blueprint Content:")
        print(f"    States:      {len(data.get('states', {}))}")
        print(f"    Transitions: {len(data.get('transitions', []))}")
        print(f"    Actions:     {len(data.get('actions', {}))}")
        print(f"    Gates:       {len(data.get('gates', {}))}")


def print_versions(versions: list, bp_id: str):
    """Pretty print version history."""
    print(f"\n  Version History for {bp_id}:")
    print("  " + "-" * 40)
    for v in versions:
        current = " (current)" if v.get("is_current") else ""
        print(f"    {v['version']}{current}")


def print_diff(diff: dict):
    """Pretty print version diff."""
    print(f"\n  Comparing {diff['version_a']} -> {diff['version_b']}:")
    print("  " + "-" * 50)

    if not diff.get("changes"):
        print("  No changes detected.")
        return

    for change in diff["changes"]:
        ctype = change["type"]
        items = change["items"]
        print(f"  {ctype}:")
        for item in items[:5]:
            print(f"    - {item}")
        if len(items) > 5:
            print(f"    ... and {len(items) - 5} more")


def print_deps(graph: dict):
    """Pretty print dependency graph."""
    print(f"\n  Dependency Graph for {graph['root']}:")
    print("  " + "-" * 50)

    if not graph.get("edges"):
        print("  No dependencies.")
    else:
        print("  Dependencies:")
        for edge in graph["edges"]:
            node = graph["nodes"].get(edge["to"], {})
            exists = "[OK]" if node.get("exists") else "[MISSING]"
            print(f"    {edge['from']} -> {edge['to']} {exists}")

    if graph.get("dependents"):
        print("\n  Depended on by:")
        for dep in graph["dependents"]:
            print(f"    <- {dep}")


def print_stats(stats: dict):
    """Pretty print registry statistics."""
    print("\n  Registry Statistics:")
    print("  " + "-" * 40)
    print(f"  Total blueprints: {stats.get('total', 0)}")
    print(f"  Active:           {stats.get('active', 0)}")
    print(f"  Deprecated:       {stats.get('deprecated', 0)}")

    if stats.get("top_tags"):
        print("\n  Top Tags:")
        for t in stats["top_tags"]:
            print(f"    {t['tag']}: {t['count']}")


def main():
    print("\n=== L++ Blueprint Registry ===\n")

    # Compile and load operator
    op = compile_and_load(
        str(HERE / "blueprint_registry.json"), BPREG_REGISTRY)

    # Auto-load default registry if it exists
    default_index = DEFAULT_REGISTRY / "index.json"
    if default_index.exists():
        op.dispatch("LOAD", {"path": str(DEFAULT_REGISTRY)})
        print(f"  Loaded registry from {DEFAULT_REGISTRY}")

    ICONS = {
        "idle": "[ ]",
        "ready": "[R]",
        "viewing": "[V]",
        "searching": "[S]",
        "comparing": "[C]",
        "error": "[!]"
    }

    while True:
        ctx = op.context
        state_icon = ICONS.get(op.state, "[?]")

        # Status line
        if op.state == "ready" and ctx.get("stats"):
            stats = ctx["stats"]
            print(
                f"\n  {state_icon} {op.state} | {stats.get('total', 0)} blueprints")
        elif op.state == "viewing" and ctx.get("current_id"):
            print(
                f"\n  {state_icon} {ctx['current_id']} v{ctx.get('current_version', '?')}")
        elif ctx.get("message"):
            print(f"\n  {state_icon} {ctx['message']}")
        elif ctx.get("error"):
            print(f"\n  {state_icon} ERROR: {ctx['error']}")
        else:
            print(f"\n  {state_icon} {op.state}")

        try:
            cmd = input("\n> ").strip().split(maxsplit=1)
        except (EOFError, KeyboardInterrupt):
            break

        if not cmd:
            continue

        action = cmd[0].lower()
        arg = cmd[1] if len(cmd) > 1 else None

        # Command dispatch
        if action in ("q", "quit", "exit"):
            break

        elif action == "help":
            print("""
  Commands:
    init [path]              Initialize new registry
    load [path]              Load existing registry
    register <bp_path>       Register a blueprint
    update <bp_id> <path>    Update blueprint (version bump)
    get <bp_id> [version]    View blueprint details
    list [tag]               List all blueprints
    search <query>           Search blueprints
    versions                 Show version history (in viewing mode)
    compare <v1> <v2>        Compare two versions
    rollback <version>       Rollback to version
    deps                     Show dependencies (in viewing mode)
    deprecate [reason]       Mark as deprecated
    delete                   Delete blueprint
    export [format]          Export registry (json/markdown)
    stats                    Show registry statistics
    back                     Go back
    state                    Show raw context
    help                     Show this help
    quit                     Exit
            """)

        elif action == "init":
            path = arg or str(DEFAULT_REGISTRY)
            op.dispatch("INIT", {"path": path})

        elif action == "load":
            path = arg or str(DEFAULT_REGISTRY)
            op.dispatch("LOAD", {"path": path})

        elif action == "register" and arg:
            # Parse: register <path> [--tags tag1,tag2] [--owner name]
            parts = arg.split()
            bp_path = parts[0]
            tags = []
            owner = "unknown"

            i = 1
            while i < len(parts):
                if parts[i] == "--tags" and i + 1 < len(parts):
                    tags = parts[i + 1].split(",")
                    i += 2
                elif parts[i] == "--owner" and i + 1 < len(parts):
                    owner = parts[i + 1]
                    i += 2
                else:
                    i += 1

            op.dispatch("REGISTER", {
                "blueprint_path": bp_path,
                "tags": tags,
                "owner": owner
            })

        elif action == "update":
            if arg:
                parts = arg.split()
                if len(parts) >= 2:
                    bp_id, bp_path = parts[0], parts[1]
                    bump = parts[2] if len(parts) > 2 else "patch"
                    op.dispatch("UPDATE", {
                        "blueprint_id": bp_id,
                        "blueprint_path": bp_path,
                        "bump": bump
                    })
                else:
                    print(
                        "  Usage: update <blueprint_id> <path> [major|minor|patch]")
            elif ctx.get("current_id"):
                # Update current blueprint
                source = ctx.get("current_blueprint", {}).get(
                    "metadata", {}).get("source_path")
                if source:
                    op.dispatch("UPDATE", {
                        "blueprint_id": ctx["current_id"],
                        "blueprint_path": source,
                        "bump": "patch"
                    })

        elif action == "get":
            if arg:
                parts = arg.split()
                bp_id = parts[0]
                version = parts[1] if len(parts) > 1 else None
                op.dispatch("GET", {"blueprint_id": bp_id, "version": version})
            if ctx.get("current_blueprint"):
                print_blueprint(ctx["current_blueprint"])

        elif action == "list":
            op.dispatch("LIST", {"tag": arg, "show_deprecated": False})
            if ctx.get("search_results"):
                print_results(ctx["search_results"], "Blueprints")

        elif action == "search" and arg:
            op.dispatch("SEARCH", {"query": arg})
            if ctx.get("search_results"):
                print_results(ctx["search_results"], f"Search: '{arg}'")

        elif action == "select" and arg:
            op.dispatch("SELECT", {"blueprint_id": arg})
            if ctx.get("current_blueprint"):
                print_blueprint(ctx["current_blueprint"])

        elif action == "versions":
            if ctx.get("current_id"):
                op.dispatch("VERSIONS", {"blueprint_id": ctx["current_id"]})
                if ctx.get("version_history"):
                    print_versions(ctx["version_history"], ctx["current_id"])
            else:
                print("  Select a blueprint first with 'get <id>'")

        elif action == "compare" and arg:
            parts = arg.split()
            if len(parts) >= 2:
                v_a, v_b = parts[0], parts[1]
                bp_id = ctx.get("current_id")
                if bp_id:
                    op.dispatch("COMPARE", {
                        "blueprint_id": bp_id,
                        "version_a": v_a,
                        "version_b": v_b
                    })
                    if ctx.get("diff_result"):
                        print_diff(ctx["diff_result"])
                else:
                    print("  Select a blueprint first with 'get <id>'")
            else:
                print("  Usage: compare <version_a> <version_b>")

        elif action == "rollback" and arg:
            bp_id = ctx.get("current_id")
            if bp_id:
                op.dispatch("ROLLBACK", {
                    "blueprint_id": bp_id,
                    "version": arg
                })
            else:
                print("  Select a blueprint first")

        elif action == "deps":
            bp_id = ctx.get("current_id")
            if bp_id:
                op.dispatch("DEPS", {"blueprint_id": bp_id})
                if ctx.get("dependency_graph"):
                    print_deps(ctx["dependency_graph"])
            else:
                print("  Select a blueprint first")

        elif action == "deprecate":
            bp_id = ctx.get("current_id")
            if bp_id:
                reason = arg or "No reason provided"
                op.dispatch("DEPRECATE", {
                    "blueprint_id": bp_id,
                    "reason": reason
                })
            else:
                print("  Select a blueprint first")

        elif action == "delete":
            bp_id = arg or ctx.get("current_id")
            if bp_id:
                confirm = input(f"  Delete {bp_id}? (y/N): ").strip().lower()
                if confirm == "y":
                    op.dispatch("DELETE", {
                        "blueprint_id": bp_id,
                        "delete_files": True
                    })
            else:
                print("  Usage: delete <blueprint_id>")

        elif action == "export":
            fmt = arg or "json"
            op.dispatch("EXPORT", {"format": fmt})
            if ctx.get("export_data"):
                data = ctx["export_data"]
                if data.get("format") == "markdown":
                    print(data["content"])
                else:
                    print(json.dumps(data, indent=2))

        elif action == "stats":
            op.dispatch("STATS", {})
            if ctx.get("stats"):
                print_stats(ctx["stats"])

        elif action == "back":
            op.dispatch("BACK", {})

        elif action == "clear":
            op.dispatch("CLEAR", {})

        elif action == "state":
            print(json.dumps(ctx, indent=2, default=str))

        else:
            print(f"  Unknown command: {action}. Type 'help' for commands.")

    print("\n  Goodbye!")


if __name__ == "__main__":
    main()
