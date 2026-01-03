#!/usr/bin/env python3
"""
L++ Documentation Generator - Interactive Shell

A minimal CLI that drives compiled L++ operators for documentation generation.
All logic lives in blueprints + COMPUTE units. This is just a thin caller.
"""

import sys
import json
from pathlib import Path
from src import DOC_REGISTRY
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
  load <path>       Load a blueprint JSON file
  format <fmt>      Set output format: markdown | html | json
  generate          Generate all documentation sections
  export [path]     Export documentation to file
  full [path]       Generate and export in one step

Options:
  mermaid           Toggle mermaid diagram inclusion
  tables            Toggle detailed tables inclusion
  quickstart        Toggle quick-start guide inclusion
  context           Toggle context schema docs inclusion

Navigation:
  back              Go back to previous state
  unload            Unload current blueprint
  state             Show current context
  help              Show this help
  quit              Exit
""")


def main():
    print("\nL++ Documentation Generator\n")

    doc = compile_and_load(str(HERE / "doc_generator.json"), DOC_REGISTRY)

    # CLI arg
    if len(sys.argv) > 1:
        doc.dispatch("LOAD", {"path": sys.argv[1]})

    ICONS = {
        "idle": "[.]",
        "loaded": "[+]",
        "generating": "[~]",
        "assembling": "[~]",
        "exporting": "[>]",
        "done": "[!]",
        "error": "[X]"
    }

    while True:
        ctx = doc.context
        icon = ICONS.get(doc.state, "[?]")
        status = doc.display() if hasattr(doc, 'display') else doc.state

        # Show options status when loaded
        if doc.state == "loaded":
            opts = []
            if ctx.get("include_mermaid"):
                opts.append("mermaid")
            if ctx.get("include_tables"):
                opts.append("tables")
            if ctx.get("include_quickstart"):
                opts.append("quickstart")
            if ctx.get("include_context"):
                opts.append("context")
            opts_str = f" [{', '.join(opts)}]" if opts else ""
            print(f"\n  {icon} [{doc.state}] {ctx.get('blueprint_name', '-')} "
                  f"({ctx.get('output_format', 'markdown')}){opts_str}")
        else:
            print(f"\n  {icon} [{doc.state}] {status}")

        # Show output path when done
        if doc.state == "done" and ctx.get("output_path"):
            print(f"  Exported to: {ctx['output_path']}")

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
            print_help()
        elif action == "load" and arg:
            doc.dispatch("LOAD", {"path": arg})
        elif action == "format" and arg:
            fmt = arg.lower()
            if fmt == "markdown":
                doc.dispatch("FORMAT_MARKDOWN")
            elif fmt == "html":
                doc.dispatch("FORMAT_HTML")
            elif fmt == "json":
                doc.dispatch("FORMAT_JSON")
            else:
                print(f"  Unknown format: {fmt}")
        elif action == "mermaid":
            doc.dispatch("TOGGLE_MERMAID")
        elif action == "tables":
            doc.dispatch("TOGGLE_TABLES")
        elif action == "quickstart":
            doc.dispatch("TOGGLE_QUICKSTART")
        elif action == "context":
            doc.dispatch("TOGGLE_CONTEXT")
        elif action == "generate":
            doc.dispatch("GENERATE")
            if doc.state == "generating":
                doc.dispatch("ASSEMBLE")
        elif action == "export":
            path = arg or f"./{ctx.get('blueprint_id', 'doc')}_docs." \
                          f"{_ext(ctx.get('output_format', 'markdown'))}"
            if doc.state == "assembling":
                doc.dispatch("EXPORT", {"path": path})
                doc.dispatch("DONE")
            else:
                print("  Generate documentation first with 'generate'")
        elif action == "full":
            path = arg or f"./{ctx.get('blueprint_id', 'doc')}_docs." \
                          f"{_ext(ctx.get('output_format', 'markdown'))}"
            doc.dispatch("GENERATE")
            if doc.state == "generating":
                doc.dispatch("ASSEMBLE")
            if doc.state == "assembling":
                doc.dispatch("EXPORT", {"path": path})
                doc.dispatch("DONE")
        elif action == "back":
            doc.dispatch("BACK")
        elif action == "unload":
            doc.dispatch("UNLOAD")
        elif action == "clear":
            doc.dispatch("CLEAR")
        elif action == "state":
            print(json.dumps(ctx, indent=2, default=str))
        else:
            print(f"  Unknown command: {action}. Type 'help' for commands.")

    print("  Goodbye!")


def _ext(fmt: str) -> str:
    """Get extension for format."""
    return {"markdown": "md", "html": "html", "json": "json"}.get(fmt, "txt")


if __name__ == "__main__":
    main()
