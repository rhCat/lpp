#!/usr/bin/env python3
"""L++ Function Decoder - Interactive CLI (< 50 lines per build_rules.md)"""
from src.function_decoder_compute import COMPUTE_REGISTRY, visualizeModuleGraph
from frame_py.compiler import compile_blueprint
from pathlib import Path
import importlib.util
import json
import os
import sys
sys.path.insert(0, "../../src")

HERE = Path(__file__).parent


def load():
    out = HERE / "results/function_decoder_compiled.py"
    out.parent.mkdir(exist_ok=True)
    compile_blueprint(str(HERE / "function_decoder.json"), str(out))
    spec = importlib.util.spec_from_file_location("op", out)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    reg = {tuple(k.split(":")): fn for k, fn in COMPUTE_REGISTRY.items()}
    return mod.create_operator(reg)


def main():
    op = load()
    print(
        "FuncDecoder: decode <file.py> | show | export [file] | graph | visualize [files...] | quit")
    while True:
        try:
            cmd = input(f"[{op.state}]> ").strip()
        except (EOFError, KeyboardInterrupt):
            break
        if not cmd:
            continue
        parts = cmd.split(maxsplit=1)
        verb, arg = parts[0].lower(), parts[1] if len(parts) > 1 else ""

        if verb == "quit":
            break
        elif verb == "decode":
            if not arg:
                print("Usage: decode <path/to/file.py>")
                continue
            op.context["filePath"] = os.path.abspath(arg)
            op.dispatch("DECODE", {})
            for _ in range(5):
                op.dispatch("AUTO", {})
            c = op.context.get("coupling", {})
            print(
                f"Exports: {c.get('fanIn', 0)} | Imports: {c.get('fanOut', 0)}")
            print(f"Internal edges: {c.get('internalEdges', 0)}")
            if op.context.get("error"):
                print(f"Error: {op.context['error']}")
        elif verb == "show":
            mg = op.context.get("moduleGraph")
            print(json.dumps(mg, indent=2) if mg else "No graph. Run decode.")
        elif verb == "graph":
            mg = op.context.get("moduleGraph", {})
            _print_graph(mg)
        elif verb == "visualize":
            _visualize(arg, op.context.get("moduleGraph"))
        elif verb == "export":
            mg = op.context.get("moduleGraph")
            if not mg:
                print("No graph to export.")
                continue
            out = arg if arg else "module_graph.json"
            with open(out, "w") as f:
                json.dump(mg, f, indent=2)
            print(f"Exported: {out}")
        elif verb == "reset":
            op.dispatch("RESET", {})
        else:
            print("Unknown command")


def _visualize(args: str, current_graph):
    """Visualize one or more module graphs as stackable HTML."""
    graphs = []
    files = args.split() if args else []

    # Load from JSON files
    for f in files:
        try:
            with open(f, "r") as fp:
                data = json.load(fp)
                # Handle both raw moduleGraph and wrapped format
                if "moduleGraph" in data:
                    graphs.append(data["moduleGraph"])
                elif "module" in data:
                    graphs.append(data)
        except Exception as e:
            print(f"Error loading {f}: {e}")

    # Add current graph if available
    if current_graph and not files:
        graphs.append(current_graph)

    if not graphs:
        print("No graphs to visualize. Decode a file or provide JSON paths.")
        return

    output = "results/function_graph.html"
    Path(output).parent.mkdir(exist_ok=True)

    title = f"Function Graph ({len(graphs)} modules)" if len(
        graphs) > 1 else f"Function Graph: {graphs[0].get('module', 'unknown')}"
    result = visualizeModuleGraph({
        "moduleGraphs": graphs,
        "outputPath": output,
        "title": title
    })

    if result.get("error"):
        print(f"Error: {result['error']}")
    else:
        print(f"Generated: {result['htmlPath']}")
        print(
            f"Nodes: {sum(len(g.get('nodes', [])) for g in graphs)} | Edges: {sum(len(g.get('edges', [])) for g in graphs)}")


def _print_graph(mg):
    if not mg:
        print("No graph.")
        return
    print(f"\n=== {mg.get('module', '?')} ===")
    print("\nINBOUND (exports):")
    for e in mg.get("inbound", []):
        sig = e.get("signature", "") or ""
        print(f"  {e['type']:12} {e['name']}{sig}")
    print("\nOUTBOUND (imports):")
    for o in mg.get("outbound", []):
        names = [n["name"] for n in o.get("names", [])]
        print(f"  [{o['category']:6}] {o['module']}: {', '.join(names) or '*'}")
    c = mg.get("coupling", {})
    print(f"\nCoupling: fanIn={c.get('fanIn')} fanOut={c.get('fanOut')} "
          f"instability={c.get('instability')}")


if __name__ == "__main__":
    main()
