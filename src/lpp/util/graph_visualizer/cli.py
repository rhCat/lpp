#!/usr/bin/env python3
"""
Graph Visualizer CLI

Generates interactive HTML/SVG state machine diagrams.

Usage:
    lpp util graph_visualizer <blueprint.json> [--output <file>]
    python -m lpp.util.graph_visualizer <blueprint.json>

Examples:
    lpp util graph_visualizer blueprint.json
    lpp util graph_visualizer blueprint.json --output diagram.html
"""
import sys
import argparse
from pathlib import Path


def main(args=None):
    parser = argparse.ArgumentParser(
        description='Generate interactive state machine diagrams'
    )
    parser.add_argument('blueprint', nargs='?',
                        help='Path to L++ blueprint JSON')
    parser.add_argument('--output', '-o', default='diagram.html',
                        help='Output HTML file (default: diagram.html)')

    parsed = parser.parse_args(args)

    if not parsed.blueprint:
        parser.print_help()
        print("\nError: blueprint path required")
        return 1

    bp_path = Path(parsed.blueprint)
    if not bp_path.exists():
        print(f"Error: Blueprint not found: {bp_path}")
        return 1

    # Read blueprint
    with open(bp_path) as f:
        blueprint_data = f.read()

    from . import run

    result = run({
        "blueprint": blueprint_data,
        "html_path": parsed.output,
    })

    if result.get("error"):
        print(f"Error: {result['error']}")
        return 1

    ctx = result.get("context", {})
    if ctx.get("has_html"):
        print(f"Generated: {ctx.get('html_path')}")
    else:
        print(f"State: {result.get('state')}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
