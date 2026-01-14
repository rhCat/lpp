#!/usr/bin/env python3
"""
Documentation Generator CLI

Generates documentation artifacts for L++ blueprints including
Mermaid diagrams and HTML dashboards.

Usage:
    lpp util doc_generator <path> [options]
    python -m lpp.util.doc_generator <path>

Examples:
    lpp util doc_generator .                    # Current directory
    lpp util doc_generator demo/task_tracker    # Specific project
    lpp util doc_generator . --mermaid          # Mermaid only
    lpp util doc_generator . --dashboard        # Dashboard only

Note: This is a wrapper around 'lpp docs' functionality.
"""
import sys
import argparse
from pathlib import Path
from datetime import datetime


def main(args=None):
    parser = argparse.ArgumentParser(
        description='Generate L++ documentation artifacts'
    )
    parser.add_argument('path', nargs='?', default='.',
                        help='Path to L++ project or blueprint')
    parser.add_argument('--output', '-o',
                        help='Output directory (default: <path>/results)')
    parser.add_argument('--mermaid', action='store_true',
                        help='Generate Mermaid diagrams only')
    parser.add_argument('--dashboard', action='store_true',
                        help='Generate dashboard HTML only')
    parser.add_argument('-q', '--quiet', action='store_true',
                        help='Suppress verbose output')

    parsed = parser.parse_args(args)

    target = Path(parsed.path).resolve()
    if not target.exists():
        print(f"Error: Path not found: {target}")
        return 1

    # Find blueprint
    bp_file = None
    if target.is_file() and target.suffix == ".json":
        bp_file = target
        target = target.parent
    else:
        for p in [target / "blueprint.json", target / f"{target.name}.json"]:
            if p.exists():
                bp_file = p
                break
        if not bp_file:
            for p in target.glob("*.json"):
                bp_file = p
                break

    if not bp_file:
        print(f"No blueprint found in {target}")
        return 1

    output_dir = Path(parsed.output) if parsed.output else target / "results"
    output_dir.mkdir(parents=True, exist_ok=True)

    if not parsed.quiet:
        print("=" * 60)
        print("L++ Documentation Generator")
        print(f"Blueprint: {bp_file}")
        print(f"Output:    {output_dir}")
        print(f"Time:      {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        print("=" * 60)

    import json
    with open(bp_file) as f:
        bp = json.load(f)

    from lpp.core.visualizer import generate_mermaid, generate_html

    generated = 0

    if not parsed.dashboard:  # mermaid only or both
        mmd = generate_mermaid(bp)
        mmd_file = output_dir / "diagram.mmd"
        mmd_file.write_text(mmd)
        if not parsed.quiet:
            print(f"Generated: {mmd_file}")
        generated += 1

    if not parsed.mermaid:  # dashboard only or both
        html = generate_html(bp)
        html_file = output_dir / "dashboard.html"
        html_file.write_text(html)
        if not parsed.quiet:
            print(f"Generated: {html_file}")
        generated += 1

    if not parsed.quiet:
        print(f"\nTotal: {generated} artifacts generated")

    return 0


if __name__ == "__main__":
    sys.exit(main())
