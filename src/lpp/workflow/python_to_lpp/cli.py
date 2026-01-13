#!/usr/bin/env python3
"""
Python to L++ Refactorer - Interactive CLI

Orchestrates existing L++ utils to refactor Python projects into L++ blueprints.

Usage:
    python interactive.py <project_path> [options]

Examples:
    python interactive.py /path/to/my/project
    python interactive.py /path/to/project --output /path/to/output
    python interactive.py /path/to/project --include-tests --verbose
"""
from src.py2lpp_compute import COMPUTE_REGISTRY
import sys
import os
import argparse
from datetime import datetime

# Add src to path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


def main():
    parser = argparse.ArgumentParser(
        description='Refactor Python project to L++ using utils tools',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
This workflow orchestrates existing L++ utils:
  - doc_generator: For documentation and diagrams
  - legacy_extractor: For pattern extraction (if available)
  - logic_decoder: For logic analysis (if available)
  - dashboard: For project dashboard

Examples:
  %(prog)s /path/to/project                    # Basic refactoring
  %(prog)s /path/to/project -o /path/to/output # Custom output
  %(prog)s /path/to/project --no-docs          # Skip doc generation
        """
    )
    parser.add_argument('project', help='Path to Python project')
    parser.add_argument('-o', '--output', metavar='PATH',
                        help='Output path (default: <project>/lpp_output)')
    parser.add_argument('-n', '--name', metavar='NAME',
                        help='Project name (default: directory name)')
    parser.add_argument('--include-tests', action='store_true',
                        help='Include test files')
    parser.add_argument('--no-docs', action='store_true',
                        help='Skip documentation generation')
    parser.add_argument('-v', '--verbose', action='store_true',
                        help='Verbose output')

    args = parser.parse_args()

    # Validate project path
    projectPath = os.path.abspath(args.project)
    if not os.path.isdir(projectPath):
        print(f"Error: Project path does not exist: {projectPath}")
        return 1

    outputPath = os.path.abspath(args.output) if args.output else None

    options = {
        "includeTests": args.include_tests,
        "generateDocs": not args.no_docs,
        "preserveOriginal": True,
        "verbose": args.verbose
    }

    print("=" * 60)
    print("Python to L++ Refactorer")
    print("=" * 60)
    print(f"Project: {projectPath}")
    if outputPath:
        print(f"Output:  {outputPath}")
    print(f"Started: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print()

    # Step 1: Initialize
    print("[1/9] Initializing...")
    result = COMPUTE_REGISTRY["py2lpp:init"]({
        "projectPath": projectPath,
        "outputPath": outputPath,
        "projectName": args.name,
        "options": options
    })
    print(f"  Utils available:")
    for util, available in result.get("utilsAvailable", {}).items():
        status = "Yes" if available else "No (using fallback)"
        print(f"    - {util}: {status}")

    # Step 2: Scan project
    print("\n[2/9] Scanning project...")
    result = COMPUTE_REGISTRY["py2lpp:scanProject"](
        {"projectPath": projectPath})
    if result.get("error"):
        print(f"Error: {result['error']}")
        return 1
    print(f"  Found {result['count']} Python files")
    if args.verbose and result.get("files"):
        for f in result["files"][:10]:
            print(f"    - {f['relpath']}")
        if len(result["files"]) > 10:
            print(f"    ... and {len(result['files']) - 10} more")

    # Step 3: Extract patterns
    print("\n[3/9] Extracting patterns...")
    result = COMPUTE_REGISTRY["py2lpp:extractPatterns"]({})
    print(f"  Extracted {result['count']} modules")
    if args.verbose and result.get("modules"):
        for m in result["modules"][:5]:
            src = m.get("source", "basic")
            name = m.get("name", m.get("file", {}).get("name", "unknown"))
            print(f"    - {name} (via {src})")

    if result["count"] == 0:
        print("\nNo modules extracted. Try with --include-tests or check")
        print("if your code has classes with multiple methods.")
        return 1

    # Step 4: Decode logic
    print("\n[4/9] Decoding logic...")
    result = COMPUTE_REGISTRY["py2lpp:decodeLogic"]({})
    print(f"  Decoded {result['count']} modules")

    # Step 5: Generate blueprints
    print("\n[5/9] Generating L++ blueprints...")
    result = COMPUTE_REGISTRY["py2lpp:generateBlueprints"]({})
    print(f"  Generated {result['count']} blueprints")
    if args.verbose and result.get("blueprints"):
        for bp in result["blueprints"]:
            print(f"    - {bp['id']}: {len(bp['states'])} states")

    # Step 6: Generate function graphs
    print("\n[6/9] Generating function dependency graphs...")
    result = COMPUTE_REGISTRY["py2lpp:generateFunctionGraphs"]({})
    print(f"  Generated {result['generated']} module graphs")
    if args.verbose and result.get("graphs"):
        for g in result["graphs"][:10]:
            print(f"    - {g}")
        if len(result["graphs"]) > 10:
            print(f"    ... and {len(result['graphs']) - 10} more")

    # Step 7: Generate compute stubs
    print("\n[7/9] Generating compute functions...")
    result = COMPUTE_REGISTRY["py2lpp:generateCompute"]({})
    print(f"  Generated {result['generated']} compute files")

    # Step 8: Generate documentation (using doc_generator util)
    if not args.no_docs:
        print("\n[8/9] Generating documentation (via doc_generator)...")
        result = COMPUTE_REGISTRY["py2lpp:generateDocs"]({})
        print(f"  Generated {result['generated']} documentation files")

        # Generate dashboard
        print("\n[9/9] Generating dashboard (via dashboard util)...")
        result = COMPUTE_REGISTRY["py2lpp:generateDashboard"]({})
        print(
            f"  Dashboard: {'Generated' if result['generated'] else 'Skipped'}")
    else:
        print("\n[8/9] Skipping documentation (--no-docs)")
        print("\n[9/9] Skipping dashboard")

    # Validate
    print("\nValidating...")
    result = COMPUTE_REGISTRY["py2lpp:validate"]({})
    if result["valid"]:
        print("  All validations passed")
    else:
        print(f"  Errors: {len(result['errors'])}")
        for err in result["errors"][:5]:
            print(f"    - {err}")
    if result.get("warnings"):
        print(f"  Warnings: {len(result['warnings'])}")

    # Finalize
    print("\nFinalizing...")
    summary = COMPUTE_REGISTRY["py2lpp:finalize"]({})

    # Print summary
    print("\n" + "=" * 60)
    print("REFACTORING COMPLETE")
    print("=" * 60)
    print(f"\nProject:              {summary['projectName']}")
    print(f"Output:               {summary['outputPath']}")
    print(f"Modules Found:        {summary['modulesFound']}")
    print(f"Blueprints Generated: {summary['blueprintsGenerated']}")
    print(f"Function Graphs:      {summary['functionGraphsGenerated']}")
    print(f"Docs Generated:       {summary['docsGenerated']}")

    if summary.get("errors"):
        print(f"\nErrors: {len(summary['errors'])}")
        for name, err in summary["errors"][:5]:
            print(f"  - {name}: {err}")

    print(f"\nGenerated outputs:")
    print(f"  - function_graph.html  (interactive dependency visualization)")
    print(f"  - function_graphs.json (raw graph data)")
    print(f"  - dashboard.html       (project dashboard)")
    print(f"  - {len(summary['blueprints'])} L++ blueprints")

    print(f"\nNext steps:")
    print(f"  1. Open {summary['outputPath']}/function_graph.html")
    print(f"  2. Review blueprints in {summary['outputPath']}/")
    print(f"  3. Implement TODO stubs in *_compute.py files")

    return 0


if __name__ == "__main__":
    sys.exit(main())
