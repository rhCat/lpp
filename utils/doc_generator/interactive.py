#!/usr/bin/env python3
"""
Documentation Generator CLI
Generates all documentation artifacts for L++ blueprints.

Works on any L++ project by specifying --project <path>.

Usage:
    python interactive.py [--project <path>] [--all] [--graphs] [--mermaid] ...

Examples:
    python interactive.py                    # Generate docs for L++ utils
    python interactive.py --project /my/app  # Generate docs for external project
"""
import sys
import os
import argparse
from datetime import datetime

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from src.docgen_compute import COMPUTE_REGISTRY


def main():
    parser = argparse.ArgumentParser(
        description='L++ Documentation Generator - Works on any L++ project'
    )
    parser.add_argument('--project', '-p', metavar='PATH',
                        help='Path to L++ project (default: L++ utils directory)')
    parser.add_argument('--all', action='store_true', help='Generate all docs (default)')
    parser.add_argument('--graphs', action='store_true', help='Generate HTML graph visualizations')
    parser.add_argument('--logic', action='store_true', help='Generate logic graphs from Python')
    parser.add_argument('--functions', action='store_true', help='Generate function dependency graphs')
    parser.add_argument('--mermaid', action='store_true', help='Generate Mermaid diagrams')
    parser.add_argument('--readme', action='store_true', help='Update README files')
    parser.add_argument('--report', action='store_true', help='Generate analysis report')
    parser.add_argument('--dashboard', action='store_true', help='Generate dashboard HTML')
    parser.add_argument('-q', '--quiet', action='store_true', help='Suppress verbose output')

    args = parser.parse_args()

    # Default to --all if no specific flags
    if not any([args.graphs, args.logic, args.functions, args.mermaid,
                args.readme, args.report, args.dashboard]):
        args.all = True

    verbose = not args.quiet

    # Determine project path
    if args.project:
        projectPath = os.path.abspath(args.project)
        if not os.path.isdir(projectPath):
            print(f"ERROR: Project path does not exist: {projectPath}")
            return 1
    else:
        # Default to L++ utils directory
        projectPath = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

    print("=" * 60)
    print("L++ Documentation Generator")
    print(f"Project: {projectPath}")
    print(f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print("=" * 60)

    # Initialize
    options = {
        "all": args.all,
        "graphs": args.graphs,
        "logic": args.logic,
        "functions": args.functions,
        "mermaid": args.mermaid,
        "readme": args.readme,
        "report": args.report,
        "dashboard": args.dashboard,
    }
    COMPUTE_REGISTRY["docgen:init"]({"options": options})

    # Discover blueprints
    print("\nDiscovering blueprints...")
    result = COMPUTE_REGISTRY["docgen:discoverBlueprints"]({"utilsPath": projectPath})
    print(f"Found {result['count']} blueprints")

    if result['count'] == 0:
        print("ERROR: No blueprints found")
        return 1

    totalGenerated = 0
    totalErrors = []

    # Generate graphs
    if args.all or args.graphs:
        print("\nGenerating HTML Graph Visualizations...")
        result = COMPUTE_REGISTRY["docgen:generateGraphs"]({"verbose": verbose})
        totalGenerated += result['generated']
        totalErrors.extend(result['errors'])
        print(f"  Generated: {result['generated']}")

    # Generate logic graphs
    if args.all or args.logic:
        print("\nGenerating Logic Graphs...")
        result = COMPUTE_REGISTRY["docgen:generateLogicGraphs"]({"verbose": verbose})
        totalGenerated += result['generated']
        totalErrors.extend(result['errors'])
        print(f"  Generated: {result['generated']}")

    # Generate function graphs
    if args.all or args.functions:
        print("\nGenerating Function Dependency Graphs...")
        result = COMPUTE_REGISTRY["docgen:generateFunctionGraphs"]({"verbose": verbose})
        totalGenerated += result['generated']
        totalErrors.extend(result['errors'])
        print(f"  Generated: {result['generated']}")

    # Generate Mermaid diagrams
    if args.all or args.mermaid:
        print("\nGenerating Mermaid Diagrams...")
        result = COMPUTE_REGISTRY["docgen:generateMermaid"]({"verbose": verbose})
        totalGenerated += result['generated']
        totalErrors.extend(result['errors'])
        print(f"  Generated: {result['generated']}")

    # Update READMEs
    if args.all or args.readme:
        print("\nUpdating README files...")
        result = COMPUTE_REGISTRY["docgen:updateReadmes"]({"verbose": verbose})
        totalGenerated += result['updated']
        totalErrors.extend(result['errors'])
        print(f"  Updated: {result['updated']}")

    # Generate report
    if args.all or args.report:
        print("\nGenerating Analysis Report...")
        result = COMPUTE_REGISTRY["docgen:generateReport"]({"utilsPath": projectPath, "verbose": verbose})
        if result.get('success'):
            totalGenerated += 1

    # Generate dashboard
    if args.all or args.dashboard:
        print("\nGenerating Dashboard...")
        result = COMPUTE_REGISTRY["docgen:generateDashboard"]({"utilsPath": projectPath, "verbose": verbose})
        if result.get('success'):
            totalGenerated += 1

    # Summary
    print("\n" + "=" * 60)
    print(f"COMPLETE: Generated {totalGenerated} artifacts")
    if totalErrors:
        print(f"ERRORS: {len(totalErrors)}")
        for name, err in totalErrors[:10]:
            print(f"  - {name}: {err}")

    print("\nOutput locations:")
    print("  - Graphs:     <tool>/results/<tool>_graph.html")
    print("  - Logic:      <tool>/results/<tool>_logic_graph.html")
    print("  - Functions:  <tool>/results/<tool>_functions.html")
    print("  - Mermaid:    <tool>/results/<tool>.mmd")
    print("  - Diagrams:   <tool>/results/<tool>_diagram.html")
    print(f"  - Report:     {projectPath}/analysis_report.md")
    print(f"  - Dashboard:  {projectPath}/dashboard.html")

    return 0 if not totalErrors else 1


if __name__ == "__main__":
    sys.exit(main())
