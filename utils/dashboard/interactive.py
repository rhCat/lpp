#!/usr/bin/env python3
"""
Dashboard Interactive CLI
Generates an interactive HTML dashboard for all L++ utility tools.
"""
import sys
import os
import json

# Add parent to path for imports
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from src.dashboard_compute import COMPUTE_REGISTRY


def main():
    """Generate the L++ tools dashboard."""
    # Default to the utils directory
    if len(sys.argv) > 1:
        utilsPath = sys.argv[1]
    else:
        utilsPath = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

    if not os.path.isdir(utilsPath):
        print(f"Error: Invalid path: {utilsPath}")
        sys.exit(1)

    print(f"Scanning tools in: {utilsPath}")

    # Step 1: Scan for tools
    result = COMPUTE_REGISTRY["dashboard:scanTools"]({"utilsPath": utilsPath})
    if result.get("error"):
        print(f"Error scanning: {result['error']}")
        sys.exit(1)

    tools = result["tools"]
    print(f"Found {len(tools)} tools")

    # Step 2: Analyze tools
    result = COMPUTE_REGISTRY["dashboard:analyzeTools"]({"tools": tools})
    if result.get("error"):
        print(f"Error analyzing: {result['error']}")
        sys.exit(1)

    tools = result["tools"]
    stats = result["statistics"]
    print(f"Statistics: {stats['totalStates']} states, {stats['totalTransitions']} transitions")

    # Step 3: Categorize tools
    result = COMPUTE_REGISTRY["dashboard:categorizeTools"]({"tools": tools})
    if result.get("error"):
        print(f"Error categorizing: {result['error']}")
        sys.exit(1)

    categories = result["categories"]
    print(f"Categories: {', '.join(categories.keys())}")

    # Step 4: Generate dashboard
    result = COMPUTE_REGISTRY["dashboard:generateDashboard"]({
        "tools": tools,
        "categories": categories,
        "statistics": stats,
        "utilsPath": utilsPath
    })

    if result.get("error"):
        print(f"Error generating dashboard: {result['error']}")
        sys.exit(1)

    print(f"\nDashboard generated: {result['htmlPath']}")
    print("Open this file in a browser to view the dashboard.")


if __name__ == "__main__":
    main()
