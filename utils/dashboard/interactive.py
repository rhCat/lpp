#!/usr/bin/env python3
"""
Dashboard Interactive CLI
Generates an interactive HTML dashboard for all L++ utility tools.

Note: Only scans utils/ directory. Core framework (src/) is foundational
infrastructure, not utility tools.
"""
import sys
import os

# Add parent to path for imports
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from src.dashboard_compute import COMPUTE_REGISTRY


def main():
    """Generate the L++ tools dashboard."""
    # Get the utils path (one level up from this file)
    dashboardDir = os.path.dirname(os.path.abspath(__file__))
    utilsPath = os.path.dirname(dashboardDir)

    if not os.path.isdir(utilsPath):
        print("Error: No valid utils path")
        sys.exit(1)

    print(f"Scanning utils: {utilsPath}")

    # Step 1: Scan for tools (utils/ only)
    result = COMPUTE_REGISTRY["dashboard:scanTools"]({"utilsPath": utilsPath})
    if result.get("error"):
        print(f"Error scanning: {result['error']}")
        sys.exit(1)

    tools = result["tools"]
    print(f"Found {len(tools)} utility tools")

    # Step 2: Analyze tools
    result = COMPUTE_REGISTRY["dashboard:analyzeTools"]({"tools": tools})
    if result.get("error"):
        print(f"Error analyzing: {result['error']}")
        sys.exit(1)

    tools = result["tools"]
    stats = result["statistics"]
    print(f"Statistics: {stats['totalStates']} states, "
          f"{stats['totalTransitions']} transitions")

    # Step 3: Categorize tools
    result = COMPUTE_REGISTRY["dashboard:categorizeTools"]({"tools": tools})
    if result.get("error"):
        print(f"Error categorizing: {result['error']}")
        sys.exit(1)

    categories = result["categories"]
    print(f"Categories: {', '.join(categories.keys())}")

    # Step 4: Generate dashboard at utils/dashboard.html
    outputPath = os.path.join(utilsPath, "dashboard.html")
    result = COMPUTE_REGISTRY["dashboard:generateDashboard"]({
        "tools": tools,
        "categories": categories,
        "statistics": stats,
        "basePath": utilsPath,
        "outputPath": outputPath
    })

    if result.get("error"):
        print(f"Error generating dashboard: {result['error']}")
        sys.exit(1)

    print(f"\nDashboard generated: {result['htmlPath']}")
    print("Open this file in a browser to view the dashboard.")


if __name__ == "__main__":
    main()
