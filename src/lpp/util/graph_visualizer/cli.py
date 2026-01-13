from src.graph_visualizer_compute import COMPUTE_UNITS
import json
import sys


def main():
    if len(sys.argv) < 2:
        print("Usage: python interactive.py <blueprint.json>")
        sys.exit(1)
    blueprint_path = sys.argv[1]
    try:
        with open(blueprint_path, 'r') as f:
            blueprint_data = f.read()
    except Exception as e:
        print(f"Error reading blueprint: {e}")
        sys.exit(1)
    params = {"blueprint": blueprint_data, "html_path": "output.html"}
    result = COMPUTE_UNITS["process"](params)
    print("Result:")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
