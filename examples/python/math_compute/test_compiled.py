#!/usr/bin/env python3
"""
Test the L++ Calculator - Compile and Run

1. Creates unique run folder: results/run_YYYYMMDD_HHMMSS/
2. Compiles calculator.json -> run folder
3. Runs tests and saves all artifacts to run folder
"""

from frame_py.compiler import compile_blueprint
import sys
import json
import shutil
import importlib.util
from pathlib import Path
from datetime import datetime, timezone

# Setup paths
HERE = Path(__file__).parent
ROOT = HERE.parent.parent
RESULTS_DIR = HERE / "results"
RUN_TIMESTAMP = datetime.now().strftime("%Y%m%d_%H%M%S")
RUN_DIR = RESULTS_DIR / f"run_{RUN_TIMESTAMP}"
sys.path.insert(0, str(ROOT / "src"))


blueprint_name = "math_compute.json"
compiled_name = "math_compute_compiled.py"

# =========================================================================
# STEP 1: COMPILE
# =========================================================================


def compile_calculator():
    """Compile the calculator blueprint to Python."""
    RUN_DIR.mkdir(parents=True, exist_ok=True)
    blueprint_path = HERE / blueprint_name
    output_path = RUN_DIR / compiled_name

    print("=" * 60)
    print("STEP 1: COMPILING BLUEPRINT")
    print("=" * 60)
    print(f"  Run folder: {RUN_DIR}")
    print(f"  Input:  {blueprint_path}")
    print(f"  Output: {output_path}")

    # Copy source blueprint to run folder
    shutil.copy(blueprint_path, RUN_DIR / "calculator.json")
    compile_blueprint(str(blueprint_path), str(output_path))
    print("  Status: SUCCESS")
    print()

    return output_path


# =========================================================================
# STEP 2: IMPORT COMPILED OPERATOR
# =========================================================================

def load_operator():
    """Load the compiled operator module from run folder."""
    module_path = RUN_DIR / compiled_name
    spec = importlib.util.spec_from_file_location(
        "math_compute_compiled", module_path
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.create_operator


# =========================================================================
# COMPUTE REGISTRY
# =========================================================================

def math_calculate(payload: dict) -> dict:
    """Hermetic compute unit for arithmetic."""
    a = payload.get("a", 0)
    b = payload.get("b", 0)
    op = payload.get("op", "+")

    ops = {
        "+": lambda x, y: x + y,
        "-": lambda x, y: x - y,
        "*": lambda x, y: x * y,
        "/": lambda x, y: x / y if y != 0 else None,
    }

    result = ops.get(op, lambda x, y: None)(a, b)
    if result is None:
        return {"error": "Invalid", "status": "failed"}
    return {"result": result, "status": "success"}


REGISTRY = {
    ("math", "calculate"): math_calculate,
}


# =========================================================================
# STEP 3: RUN TESTS
# =========================================================================

def run_tests(create_operator):
    """Run test cases and collect results."""
    print("=" * 60)
    print("STEP 2: RUNNING TESTS")
    print("=" * 60)

    results = {
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "tests": [],
        "summary": {"passed": 0, "failed": 0},
    }

    calc = create_operator(REGISTRY)

    # Test 1: Basic addition
    test = {"name": "5 + 4 = 9", "expected": 9, "passed": False}
    print(f"\n>> Test 1: {test['name']}")
    calc.reset()
    calc.dispatch("NUMBER", {"value": 5})
    calc.dispatch("OPERATOR", {"op": "+"})
    calc.dispatch("NUMBER", {"value": 4})
    ok, state, err = calc.dispatch("EQUALS")
    actual = calc.get("a")  # result stored in 'a'
    test["actual"] = actual
    test["state"] = state
    test["passed"] = (actual == test["expected"])
    print(f"   Result: {actual}, Expected: {test['expected']}, "
          f"{'PASS' if test['passed'] else 'FAIL'}")
    results["tests"].append(test)

    # Test 2: Chain operation (9 * 2 = 18, since previous result is 9)
    test = {"name": "9 * 2 = 18 (chained)", "expected": 18, "passed": False}
    print(f"\n>> Test 2: {test['name']}")
    calc.dispatch("OPERATOR", {"op": "*"})
    calc.dispatch("NUMBER", {"value": 2})
    ok, state, err = calc.dispatch("EQUALS")
    actual = calc.get("a")  # result stored in 'a'
    test["actual"] = actual
    test["state"] = state
    test["passed"] = (actual == test["expected"])
    print(f"   Result: {actual}, Expected: {test['expected']}, "
          f"{'PASS' if test['passed'] else 'FAIL'}")
    results["tests"].append(test)

    # Test 3: Division by zero (should transition to error state)
    test = {"name": "10 / 0 = ERROR", "expected_state": "error",
            "passed": False}
    print(f"\n>> Test 3: {test['name']}")
    calc.reset()
    calc.dispatch("NUMBER", {"value": 10})
    calc.dispatch("OPERATOR", {"op": "/"})
    calc.dispatch("NUMBER", {"value": 0})
    ok, state, err = calc.dispatch("EQUALS")
    test["actual_state"] = state
    test["error"] = calc.get("error")
    test["passed"] = (state == test["expected_state"])
    print(f"   State: {state}, Error: {test['error']}, "
          f"{'PASS' if test['passed'] else 'FAIL'}")
    results["tests"].append(test)

    # Test 4: Subtraction
    test = {"name": "100 - 37 = 63", "expected": 63, "passed": False}
    print(f"\n>> Test 4: {test['name']}")
    calc.dispatch("CLEAR")
    calc.dispatch("NUMBER", {"value": 100})
    calc.dispatch("OPERATOR", {"op": "-"})
    calc.dispatch("NUMBER", {"value": 37})
    ok, state, err = calc.dispatch("EQUALS")
    actual = calc.get("a")  # result stored in 'a'
    test["actual"] = actual
    test["state"] = state
    test["passed"] = (actual == test["expected"])
    print(f"   Result: {actual}, Expected: {test['expected']}, "
          f"{'PASS' if test['passed'] else 'FAIL'}")
    results["tests"].append(test)

    # Test 5: Multiplication
    test = {"name": "7 * 6 = 42", "expected": 42, "passed": False}
    print(f"\n>> Test 5: {test['name']}")
    calc.reset()
    calc.dispatch("NUMBER", {"value": 7})
    calc.dispatch("OPERATOR", {"op": "*"})
    calc.dispatch("NUMBER", {"value": 6})
    ok, state, err = calc.dispatch("EQUALS")
    actual = calc.get("a")  # result stored in 'a'
    test["actual"] = actual
    test["state"] = state
    test["passed"] = (actual == test["expected"])
    print(f"   Result: {actual}, Expected: {test['expected']}, "
          f"{'PASS' if test['passed'] else 'FAIL'}")
    results["tests"].append(test)

    # Test 6: Division
    test = {"name": "144 / 12 = 12", "expected": 12, "passed": False}
    print(f"\n>> Test 6: {test['name']}")
    calc.reset()
    calc.dispatch("NUMBER", {"value": 144})
    calc.dispatch("OPERATOR", {"op": "/"})
    calc.dispatch("NUMBER", {"value": 12})
    ok, state, err = calc.dispatch("EQUALS")
    actual = calc.get("a")  # result stored in 'a'
    test["actual"] = actual
    test["state"] = state
    test["passed"] = (actual == test["expected"])
    print(f"   Result: {actual}, Expected: {test['expected']}, "
          f"{'PASS' if test['passed'] else 'FAIL'}")
    results["tests"].append(test)

    # Summary
    results["summary"]["passed"] = sum(
        1 for t in results["tests"] if t["passed"]
    )
    results["summary"]["failed"] = sum(
        1 for t in results["tests"] if not t["passed"]
    )
    results["total_transitions"] = len(calc.traces)

    return results


# =========================================================================
# STEP 4: SAVE RESULTS
# =========================================================================

def save_results(results: dict):
    """Save test results to run folder."""
    print()
    print("=" * 60)
    print("STEP 3: SAVING RESULTS")
    print("=" * 60)

    # Save JSON results
    json_path = RUN_DIR / "results.json"
    with open(json_path, "w") as f:
        json.dump(results, f, indent=2, default=str)
    print(f"  Results: {json_path}")

    # Save human-readable summary
    summary_path = RUN_DIR / "summary.txt"
    with open(summary_path, "w") as f:
        f.write("L++ Calculator Test Results\n")
        f.write("=" * 40 + "\n")
        f.write(f"Run: {RUN_TIMESTAMP}\n")
        f.write(f"Timestamp: {results['timestamp']}\n")
        f.write(f"Passed: {results['summary']['passed']}\n")
        f.write(f"Failed: {results['summary']['failed']}\n")
        f.write(f"Total Transitions: {results['total_transitions']}\n")
        f.write("\nTests:\n")
        for i, t in enumerate(results["tests"], 1):
            status = "PASS" if t["passed"] else "FAIL"
            f.write(f"  {i}. [{status}] {t['name']}\n")
    print(f"  Summary: {summary_path}")

    # Update latest symlink
    latest_link = RESULTS_DIR / "latest"
    if latest_link.exists() or latest_link.is_symlink():
        latest_link.unlink()
    latest_link.symlink_to(RUN_DIR.name)
    print(f"  Latest: {latest_link} -> {RUN_DIR.name}")

    return json_path


# =========================================================================
# MAIN
# =========================================================================

def main():
    print()
    print("L++ Calculator - Compile & Test")
    print("=" * 60)
    print()

    # Step 1: Compile
    compile_calculator()

    # Step 2: Load compiled operator
    create_operator = load_operator()

    # Step 3: Run tests
    results = run_tests(create_operator)

    # Step 4: Save results
    save_results(results)

    # Final summary
    print()
    print("=" * 60)
    print("FINAL SUMMARY")
    print("=" * 60)
    passed = results["summary"]["passed"]
    failed = results["summary"]["failed"]
    total = passed + failed
    print(f"  Tests: {passed}/{total} passed")
    print(f"  Transitions: {results['total_transitions']}")
    print()

    return 0 if failed == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
