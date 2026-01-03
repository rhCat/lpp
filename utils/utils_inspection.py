#!/usr/bin/env python3
"""
L++ Utils Inspection - Consolidated Blueprint Analysis Tool

A comprehensive analysis script that discovers, lints, and reports on all
L++ blueprints in the utils/ directory. Consolidates functionality from:
- blueprint_linter: Structural linting and metrics
- compliance_checker: Policy compliance verification
- doc_generator: Documentation metadata extraction

Usage:
    python utils/utils_inspection.py [--output PATH] [--verbose]

Can also be imported and called programmatically:
    from utils.utils_inspection import inspect_all
    results = inspect_all()
"""

import argparse
import json
import sys
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

# Determine paths
HERE = Path(__file__).parent
ROOT = HERE.parent
SRC_PATH = ROOT / "src"

# Add L++ framework to path
if str(SRC_PATH) not in sys.path:
    sys.path.insert(0, str(SRC_PATH))


# =============================================================================
# BLUEPRINT DISCOVERY
# =============================================================================

def discover_blueprints(utils_dir: Path = None) -> List[Dict[str, Any]]:
    """
    Discover all L++ blueprints in utils/ subdirectories.

    Each tool typically has a main .json blueprint file at its root.
    Excludes results/, tests/, migrations/, policies/ subdirectories.
    """
    if utils_dir is None:
        utils_dir = HERE

    blueprints = []
    exclude_dirs = {"results", "tests", "migrations", "policies", "registry",
                    "__pycache__", ".git"}

    for tool_dir in sorted(utils_dir.iterdir()):
        if not tool_dir.is_dir():
            continue
        if tool_dir.name.startswith(".") or tool_dir.name in exclude_dirs:
            continue

        # Look for main blueprint JSON in tool root
        for json_file in tool_dir.glob("*.json"):
            # Skip decoded results and other non-blueprint files
            if "_decoded" in json_file.name or "_functions" in json_file.name:
                continue
            if json_file.name.startswith("_"):
                continue

            # Verify it looks like a blueprint
            try:
                with open(json_file) as f:
                    data = json.load(f)

                # Check for blueprint markers
                if "states" in data and "transitions" in data:
                    blueprints.append({
                        "path": str(json_file),
                        "tool_name": tool_dir.name,
                        "file_name": json_file.name,
                        "id": data.get("id", "unknown"),
                        "name": data.get("name", json_file.stem),
                        "version": data.get("version", "0.0.0"),
                        "raw": data
                    })
            except (json.JSONDecodeError, IOError):
                continue

    return blueprints


# =============================================================================
# LINTING (using blueprint_linter compute units)
# =============================================================================

def run_linting(blueprint_info: Dict[str, Any], verbose: bool = False
                ) -> Dict[str, Any]:
    """
    Run linting on a blueprint using blueprint_linter compute units.
    """
    try:
        from blueprint_linter.src.linter_compute import (
            load_blueprint,
            check_unreachable_states,
            check_dead_end_states,
            check_unused_gates,
            check_unused_actions,
            check_unused_context,
            check_orphaned_transitions,
            check_missing_gate_refs,
            check_missing_action_refs,
            check_duplicate_ids,
            check_naming_conventions,
            compute_metrics,
            compute_summary
        )
    except ImportError as e:
        return {
            "success": False,
            "error": f"Failed to import linter: {e}",
            "findings": [],
            "metrics": {},
            "summary": {}
        }

    # Load blueprint
    result = load_blueprint({"path": blueprint_info["path"]})
    if result.get("error"):
        return {
            "success": False,
            "error": result["error"],
            "findings": [],
            "metrics": {},
            "summary": {}
        }

    bp = result["blueprint"]
    findings = []

    # Run all lint checks
    checks = [
        check_unreachable_states,
        check_dead_end_states,
        check_unused_gates,
        check_unused_actions,
        check_unused_context,
        check_orphaned_transitions,
        check_missing_gate_refs,
        check_missing_action_refs,
        check_duplicate_ids,
        check_naming_conventions
    ]

    for check_fn in checks:
        try:
            res = check_fn({"blueprint": bp, "findings": findings})
            findings = res.get("findings", findings)
        except Exception as e:
            if verbose:
                print(f"    Warning: {check_fn.__name__} failed: {e}")

    # Compute metrics
    metrics_result = compute_metrics({"blueprint": bp})
    metrics = metrics_result.get("metrics", {})

    # Compute summary
    summary_result = compute_summary({"findings": findings})
    summary = summary_result.get("summary", {})

    return {
        "success": True,
        "error": None,
        "findings": findings,
        "metrics": metrics,
        "summary": summary
    }


# =============================================================================
# COMPLIANCE CHECKING (using compliance_checker compute units)
# =============================================================================

def run_compliance(blueprint_info: Dict[str, Any], verbose: bool = False
                   ) -> Dict[str, Any]:
    """
    Run compliance checks using compliance_checker compute units.
    """
    try:
        from compliance_checker.src.compliance_compute import (
            load_blueprint as compliance_load_blueprint,
            load_policies,
            check_all_policies,
            calculate_score
        )
    except ImportError as e:
        return {
            "success": False,
            "error": f"Failed to import compliance checker: {e}",
            "findings": [],
            "score": None,
            "summary": {}
        }

    # Load blueprint
    bp_result = compliance_load_blueprint({"path": blueprint_info["path"]})
    if bp_result.get("error"):
        return {
            "success": False,
            "error": bp_result["error"],
            "findings": [],
            "score": None,
            "summary": {}
        }

    # Load policies from default directory
    policies_result = load_policies({})
    policies = policies_result.get("policies", [])

    if not policies:
        return {
            "success": True,
            "error": None,
            "findings": [],
            "score": 100,
            "summary": {"passed": 0, "failed": 0}
        }

    # Run compliance checks
    check_result = check_all_policies({
        "blueprint": bp_result["blueprint"],
        "policies": policies
    })

    findings = check_result.get("findings", [])
    summary = check_result.get("summary", {})

    # Calculate score
    score_result = calculate_score({"findings": findings})
    score = score_result.get("score", 100)

    return {
        "success": True,
        "error": None,
        "findings": findings,
        "score": score,
        "summary": summary
    }


# =============================================================================
# DOCUMENTATION METADATA (using doc_generator compute units)
# =============================================================================

def extract_doc_metadata(blueprint_info: Dict[str, Any], verbose: bool = False
                         ) -> Dict[str, Any]:
    """
    Extract documentation metadata using doc_generator compute units.
    """
    try:
        from doc_generator.src.doc_compute import extract_metadata
    except ImportError as e:
        # Fall back to manual extraction
        return _extract_metadata_manual(blueprint_info)

    bp = blueprint_info.get("raw", {})
    result = extract_metadata({"blueprint": bp})
    return result.get("metadata", {})


def _extract_metadata_manual(blueprint_info: Dict[str, Any]) -> Dict[str, Any]:
    """Manual metadata extraction fallback."""
    bp = blueprint_info.get("raw", {})
    return {
        "name": bp.get("name", "Untitled"),
        "id": bp.get("id", "unknown"),
        "version": bp.get("version", "0.0.0"),
        "description": bp.get("description", ""),
        "schema": bp.get("$schema", "lpp/v0.1.2"),
        "state_count": len(bp.get("states", {})),
        "transition_count": len(bp.get("transitions", [])),
        "gate_count": len(bp.get("gates", {})),
        "action_count": len(bp.get("actions", {})),
        "entry_state": bp.get("entry_state", ""),
        "terminal_states": bp.get("terminal_states", [])
    }


# =============================================================================
# COMPLEXITY CALCULATION
# =============================================================================

def calculate_complexity(blueprint_info: Dict[str, Any]) -> Dict[str, int]:
    """
    Calculate complexity metrics for a blueprint.

    Cyclomatic complexity: E - N + 2P
    Where E = edges (transitions), N = nodes (states), P = connected components
    """
    bp = blueprint_info.get("raw", {})

    states = bp.get("states", {})
    transitions = bp.get("transitions", [])
    gates = bp.get("gates", {})
    actions = bp.get("actions", {})

    num_states = len(states)
    num_transitions = len(transitions)
    num_gates = len(gates)
    num_actions = len(actions)

    # Cyclomatic complexity: transitions - states + 2
    cyclomatic = max(1, num_transitions - num_states + 2)

    # Unique events
    events = set()
    for t in transitions:
        event = t.get("on_event")
        if event:
            events.add(event)

    # Context properties
    ctx_schema = bp.get("context_schema", {})
    props = ctx_schema.get("properties", {})

    return {
        "states": num_states,
        "transitions": num_transitions,
        "gates": num_gates,
        "actions": num_actions,
        "events": len(events),
        "context_properties": len(props),
        "cyclomatic_complexity": cyclomatic
    }


# =============================================================================
# MAIN INSPECTION FUNCTION
# =============================================================================

def inspect_all(output_path: str = None, verbose: bool = False
                ) -> Dict[str, Any]:
    """
    Run comprehensive inspection on all discovered blueprints.

    Returns a dictionary with:
    - blueprints: List of discovered blueprints with analysis results
    - totals: Aggregate statistics
    - report_path: Path where report was written (if output_path provided)
    """
    if output_path is None:
        output_path = str(HERE / "analysis_report.md")

    if verbose:
        print("\n  L++ Utils Inspection")
        print("  " + "=" * 50)

    # Discover blueprints
    if verbose:
        print("\n  [1/5] Discovering blueprints...")

    blueprints = discover_blueprints()

    if verbose:
        print(f"        Found {len(blueprints)} blueprints")

    # Initialize totals
    totals = {
        "blueprints": len(blueprints),
        "states": 0,
        "transitions": 0,
        "gates": 0,
        "actions": 0,
        "lint_errors": 0,
        "lint_warnings": 0,
        "lint_info": 0,
        "compliance_passed": 0,
        "compliance_failed": 0,
        "avg_complexity": 0
    }

    results = []
    complexities = []

    # Process each blueprint
    for i, bp_info in enumerate(blueprints, 1):
        if verbose:
            print(f"\n  [{i+1}/{len(blueprints)+1}] Analyzing {bp_info['tool_name']}...")

        # Calculate complexity
        complexity = calculate_complexity(bp_info)
        complexities.append(complexity["cyclomatic_complexity"])

        totals["states"] += complexity["states"]
        totals["transitions"] += complexity["transitions"]
        totals["gates"] += complexity["gates"]
        totals["actions"] += complexity["actions"]

        # Run linting
        if verbose:
            print(f"        Running linter...")
        lint_result = run_linting(bp_info, verbose)

        if lint_result["success"]:
            totals["lint_errors"] += lint_result["summary"].get("error", 0)
            totals["lint_warnings"] += lint_result["summary"].get("warning", 0)
            totals["lint_info"] += lint_result["summary"].get("info", 0)

        # Run compliance
        if verbose:
            print(f"        Running compliance checks...")
        compliance_result = run_compliance(bp_info, verbose)

        if compliance_result["success"]:
            totals["compliance_passed"] += compliance_result["summary"].get(
                "passed", 0)
            totals["compliance_failed"] += compliance_result["summary"].get(
                "failed", 0)

        # Extract metadata
        if verbose:
            print(f"        Extracting metadata...")
        metadata = extract_doc_metadata(bp_info, verbose)

        results.append({
            "tool_name": bp_info["tool_name"],
            "file_name": bp_info["file_name"],
            "path": bp_info["path"],
            "id": bp_info["id"],
            "name": bp_info["name"],
            "version": bp_info["version"],
            "complexity": complexity,
            "lint": lint_result,
            "compliance": compliance_result,
            "metadata": metadata
        })

    # Calculate average complexity
    if complexities:
        totals["avg_complexity"] = round(sum(complexities) / len(complexities), 2)

    # Generate report
    if verbose:
        print(f"\n  [Final] Generating report...")

    report = generate_report(results, totals)

    # Write report
    report_path = Path(output_path)
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(report)

    if verbose:
        print(f"        Report written to: {report_path}")
        print("\n  " + "=" * 50)
        print(f"  Summary: {totals['blueprints']} blueprints analyzed")
        print(f"           {totals['lint_errors']} errors, "
              f"{totals['lint_warnings']} warnings")
        print(f"           Average complexity: {totals['avg_complexity']}")
        print()

    return {
        "blueprints": results,
        "totals": totals,
        "report_path": str(report_path)
    }


# =============================================================================
# REPORT GENERATION
# =============================================================================

def generate_report(results: List[Dict[str, Any]],
                    totals: Dict[str, Any]) -> str:
    """Generate a comprehensive Markdown analysis report."""
    lines = []

    # Header
    lines.append("# L++ Blueprint Analysis Report")
    lines.append("")
    lines.append(f"**Generated:** {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    lines.append("")

    # Summary Statistics
    lines.append("## Summary Statistics")
    lines.append("")
    lines.append("| Metric | Value |")
    lines.append("|--------|-------|")
    lines.append(f"| Total Blueprints | {totals['blueprints']} |")
    lines.append(f"| Total States | {totals['states']} |")
    lines.append(f"| Total Transitions | {totals['transitions']} |")
    lines.append(f"| Total Gates | {totals['gates']} |")
    lines.append(f"| Total Actions | {totals['actions']} |")
    lines.append(f"| Avg Cyclomatic Complexity | {totals['avg_complexity']} |")
    lines.append("")

    # Lint Summary
    lines.append("### Lint Summary")
    lines.append("")
    lines.append("| Severity | Count |")
    lines.append("|----------|-------|")
    lines.append(f"| Errors | {totals['lint_errors']} |")
    lines.append(f"| Warnings | {totals['lint_warnings']} |")
    lines.append(f"| Info | {totals['lint_info']} |")
    lines.append("")

    # Compliance Summary
    total_compliance = totals['compliance_passed'] + totals['compliance_failed']
    if total_compliance > 0:
        compliance_rate = round(
            (totals['compliance_passed'] / total_compliance) * 100, 1)
    else:
        compliance_rate = 100

    lines.append("### Compliance Summary")
    lines.append("")
    lines.append("| Metric | Value |")
    lines.append("|--------|-------|")
    lines.append(f"| Checks Passed | {totals['compliance_passed']} |")
    lines.append(f"| Checks Failed | {totals['compliance_failed']} |")
    lines.append(f"| Compliance Rate | {compliance_rate}% |")
    lines.append("")

    # Per-Tool Status Table
    lines.append("## Per-Tool Status")
    lines.append("")
    lines.append("| Tool | Version | States | Transitions | Complexity | "
                 "Lint Status | Compliance |")
    lines.append("|------|---------|--------|-------------|------------|"
                 "------------|------------|")

    for r in results:
        tool = r["tool_name"]
        version = r["version"]
        states = r["complexity"]["states"]
        trans = r["complexity"]["transitions"]
        cc = r["complexity"]["cyclomatic_complexity"]

        # Lint status
        if r["lint"]["success"]:
            errs = r["lint"]["summary"].get("error", 0)
            warns = r["lint"]["summary"].get("warning", 0)
            if errs > 0:
                lint_status = f"E:{errs} W:{warns}"
            elif warns > 0:
                lint_status = f"W:{warns}"
            else:
                lint_status = "PASS"
        else:
            lint_status = "FAIL"

        # Compliance status
        if r["compliance"]["success"]:
            score = r["compliance"]["score"]
            if score is not None:
                compliance_status = f"{score}%"
            else:
                compliance_status = "N/A"
        else:
            compliance_status = "FAIL"

        lines.append(f"| {tool} | {version} | {states} | {trans} | {cc} | "
                     f"{lint_status} | {compliance_status} |")

    lines.append("")

    # Detailed Lint Findings
    all_findings = []
    for r in results:
        if r["lint"]["success"]:
            for f in r["lint"]["findings"]:
                f["tool"] = r["tool_name"]
                all_findings.append(f)

    errors = [f for f in all_findings if f.get("severity") == "error"]
    warnings = [f for f in all_findings if f.get("severity") == "warning"]

    if errors or warnings:
        lines.append("## Lint Findings")
        lines.append("")

    if errors:
        lines.append("### Errors")
        lines.append("")
        for f in errors:
            lines.append(f"- **{f['tool']}** [{f.get('code', '?')}]: "
                         f"{f.get('message', '')}")
            if f.get("location"):
                lines.append(f"  - Location: `{f['location']}`")
            if f.get("suggestion"):
                lines.append(f"  - Suggestion: {f['suggestion']}")
        lines.append("")

    if warnings:
        lines.append("### Warnings")
        lines.append("")
        for f in warnings:
            lines.append(f"- **{f['tool']}** [{f.get('code', '?')}]: "
                         f"{f.get('message', '')}")
            if f.get("suggestion"):
                lines.append(f"  - Suggestion: {f['suggestion']}")
        lines.append("")

    # Compliance Results
    compliance_issues = []
    for r in results:
        if r["compliance"]["success"]:
            for f in r["compliance"]["findings"]:
                if not f.get("passed") and f.get("severity") != "info":
                    f["tool"] = r["tool_name"]
                    compliance_issues.append(f)

    if compliance_issues:
        lines.append("## Compliance Issues")
        lines.append("")
        for f in compliance_issues:
            lines.append(f"- **{f['tool']}** [{f.get('policy_id', '?')}]: "
                         f"{f.get('message', '')}")
            if f.get("remediation"):
                lines.append(f"  - Fix: {f['remediation']}")
        lines.append("")

    # Footer
    lines.append("---")
    lines.append("")
    lines.append("_Generated by L++ Utils Inspection_")
    lines.append("")

    return "\n".join(lines)


# =============================================================================
# CLI INTERFACE
# =============================================================================

def main():
    """CLI entry point."""
    parser = argparse.ArgumentParser(
        description="L++ Blueprint Analysis Tool - Inspects all blueprints "
                    "in utils/ directory",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
    python utils/utils_inspection.py
    python utils/utils_inspection.py --verbose
    python utils/utils_inspection.py --output reports/analysis.md --verbose
        """
    )

    parser.add_argument(
        "--output", "-o",
        default=str(HERE / "analysis_report.md"),
        help="Output path for the analysis report (default: utils/analysis_report.md)"
    )

    parser.add_argument(
        "--verbose", "-v",
        action="store_true",
        help="Enable verbose output during analysis"
    )

    args = parser.parse_args()

    try:
        result = inspect_all(output_path=args.output, verbose=args.verbose)

        # Print final summary if not verbose (verbose already prints it)
        if not args.verbose:
            print(f"\nAnalysis complete. Report written to: {result['report_path']}")
            print(f"  Blueprints: {result['totals']['blueprints']}")
            print(f"  Lint Errors: {result['totals']['lint_errors']}")
            print(f"  Lint Warnings: {result['totals']['lint_warnings']}")

        # Exit with error code if there are lint errors
        if result['totals']['lint_errors'] > 0:
            sys.exit(1)

    except Exception as e:
        print(f"\nError during analysis: {e}", file=sys.stderr)
        sys.exit(2)


if __name__ == "__main__":
    main()
