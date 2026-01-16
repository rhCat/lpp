"""
L++ Code Miner

Mine existing codebases to:
1. Extract hidden state machines (bones)
2. Evaluate sturdiness against golden rules
3. Analyze flesh (compute) efficiency

Usage:
    from lpp.miner import mine_project
    results = mine_project("/path/to/project")
"""

import ast
import os
from pathlib import Path
from typing import Dict, List, Any, Optional
from dataclasses import dataclass, field


@dataclass
class ExtractedBone:
    """A state machine extracted from code."""
    name: str
    states: List[str]
    source_file: str
    line_number: int
    has_entry: bool = False
    has_terminal: bool = False
    has_error: bool = False
    verdict: str = "UNKNOWN"


@dataclass
class FleshMetrics:
    """Metrics for a compute function."""
    name: str
    lines: int
    branches: int
    complexity: str  # LOW, MEDIUM, HIGH


@dataclass
class MiningResult:
    """Complete mining result for a file."""
    file_path: str
    bones: List[ExtractedBone] = field(default_factory=list)
    flesh: List[FleshMetrics] = field(default_factory=list)
    state_machine_classes: List[str] = field(default_factory=list)


def extract_bones(source: str, file_path: str) -> List[ExtractedBone]:
    """Extract state machine patterns from Python source."""
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return []

    bones = []

    for node in ast.walk(tree):
        if isinstance(node, ast.ClassDef):
            # Check if it's an Enum (likely states)
            is_enum = any(
                isinstance(base, ast.Name) and base.id == "Enum"
                for base in node.bases
            )
            if is_enum:
                # Extract enum members
                members = []
                for item in node.body:
                    if isinstance(item, ast.Assign):
                        for target in item.targets:
                            if isinstance(target, ast.Name):
                                members.append(target.id)

                if members:
                    bone = ExtractedBone(
                        name=node.name,
                        states=members,
                        source_file=file_path,
                        line_number=node.lineno
                    )

                    # Evaluate against golden rules
                    bone.has_entry = any(
                        s.upper() in ["IDLE", "INIT", "START", "INITIAL", "READY"]
                        for s in members
                    )
                    bone.has_terminal = any(
                        s.upper() in ["COMPLETE", "DONE", "FINISHED", "SUCCESS",
                                      "COMPLETED", "END", "FINAL"]
                        for s in members
                    )
                    bone.has_error = any(
                        s.upper() in ["ERROR", "FAILED", "FAILURE", "INVALID"]
                        for s in members
                    )

                    # Verdict
                    if bone.has_entry and bone.has_terminal and bone.has_error:
                        bone.verdict = "STURDY"
                    elif bone.has_entry and bone.has_terminal:
                        bone.verdict = "FRAGILE (no error handling)"
                    elif bone.has_entry:
                        bone.verdict = "INCOMPLETE (no terminal)"
                    else:
                        bone.verdict = "WEAK (no entry state)"

                    bones.append(bone)

    return bones


def analyze_flesh(source: str) -> List[FleshMetrics]:
    """Analyze compute function metrics."""
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return []

    metrics = []

    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef):
            # Calculate metrics
            lines = (node.end_lineno - node.lineno) if hasattr(node, 'end_lineno') else 0
            branch_types = (ast.If, ast.For, ast.While, ast.Try, ast.With)
            if hasattr(ast, 'Match'):  # Python 3.10+
                branch_types = branch_types + (ast.Match,)
            branches = sum(1 for n in ast.walk(node) if isinstance(n, branch_types))

            # Complexity rating
            if branches <= 2 and lines <= 20:
                complexity = "LOW"
            elif branches <= 5 and lines <= 50:
                complexity = "MEDIUM"
            else:
                complexity = "HIGH"

            metrics.append(FleshMetrics(
                name=node.name,
                lines=lines,
                branches=branches,
                complexity=complexity
            ))

    return metrics


def find_state_machine_classes(source: str) -> List[str]:
    """Find classes that appear to implement state machines."""
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return []

    sm_classes = []

    for node in ast.walk(tree):
        if isinstance(node, ast.ClassDef):
            methods = [n.name for n in node.body if isinstance(n, ast.FunctionDef)]
            attrs = [n.targets[0].id for n in node.body
                    if isinstance(n, ast.Assign) and n.targets
                    and isinstance(n.targets[0], ast.Name)]

            # Heuristics for state machine detection
            has_state_method = any("state" in m.lower() for m in methods)
            has_transition = any("transit" in m.lower() or "dispatch" in m.lower()
                                for m in methods)
            has_state_attr = any("state" in a.lower() for a in attrs)

            if has_state_method or has_transition or has_state_attr:
                sm_classes.append(node.name)

    return sm_classes


def mine_file(file_path: str) -> MiningResult:
    """Mine a single Python file."""
    result = MiningResult(file_path=file_path)

    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            source = f.read()
    except (IOError, UnicodeDecodeError):
        return result

    result.bones = extract_bones(source, file_path)
    result.flesh = analyze_flesh(source)
    result.state_machine_classes = find_state_machine_classes(source)

    return result


def mine_project(project_path: str, extensions: List[str] = None) -> Dict[str, Any]:
    """
    Mine an entire project for state machines.

    Args:
        project_path: Root directory to scan
        extensions: File extensions to scan (default: ['.py'])

    Returns:
        Mining report with all extracted bones and flesh metrics
    """
    if extensions is None:
        extensions = ['.py']

    project_path = Path(project_path)
    results = []

    # Scan all files
    for ext in extensions:
        for file_path in project_path.rglob(f"*{ext}"):
            # Skip common non-source directories
            if any(part.startswith('.') or part in ['__pycache__', 'node_modules',
                                                      'venv', '.git', 'build', 'dist']
                   for part in file_path.parts):
                continue

            result = mine_file(str(file_path))
            if result.bones or result.state_machine_classes:
                results.append(result)

    # Aggregate report
    all_bones = []
    all_sm_classes = []
    verdict_counts = {"STURDY": 0, "FRAGILE": 0, "INCOMPLETE": 0, "WEAK": 0}

    for r in results:
        all_bones.extend(r.bones)
        all_sm_classes.extend(r.state_machine_classes)
        for bone in r.bones:
            for verdict in verdict_counts:
                if verdict in bone.verdict:
                    verdict_counts[verdict] += 1
                    break

    return {
        "project": str(project_path),
        "files_with_state_machines": len(results),
        "total_bones_found": len(all_bones),
        "state_machine_classes": list(set(all_sm_classes)),
        "verdict_summary": verdict_counts,
        "bones": [
            {
                "name": b.name,
                "states": b.states,
                "file": b.source_file,
                "line": b.line_number,
                "verdict": b.verdict
            }
            for b in all_bones
        ]
    }


def print_mining_report(report: Dict[str, Any]):
    """Pretty print a mining report."""
    print("=" * 70)
    print(f"L++ CODE MINING REPORT: {report['project']}")
    print("=" * 70)

    print(f"\nFiles with state patterns: {report['files_with_state_machines']}")
    print(f"Total bones extracted: {report['total_bones_found']}")

    print("\n--- VERDICT SUMMARY ---")
    for verdict, count in report["verdict_summary"].items():
        bar = "" * count
        print(f"  {verdict:12} {count:3} {bar}")

    print("\n--- STATE MACHINE CLASSES ---")
    for cls in report["state_machine_classes"][:10]:
        print(f"  {cls}")

    print("\n--- EXTRACTED BONES ---")
    for bone in report["bones"]:
        print(f"\n  {bone['name']} ({bone['file']}:{bone['line']})")
        print(f"    States: {bone['states']}")
        print(f"    Verdict: {bone['verdict']}")

    print("\n" + "=" * 70)
