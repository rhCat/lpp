"""
COMPUTE units for the L++ Blueprint Differ

These are the pure computation functions that implement semantic diff/merge.
All functions are hermetic: input is params dict, output is result dict.
"""

import json
import copy
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple


# =============================================================================
# Change Types
# =============================================================================

class ChangeType:
    ADDED = "added"
    REMOVED = "removed"
    MODIFIED = "modified"
    UNCHANGED = "unchanged"


class ElementType:
    STATE = "state"
    TRANSITION = "transition"
    GATE = "gate"
    ACTION = "action"
    CONTEXT_PROPERTY = "context_property"
    ENTRY_STATE = "entry_state"
    TERMINAL_STATE = "terminal_state"
    METADATA = "metadata"


def make_change(
    element_type: str,
    change_type: str,
    key: str,
    left_value: Any = None,
    right_value: Any = None,
    details: str = None
) -> Dict[str, Any]:
    """Create a standardized change record."""
    change = {
        "element_type": element_type,
        "change_type": change_type,
        "key": key
    }
    if left_value is not None:
        change["left"] = left_value
    if right_value is not None:
        change["right"] = right_value
    if details:
        change["details"] = details
    return change


# =============================================================================
# Blueprint Loading
# =============================================================================

def load_blueprint(params: Dict[str, Any]) -> Dict[str, Any]:
    """Load an L++ blueprint from a JSON file."""
    path = params.get("path")
    side = params.get("side", "unknown")

    if not path:
        return {"blueprint": None, "path": None,
                "error": f"No path provided for {side}"}

    try:
        p = Path(path)
        if not p.exists():
            return {"blueprint": None, "path": None,
                    "error": f"File not found: {path}"}

        with open(p) as f:
            raw = json.load(f)

        bp = {
            "id": raw.get("id", "unknown"),
            "name": raw.get("name", "Unknown"),
            "version": raw.get("version", "0.0.0"),
            "description": raw.get("description", ""),
            "$schema": raw.get("$schema", ""),
            "states": raw.get("states", {}),
            "transitions": raw.get("transitions", []),
            "gates": raw.get("gates", {}),
            "actions": raw.get("actions", {}),
            "context_schema": raw.get("context_schema", {}),
            "entry_state": raw.get("entry_state"),
            "terminal_states": raw.get("terminal_states", []),
            "display": raw.get("display", {})
        }

        return {"blueprint": bp, "path": str(p), "error": None}
    except json.JSONDecodeError as e:
        return {"blueprint": None, "path": None,
                "error": f"Invalid JSON in {side}: {e}"}
    except Exception as e:
        return {"blueprint": None, "path": None, "error": str(e)}


def clear_all(params: Dict[str, Any]) -> Dict[str, Any]:
    """Clear all loaded blueprints and diff results."""
    return {
        "blueprint_left": None,
        "blueprint_right": None,
        "blueprint_base": None,
        "diff_result": None,
        "conflicts": None,
        "merged_blueprint": None,
        "formatted_diff": None,
        "json_patch": None
    }


# =============================================================================
# Semantic Diff Computation
# =============================================================================

def _diff_dict(
    left: Dict[str, Any],
    right: Dict[str, Any],
    element_type: str
) -> List[Dict[str, Any]]:
    """Diff two dictionaries (states, gates, actions, etc.)."""
    changes = []
    leftKeys = set(left.keys())
    rightKeys = set(right.keys())

    # Added
    for key in sorted(rightKeys - leftKeys):
        changes.append(make_change(
            element_type, ChangeType.ADDED, key,
            right_value=right[key]
        ))

    # Removed
    for key in sorted(leftKeys - rightKeys):
        changes.append(make_change(
            element_type, ChangeType.REMOVED, key,
            left_value=left[key]
        ))

    # Modified
    for key in sorted(leftKeys & rightKeys):
        if left[key] != right[key]:
            changes.append(make_change(
                element_type, ChangeType.MODIFIED, key,
                left_value=left[key],
                right_value=right[key]
            ))

    return changes


def _diff_transitions(
    left: List[Dict],
    right: List[Dict]
) -> List[Dict[str, Any]]:
    """Diff transition arrays using ID as key."""
    changes = []

    # Index by ID
    leftById = {t.get("id", f"idx_{i}"): t for i, t in enumerate(left)}
    rightById = {t.get("id", f"idx_{i}"): t for i, t in enumerate(right)}

    leftIds = set(leftById.keys())
    rightIds = set(rightById.keys())

    # Added
    for tid in sorted(rightIds - leftIds):
        changes.append(make_change(
            ElementType.TRANSITION, ChangeType.ADDED, tid,
            right_value=rightById[tid]
        ))

    # Removed
    for tid in sorted(leftIds - rightIds):
        changes.append(make_change(
            ElementType.TRANSITION, ChangeType.REMOVED, tid,
            left_value=leftById[tid]
        ))

    # Modified
    for tid in sorted(leftIds & rightIds):
        lt = leftById[tid]
        rt = rightById[tid]
        if lt != rt:
            # Compute detailed diff
            details = []
            for field in ["from", "to", "on_event", "gates", "gate", "actions"]:
                lv = lt.get(field)
                rv = rt.get(field)
                if lv != rv:
                    details.append(f"{field}: {lv} -> {rv}")
            changes.append(make_change(
                ElementType.TRANSITION, ChangeType.MODIFIED, tid,
                left_value=lt,
                right_value=rt,
                details="; ".join(details)
            ))

    return changes


def _diff_context_schema(
    left: Dict[str, Any],
    right: Dict[str, Any]
) -> List[Dict[str, Any]]:
    """Diff context_schema properties."""
    leftProps = left.get("properties", {})
    rightProps = right.get("properties", {})
    return _diff_dict(leftProps, rightProps, ElementType.CONTEXT_PROPERTY)


def _diff_terminal_states(
    left: List[str],
    right: List[str]
) -> List[Dict[str, Any]]:
    """Diff terminal_states arrays."""
    changes = []
    leftSet = set(left or [])
    rightSet = set(right or [])

    for state in sorted(rightSet - leftSet):
        changes.append(make_change(
            ElementType.TERMINAL_STATE, ChangeType.ADDED, state
        ))

    for state in sorted(leftSet - rightSet):
        changes.append(make_change(
            ElementType.TERMINAL_STATE, ChangeType.REMOVED, state
        ))

    return changes


def compute_diff(params: Dict[str, Any]) -> Dict[str, Any]:
    """Compute semantic diff between two blueprints."""
    left = params.get("left", {})
    right = params.get("right", {})

    if not left or not right:
        return {"diff": {"changes": [], "summary": {}, "identical": True}}

    changes = []

    # Metadata changes
    for field in ["id", "name", "version", "description", "$schema"]:
        lv = left.get(field)
        rv = right.get(field)
        if lv != rv:
            changes.append(make_change(
                ElementType.METADATA, ChangeType.MODIFIED, field,
                left_value=lv, right_value=rv
            ))

    # Entry state
    if left.get("entry_state") != right.get("entry_state"):
        changes.append(make_change(
            ElementType.ENTRY_STATE, ChangeType.MODIFIED, "entry_state",
            left_value=left.get("entry_state"),
            right_value=right.get("entry_state")
        ))

    # States
    changes.extend(_diff_dict(
        left.get("states", {}),
        right.get("states", {}),
        ElementType.STATE
    ))

    # Transitions
    changes.extend(_diff_transitions(
        left.get("transitions", []),
        right.get("transitions", [])
    ))

    # Gates
    changes.extend(_diff_dict(
        left.get("gates", {}),
        right.get("gates", {}),
        ElementType.GATE
    ))

    # Actions
    changes.extend(_diff_dict(
        left.get("actions", {}),
        right.get("actions", {}),
        ElementType.ACTION
    ))

    # Context schema
    changes.extend(_diff_context_schema(
        left.get("context_schema", {}),
        right.get("context_schema", {})
    ))

    # Terminal states
    changes.extend(_diff_terminal_states(
        left.get("terminal_states", []),
        right.get("terminal_states", [])
    ))

    # Summary
    summary = {
        "total": len(changes),
        "added": sum(1 for c in changes if c["change_type"] == ChangeType.ADDED),
        "removed": sum(1 for c in changes
                       if c["change_type"] == ChangeType.REMOVED),
        "modified": sum(1 for c in changes
                        if c["change_type"] == ChangeType.MODIFIED),
        "by_type": {}
    }

    for c in changes:
        et = c["element_type"]
        if et not in summary["by_type"]:
            summary["by_type"][et] = {"added": 0, "removed": 0, "modified": 0}
        summary["by_type"][et][c["change_type"]] += 1

    return {
        "diff": {
            "changes": changes,
            "summary": summary,
            "identical": len(changes) == 0
        }
    }


# =============================================================================
# Diff Formatting
# =============================================================================

def format_diff(params: Dict[str, Any]) -> Dict[str, Any]:
    """Format diff for display."""
    diff = params.get("diff", {})
    fmt = params.get("format", "unified")
    pathLeft = params.get("path_left", "left")
    pathRight = params.get("path_right", "right")

    if not diff:
        return {"output": "No diff available", "format": fmt}

    changes = diff.get("changes", [])
    summary = diff.get("summary", {})

    if diff.get("identical"):
        return {"output": "Blueprints are identical.", "format": fmt}

    lines = []

    if fmt == "summary":
        lines.append("=" * 70)
        lines.append("  L++ Blueprint Diff Summary")
        lines.append("=" * 70)
        lines.append("")
        lines.append(f"  Left:  {pathLeft}")
        lines.append(f"  Right: {pathRight}")
        lines.append("")
        lines.append("-" * 70)
        lines.append(f"  Total Changes: {summary.get('total', 0)}")
        lines.append(f"    Added:    {summary.get('added', 0)}")
        lines.append(f"    Removed:  {summary.get('removed', 0)}")
        lines.append(f"    Modified: {summary.get('modified', 0)}")
        lines.append("")

        byType = summary.get("by_type", {})
        if byType:
            lines.append("-" * 70)
            lines.append("  Changes by Element Type:")
            for et, counts in sorted(byType.items()):
                total = sum(counts.values())
                lines.append(f"    {et}: {total} "
                             f"(+{counts['added']} -{counts['removed']} "
                             f"~{counts['modified']})")

        lines.append("=" * 70)

    else:  # unified
        lines.append("=" * 70)
        lines.append("  L++ Blueprint Diff (Unified)")
        lines.append("=" * 70)
        lines.append(f"  --- {pathLeft}")
        lines.append(f"  +++ {pathRight}")
        lines.append("")

        # Group by element type
        byType: Dict[str, List] = {}
        for c in changes:
            et = c["element_type"]
            if et not in byType:
                byType[et] = []
            byType[et].append(c)

        typeOrder = [
            ElementType.METADATA,
            ElementType.ENTRY_STATE,
            ElementType.STATE,
            ElementType.TRANSITION,
            ElementType.GATE,
            ElementType.ACTION,
            ElementType.CONTEXT_PROPERTY,
            ElementType.TERMINAL_STATE
        ]

        for et in typeOrder:
            if et not in byType:
                continue
            lines.append("-" * 70)
            lines.append(f"  [{et.upper()}]")

            for c in byType[et]:
                ct = c["change_type"]
                key = c["key"]

                if ct == ChangeType.ADDED:
                    lines.append(f"    + {key}")
                    if "right" in c:
                        val = _format_value(c["right"])
                        for line in val.split("\n"):
                            lines.append(f"      {line}")
                elif ct == ChangeType.REMOVED:
                    lines.append(f"    - {key}")
                    if "left" in c:
                        val = _format_value(c["left"])
                        for line in val.split("\n"):
                            lines.append(f"      {line}")
                elif ct == ChangeType.MODIFIED:
                    lines.append(f"    ~ {key}")
                    if c.get("details"):
                        lines.append(f"      {c['details']}")
                    elif "left" in c and "right" in c:
                        lines.append(
                            f"      left:  {_format_value_inline(c['left'])}")
                        lines.append(
                            f"      right: {_format_value_inline(c['right'])}")
            lines.append("")

        lines.append("=" * 70)
        lines.append(f"  Summary: +{summary.get('added', 0)} "
                     f"-{summary.get('removed', 0)} "
                     f"~{summary.get('modified', 0)}")
        lines.append("=" * 70)

    return {"output": "\n".join(lines), "format": fmt}


def _format_value(val: Any, indent: int = 0) -> str:
    """Format a value for display."""
    if isinstance(val, dict):
        return json.dumps(val, indent=2)
    elif isinstance(val, list):
        return json.dumps(val, indent=2)
    else:
        return str(val)


def _format_value_inline(val: Any) -> str:
    """Format a value for inline display."""
    if isinstance(val, dict):
        return json.dumps(val, separators=(",", ":"))
    elif isinstance(val, list):
        return json.dumps(val, separators=(",", ":"))
    else:
        return str(val)


# =============================================================================
# JSON Patch Generation (RFC 6902)
# =============================================================================

def generate_json_patch(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate RFC 6902 JSON patch from diff."""
    diff = params.get("diff", {})
    changes = diff.get("changes", [])

    if not changes:
        return {"patch": [], "formatted": "No changes - empty patch"}

    patch = []

    for c in changes:
        et = c["element_type"]
        ct = c["change_type"]
        key = c["key"]

        # Compute JSON path
        if et == ElementType.STATE:
            path = f"/states/{key}"
        elif et == ElementType.GATE:
            path = f"/gates/{key}"
        elif et == ElementType.ACTION:
            path = f"/actions/{key}"
        elif et == ElementType.CONTEXT_PROPERTY:
            path = f"/context_schema/properties/{key}"
        elif et == ElementType.TRANSITION:
            path = f"/transitions/{key}"  # By ID reference
        elif et == ElementType.ENTRY_STATE:
            path = "/entry_state"
        elif et == ElementType.TERMINAL_STATE:
            path = f"/terminal_states/{key}"
        elif et == ElementType.METADATA:
            path = f"/{key}"
        else:
            path = f"/{et}/{key}"

        if ct == ChangeType.ADDED:
            patch.append({
                "op": "add",
                "path": path,
                "value": c.get("right")
            })
        elif ct == ChangeType.REMOVED:
            patch.append({
                "op": "remove",
                "path": path
            })
        elif ct == ChangeType.MODIFIED:
            patch.append({
                "op": "replace",
                "path": path,
                "value": c.get("right")
            })

    formatted = json.dumps(patch, indent=2)
    return {"patch": patch, "formatted": formatted}


# =============================================================================
# Conflict Detection
# =============================================================================

def detect_conflicts(params: Dict[str, Any]) -> Dict[str, Any]:
    """Detect merge conflicts between blueprints."""
    left = params.get("left", {})
    right = params.get("right", {})
    base = params.get("base")  # Optional for 3-way merge
    diff = params.get("diff", {})

    conflicts = []
    changes = diff.get("changes", [])

    if not base:
        # Two-way merge: conflicts are elements modified on both sides
        # Since we only have left->right diff, conflicts are modifications
        # to elements where both sides differ from a "theoretical" base
        # For 2-way, we flag any modification as potential conflict
        for c in changes:
            if c["change_type"] == ChangeType.MODIFIED:
                conflicts.append({
                    "element_type": c["element_type"],
                    "key": c["key"],
                    "left_value": c.get("left"),
                    "right_value": c.get("right"),
                    "reason": "Element modified (2-way diff)"
                })
    else:
        # Three-way merge: conflict when both left and right changed same
        # element differently from base
        leftDiff = compute_diff({"left": base, "right": left})["diff"]
        rightDiff = compute_diff({"left": base, "right": right})["diff"]

        leftChanges = {(c["element_type"], c["key"]): c
                       for c in leftDiff.get("changes", [])}
        rightChanges = {(c["element_type"], c["key"]): c
                        for c in rightDiff.get("changes", [])}

        # Conflict: both modified same element differently
        for key in set(leftChanges.keys()) & set(rightChanges.keys()):
            lc = leftChanges[key]
            rc = rightChanges[key]

            # Same change = no conflict
            if lc.get("right") == rc.get("right"):
                continue

            # Different changes = conflict
            conflicts.append({
                "element_type": key[0],
                "key": key[1],
                "base_value": lc.get("left"),
                "left_value": lc.get("right"),
                "right_value": rc.get("right"),
                "reason": "Both sides modified differently from base"
            })

    return {"conflicts": conflicts}


# =============================================================================
# Blueprint Merging
# =============================================================================

def merge_blueprints(params: Dict[str, Any]) -> Dict[str, Any]:
    """Merge two blueprints with specified strategy."""
    left = params.get("left", {})
    right = params.get("right", {})
    base = params.get("base")
    strategy = params.get("strategy", "auto")
    conflicts = params.get("conflicts", [])

    # Start with left as base
    merged = copy.deepcopy(left)

    # Merge metadata (prefer right for auto/take_right)
    if strategy in ("auto", "take_right"):
        for field in ["id", "name", "version", "description"]:
            if right.get(field):
                merged[field] = right[field]
        merged["version"] = _bump_version(left.get("version", "0.0.0"))

    # Merge states
    merged["states"] = _merge_dict(
        left.get("states", {}),
        right.get("states", {}),
        strategy, conflicts, ElementType.STATE
    )

    # Merge gates
    merged["gates"] = _merge_dict(
        left.get("gates", {}),
        right.get("gates", {}),
        strategy, conflicts, ElementType.GATE
    )

    # Merge actions
    merged["actions"] = _merge_dict(
        left.get("actions", {}),
        right.get("actions", {}),
        strategy, conflicts, ElementType.ACTION
    )

    # Merge transitions
    merged["transitions"] = _merge_transitions(
        left.get("transitions", []),
        right.get("transitions", []),
        strategy, conflicts
    )

    # Merge context schema
    leftProps = left.get("context_schema", {}).get("properties", {})
    rightProps = right.get("context_schema", {}).get("properties", {})
    mergedProps = _merge_dict(
        leftProps, rightProps, strategy, conflicts, ElementType.CONTEXT_PROPERTY
    )
    merged["context_schema"] = {"properties": mergedProps}

    # Merge terminal states (union for auto)
    leftTerms = set(left.get("terminal_states", []))
    rightTerms = set(right.get("terminal_states", []))
    if strategy == "take_left":
        merged["terminal_states"] = list(leftTerms)
    elif strategy == "take_right":
        merged["terminal_states"] = list(rightTerms)
    else:
        merged["terminal_states"] = sorted(leftTerms | rightTerms)

    # Entry state
    if strategy == "take_right" and right.get("entry_state"):
        merged["entry_state"] = right["entry_state"]

    return {"merged": merged, "strategy": strategy}


def _merge_dict(
    left: Dict[str, Any],
    right: Dict[str, Any],
    strategy: str,
    conflicts: List[Dict],
    element_type: str
) -> Dict[str, Any]:
    """Merge two dictionaries based on strategy."""
    conflictKeys = {c["key"] for c in conflicts
                    if c["element_type"] == element_type}

    result = copy.deepcopy(left)

    # Add new elements from right
    for key, value in right.items():
        if key not in result:
            result[key] = copy.deepcopy(value)
        elif key in conflictKeys:
            # Conflict resolution
            if strategy == "take_right":
                result[key] = copy.deepcopy(value)
            # take_left: keep left (already in result)
        else:
            # Non-conflicting modification - take right for auto
            if strategy in ("auto", "take_right"):
                if left.get(key) != value:
                    result[key] = copy.deepcopy(value)

    return result


def _merge_transitions(
    left: List[Dict],
    right: List[Dict],
    strategy: str,
    conflicts: List[Dict]
) -> List[Dict]:
    """Merge transition arrays."""
    conflictIds = {c["key"] for c in conflicts
                   if c["element_type"] == ElementType.TRANSITION}

    leftById = {t.get("id", f"idx_{i}"): t for i, t in enumerate(left)}
    rightById = {t.get("id", f"idx_{i}"): t for i, t in enumerate(right)}

    result = []
    seenIds = set()

    # Add all from left
    for t in left:
        tid = t.get("id")
        if tid:
            seenIds.add(tid)
            if tid in conflictIds and strategy == "take_right":
                result.append(copy.deepcopy(rightById.get(tid, t)))
            else:
                result.append(copy.deepcopy(t))
        else:
            result.append(copy.deepcopy(t))

    # Add new from right
    for t in right:
        tid = t.get("id")
        if tid and tid not in seenIds:
            result.append(copy.deepcopy(t))

    return result


def _bump_version(version: str) -> str:
    """Bump patch version number."""
    try:
        parts = version.split(".")
        if len(parts) >= 3:
            parts[2] = str(int(parts[2]) + 1)
            return ".".join(parts)
    except ValueError:
        pass
    return version + "-merged"


# =============================================================================
# Export Merged Blueprint
# =============================================================================

def export_merged(params: Dict[str, Any]) -> Dict[str, Any]:
    """Export merged blueprint to file."""
    blueprint = params.get("blueprint")
    path = params.get("path")

    if not blueprint:
        return {"path": None, "error": "No merged blueprint to export"}

    if not path:
        return {"path": None, "error": "No export path specified"}

    try:
        p = Path(path)
        p.parent.mkdir(parents=True, exist_ok=True)

        with open(p, "w") as f:
            json.dump(blueprint, f, indent=2)

        return {"path": str(p)}
    except Exception as e:
        return {"path": None, "error": str(e)}


# =============================================================================
# COMPUTE REGISTRY - Maps compute_unit names to functions
# =============================================================================

COMPUTE_REGISTRY = {
    "diff:load_blueprint": load_blueprint,
    "diff:clear_all": clear_all,
    "diff:compute_diff": compute_diff,
    "diff:format_diff": format_diff,
    "diff:generate_json_patch": generate_json_patch,
    "diff:detect_conflicts": detect_conflicts,
    "diff:merge_blueprints": merge_blueprints,
    "diff:export_merged": export_merged,
}
