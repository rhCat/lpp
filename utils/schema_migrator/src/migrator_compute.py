"""
COMPUTE units for the L++ Schema Migrator.

These are the pure computation functions that implement schema migration.
All functions are hermetic: input is params dict, output is result dict.
"""

import json
import re
import copy
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple
from packaging import version


# =============================================================================
# Schema Version Constants
# =============================================================================

SCHEMA_VERSIONS = ["lpp/v0.1.0", "lpp/v0.1.1", "lpp/v0.1.2"]
LATEST_VERSION = "lpp/v0.1.2"

# Path to custom migrations directory
MIGRATIONS_DIR = Path(__file__).parent.parent / "migrations"


# =============================================================================
# Migration Change Types
# =============================================================================

class ChangeType:
    ADD_FIELD = "add_field"
    REMOVE_FIELD = "remove_field"
    RENAME_FIELD = "rename_field"
    CONVERT_TYPE = "convert_type"
    MOVE_FIELD = "move_field"
    TRANSFORM_VALUE = "transform_value"
    RENAME_EVENT = "rename_event"
    MERGE_FIELDS = "merge_fields"
    SPLIT_FIELD = "split_field"


# =============================================================================
# Built-in Migration Definitions
# =============================================================================

BUILTIN_MIGRATIONS = {
    "lpp/v0.1.0->lpp/v0.1.1": {
        "from_version": "lpp/v0.1.0",
        "to_version": "lpp/v0.1.1",
        "description": "Standardize on_event and context_schema",
        "changes": [
            {
                "type": ChangeType.RENAME_FIELD,
                "path": "transitions[*]",
                "from": "event",
                "to": "on_event"
            },
            {
                "type": ChangeType.RENAME_FIELD,
                "path": "",
                "from": "context",
                "to": "context_schema"
            },
            {
                "type": ChangeType.ADD_FIELD,
                "path": "context_schema",
                "field": "properties",
                "default": {},
                "condition": "missing"
            }
        ]
    },
    "lpp/v0.1.1->lpp/v0.1.2": {
        "from_version": "lpp/v0.1.1",
        "to_version": "lpp/v0.1.2",
        "description": "Trinity Refinement: Rename guard to gates, add display",
        "changes": [
            {
                "type": ChangeType.RENAME_FIELD,
                "path": "transitions[*]",
                "from": "guard",
                "to": "gates",
                "transform": "wrap_array"
            },
            {
                "type": ChangeType.ADD_FIELD,
                "path": "",
                "field": "display",
                "default": {"rules": []},
                "condition": "missing"
            },
            {
                "type": ChangeType.CONVERT_TYPE,
                "path": "terminal_states",
                "from": "string",
                "to": "array",
                "transform": "string_to_array"
            },
            {
                "type": ChangeType.REMOVE_FIELD,
                "path": "",
                "field": "fork_join_patterns",
                "condition": "exists"
            }
        ]
    }
}


# =============================================================================
# Blueprint Loading and Version Detection
# =============================================================================

def load_blueprint(params: Dict[str, Any]) -> Dict[str, Any]:
    """Load an L++ blueprint from a JSON file for migration."""
    path = params.get("path")
    if not path:
        return {"blueprint": None, "path": None, "error": "No path provided"}

    try:
        filePath = Path(path)
        if not filePath.exists():
            return {"blueprint": None, "path": None,
                    "error": f"File not found: {path}"}

        with open(filePath) as f:
            blueprint = json.load(f)

        return {"blueprint": blueprint, "path": str(filePath), "error": None}
    except json.JSONDecodeError as e:
        return {"blueprint": None, "path": None,
                "error": f"Invalid JSON: {e}"}
    except Exception as e:
        return {"blueprint": None, "path": None, "error": str(e)}


def detect_version(params: Dict[str, Any]) -> Dict[str, Any]:
    """Detect the schema version of a blueprint."""
    blueprint = params.get("blueprint", {})

    if not blueprint:
        return {"source_version": None, "error": "No blueprint provided"}

    # Check explicit $schema field
    schema = blueprint.get("$schema")
    if schema:
        if schema in SCHEMA_VERSIONS:
            return {"source_version": schema, "error": None}
        # Try to normalize version
        if schema.startswith("lpp/v"):
            return {"source_version": schema, "error": None}

    # Heuristic detection based on structure
    detected = _detect_version_heuristic(blueprint)
    return {"source_version": detected, "error": None}


def _detect_version_heuristic(bp: Dict[str, Any]) -> str:
    """Detect version based on blueprint structure."""
    # Check for v0.1.2 features
    if "display" in bp:
        return "lpp/v0.1.2"

    # Check for v0.1.1 features (context_schema with properties)
    ctxSchema = bp.get("context_schema", {})
    if isinstance(ctxSchema, dict) and "properties" in ctxSchema:
        transitions = bp.get("transitions", [])
        # Check if using on_event vs event
        for t in transitions:
            if "on_event" in t:
                # Check for guard vs gates
                if any("guard" in t for t in transitions):
                    return "lpp/v0.1.1"
                if any("gates" in t for t in transitions):
                    return "lpp/v0.1.2"
        return "lpp/v0.1.1"

    # Check for v0.1.0 features (old event naming)
    transitions = bp.get("transitions", [])
    for t in transitions:
        if "event" in t and "on_event" not in t:
            return "lpp/v0.1.0"

    # Check for context vs context_schema
    if "context" in bp and "context_schema" not in bp:
        return "lpp/v0.1.0"

    # Default to v0.1.1 if uncertain
    return "lpp/v0.1.1"


def get_latest_version(params: Dict[str, Any]) -> Dict[str, Any]:
    """Get the latest schema version."""
    return {"version": LATEST_VERSION}


# =============================================================================
# Migration Listing and Planning
# =============================================================================

def list_migrations(params: Dict[str, Any]) -> Dict[str, Any]:
    """List all available migrations (built-in and custom)."""
    migrations = []

    # Add built-in migrations
    for key, mig in BUILTIN_MIGRATIONS.items():
        migrations.append({
            "key": key,
            "from": mig["from_version"],
            "to": mig["to_version"],
            "description": mig["description"],
            "source": "builtin",
            "change_count": len(mig["changes"])
        })

    # Load custom migrations from directory
    if MIGRATIONS_DIR.exists():
        for migFile in MIGRATIONS_DIR.glob("*.json"):
            try:
                with open(migFile) as f:
                    customMig = json.load(f)
                key = f"{customMig['from_version']}->{customMig['to_version']}"
                migrations.append({
                    "key": key,
                    "from": customMig["from_version"],
                    "to": customMig["to_version"],
                    "description": customMig.get("description", "Custom migration"),
                    "source": str(migFile),
                    "change_count": len(customMig.get("changes", []))
                })
            except (json.JSONDecodeError, KeyError):
                continue

    return {"migrations": migrations}


def plan_migration(params: Dict[str, Any]) -> Dict[str, Any]:
    """Plan the migration path from source to target version."""
    sourceVer = params.get("source_version")
    targetVer = params.get("target_version")
    availMigs = params.get("available_migrations", [])

    if not sourceVer:
        return {"plan": [], "error": "Source version not detected"}
    if not targetVer:
        return {"plan": [], "error": "Target version not specified"}
    if sourceVer == targetVer:
        return {"plan": [], "error": None}

    # Build migration graph
    migGraph = {}
    for mig in availMigs:
        migGraph[mig["from"]] = migGraph.get(mig["from"], [])
        migGraph[mig["from"]].append(mig)

    # Find path using BFS
    queue = [(sourceVer, [])]
    visited = {sourceVer}

    while queue:
        current, path = queue.pop(0)
        if current == targetVer:
            return {"plan": path, "error": None}

        for mig in migGraph.get(current, []):
            nextVer = mig["to"]
            if nextVer not in visited:
                visited.add(nextVer)
                queue.append((nextVer, path + [mig]))

    return {"plan": [], "error": f"No migration path from {sourceVer} to {targetVer}"}


def analyze_changes(params: Dict[str, Any]) -> Dict[str, Any]:
    """Analyze what changes will be made during migration."""
    blueprint = params.get("blueprint", {})
    plan = params.get("migration_plan", [])

    if not plan:
        return {"changes": []}

    allChanges = []
    tempBp = copy.deepcopy(blueprint)

    for step in plan:
        migKey = f"{step['from']}->{step['to']}"
        migDef = _get_migration_definition(migKey, step.get("source"))

        if not migDef:
            continue

        for change in migDef.get("changes", []):
            analyzed = _analyze_single_change(tempBp, change)
            if analyzed:
                analyzed["migration"] = migKey
                allChanges.append(analyzed)

        # Apply to temp for next step analysis
        tempBp = _apply_changes(tempBp, migDef.get("changes", []))

    return {"changes": allChanges}


def _get_migration_definition(key: str, source: Optional[str] = None
                              ) -> Optional[Dict[str, Any]]:
    """Get migration definition by key."""
    # Check built-in first
    if key in BUILTIN_MIGRATIONS:
        return BUILTIN_MIGRATIONS[key]

    # Check custom file
    if source and source != "builtin":
        try:
            with open(source) as f:
                return json.load(f)
        except (FileNotFoundError, json.JSONDecodeError):
            pass

    return None


def _analyze_single_change(bp: Dict[str, Any], change: Dict[str, Any]
                           ) -> Optional[Dict[str, Any]]:
    """Analyze a single change against the blueprint."""
    changeType = change.get("type")
    path = change.get("path", "")

    if changeType == ChangeType.RENAME_FIELD:
        oldField = change.get("from")
        newField = change.get("to")

        if path.endswith("[*]"):
            # Array path (e.g., transitions[*])
            basePath = path[:-3]
            arr = _get_nested(bp, basePath)
            if arr:
                matches = sum(1 for item in arr if oldField in item)
                if matches > 0:
                    return {
                        "type": changeType,
                        "description": f"Rename '{oldField}' to '{newField}' "
                        f"in {matches} items at {basePath}",
                        "affected_count": matches
                    }
        else:
            # Direct path
            target = _get_nested(bp, path) if path else bp
            if target and oldField in target:
                return {
                    "type": changeType,
                    "description": f"Rename '{oldField}' to '{newField}' "
                    f"at {path or 'root'}",
                    "affected_count": 1
                }

    elif changeType == ChangeType.ADD_FIELD:
        field = change.get("field")
        target = _get_nested(bp, path) if path else bp
        condition = change.get("condition", "missing")

        if condition == "missing" and target and field not in target:
            return {
                "type": changeType,
                "description": f"Add field '{field}' at {path or 'root'}",
                "affected_count": 1
            }

    elif changeType == ChangeType.REMOVE_FIELD:
        field = change.get("field")
        target = _get_nested(bp, path) if path else bp
        condition = change.get("condition", "exists")

        if condition == "exists" and target and field in target:
            return {
                "type": changeType,
                "description": f"Remove field '{field}' from {path or 'root'}",
                "affected_count": 1
            }

    elif changeType == ChangeType.CONVERT_TYPE:
        target = _get_nested(bp, path) if path else bp
        fromType = change.get("from")
        toType = change.get("to")

        if target is not None:
            actualType = type(target).__name__
            if _type_matches(actualType, fromType):
                return {
                    "type": changeType,
                    "description": f"Convert '{path}' from {fromType} to {toType}",
                    "affected_count": 1
                }

    return None


def _type_matches(actualType: str, expectedType: str) -> bool:
    """Check if actual type matches expected type name."""
    typeMap = {
        "str": "string",
        "int": "number",
        "float": "number",
        "list": "array",
        "dict": "object",
        "bool": "boolean",
        "NoneType": "null"
    }
    return typeMap.get(actualType, actualType) == expectedType


def _get_nested(obj: Dict[str, Any], path: str) -> Any:
    """Get nested value by dot-separated path."""
    if not path:
        return obj

    parts = path.split(".")
    current = obj

    for part in parts:
        if not isinstance(current, dict):
            return None
        current = current.get(part)
        if current is None:
            return None

    return current


def _set_nested(obj: Dict[str, Any], path: str, value: Any) -> None:
    """Set nested value by dot-separated path."""
    if not path:
        return

    parts = path.split(".")
    current = obj

    for part in parts[:-1]:
        if part not in current:
            current[part] = {}
        current = current[part]

    current[parts[-1]] = value


# =============================================================================
# Migration Application
# =============================================================================

def apply_migration(params: Dict[str, Any]) -> Dict[str, Any]:
    """Apply the full migration plan to the blueprint."""
    blueprint = params.get("blueprint", {})
    plan = params.get("migration_plan", [])

    if not blueprint:
        return {"blueprint": None, "error": "No blueprint provided"}

    if not plan:
        return {"blueprint": blueprint, "error": None}

    migrated = copy.deepcopy(blueprint)

    for step in plan:
        migKey = f"{step['from']}->{step['to']}"
        migDef = _get_migration_definition(migKey, step.get("source"))

        if not migDef:
            return {"blueprint": None,
                    "error": f"Migration definition not found: {migKey}"}

        try:
            migrated = _apply_changes(migrated, migDef.get("changes", []))
            # Update schema version
            migrated["$schema"] = step["to"]
        except Exception as e:
            return {"blueprint": None,
                    "error": f"Migration failed at {migKey}: {str(e)}"}

    return {"blueprint": migrated, "error": None}


def _apply_changes(bp: Dict[str, Any], changes: List[Dict[str, Any]]
                   ) -> Dict[str, Any]:
    """Apply a list of changes to a blueprint."""
    result = copy.deepcopy(bp)

    for change in changes:
        changeType = change.get("type")
        path = change.get("path", "")

        if changeType == ChangeType.RENAME_FIELD:
            _apply_rename(result, path, change)
        elif changeType == ChangeType.ADD_FIELD:
            _apply_add_field(result, path, change)
        elif changeType == ChangeType.REMOVE_FIELD:
            _apply_remove_field(result, path, change)
        elif changeType == ChangeType.CONVERT_TYPE:
            _apply_convert_type(result, path, change)
        elif changeType == ChangeType.MOVE_FIELD:
            _apply_move_field(result, path, change)
        elif changeType == ChangeType.TRANSFORM_VALUE:
            _apply_transform(result, path, change)

    return result


def _apply_rename(bp: Dict[str, Any], path: str,
                  change: Dict[str, Any]) -> None:
    """Apply a field rename change."""
    oldField = change.get("from")
    newField = change.get("to")
    transform = change.get("transform")

    if path.endswith("[*]"):
        # Array iteration
        basePath = path[:-3]
        arr = _get_nested(bp, basePath) if basePath else bp.get(
            basePath.split(".")[-1] if basePath else None)
        if basePath:
            arr = _get_nested(bp, basePath)
        else:
            arr = None

        if arr and isinstance(arr, list):
            for item in arr:
                if isinstance(item, dict) and oldField in item:
                    val = item.pop(oldField)
                    if transform == "wrap_array" and not isinstance(val, list):
                        val = [val] if val else []
                    item[newField] = val
    else:
        target = _get_nested(bp, path) if path else bp
        if isinstance(target, dict) and oldField in target:
            val = target.pop(oldField)
            if transform == "wrap_array" and not isinstance(val, list):
                val = [val] if val else []
            target[newField] = val


def _apply_add_field(bp: Dict[str, Any], path: str,
                     change: Dict[str, Any]) -> None:
    """Apply an add field change."""
    field = change.get("field")
    default = change.get("default")
    condition = change.get("condition", "missing")

    target = _get_nested(bp, path) if path else bp
    if not isinstance(target, dict):
        return

    if condition == "missing" and field not in target:
        target[field] = copy.deepcopy(default)
    elif condition == "always":
        target[field] = copy.deepcopy(default)


def _apply_remove_field(bp: Dict[str, Any], path: str,
                        change: Dict[str, Any]) -> None:
    """Apply a remove field change."""
    field = change.get("field")
    condition = change.get("condition", "exists")

    target = _get_nested(bp, path) if path else bp
    if not isinstance(target, dict):
        return

    if condition == "exists" and field in target:
        del target[field]
    elif condition == "always" and field in target:
        del target[field]


def _apply_convert_type(bp: Dict[str, Any], path: str,
                        change: Dict[str, Any]) -> None:
    """Apply a type conversion change."""
    fromType = change.get("from")
    toType = change.get("to")
    transform = change.get("transform")

    # Handle root path
    if not path:
        return

    parts = path.split(".")
    parentPath = ".".join(parts[:-1])
    field = parts[-1]

    parent = _get_nested(bp, parentPath) if parentPath else bp
    if not isinstance(parent, dict) or field not in parent:
        return

    val = parent[field]

    if transform == "string_to_array":
        if isinstance(val, str):
            parent[field] = [val] if val else []
    elif transform == "array_to_string":
        if isinstance(val, list):
            parent[field] = val[0] if val else ""
    elif transform == "wrap_object":
        if not isinstance(val, dict):
            parent[field] = {"value": val}
    elif transform == "unwrap_object":
        if isinstance(val, dict) and "value" in val:
            parent[field] = val["value"]


def _apply_move_field(bp: Dict[str, Any], path: str,
                      change: Dict[str, Any]) -> None:
    """Apply a move field change."""
    fromPath = change.get("from_path")
    toPath = change.get("to_path")

    if not fromPath or not toPath:
        return

    val = _get_nested(bp, fromPath)
    if val is None:
        return

    # Remove from old location
    parts = fromPath.split(".")
    parentPath = ".".join(parts[:-1])
    field = parts[-1]
    parent = _get_nested(bp, parentPath) if parentPath else bp
    if isinstance(parent, dict) and field in parent:
        del parent[field]

    # Add to new location
    _set_nested(bp, toPath, val)


def _apply_transform(bp: Dict[str, Any], path: str,
                     change: Dict[str, Any]) -> None:
    """Apply a value transformation."""
    transformFn = change.get("function")

    if not path:
        return

    val = _get_nested(bp, path)
    if val is None:
        return

    # Built-in transforms
    if transformFn == "uppercase":
        if isinstance(val, str):
            _set_nested(bp, path, val.upper())
    elif transformFn == "lowercase":
        if isinstance(val, str):
            _set_nested(bp, path, val.lower())
    elif transformFn == "snake_case":
        if isinstance(val, str):
            result = re.sub(r'([A-Z])', r'_\1', val).lower().lstrip('_')
            _set_nested(bp, path, result)


# =============================================================================
# Dry Run and Preview
# =============================================================================

def dry_run(params: Dict[str, Any]) -> Dict[str, Any]:
    """Preview migration without applying changes permanently."""
    blueprint = params.get("blueprint", {})
    plan = params.get("migration_plan", [])

    # Analyze changes
    analysis = analyze_changes(
        {"blueprint": blueprint, "migration_plan": plan})
    changes = analysis.get("changes", [])

    # Apply to a copy for preview
    result = apply_migration({"blueprint": blueprint, "migration_plan": plan})
    previewBp = result.get("blueprint")

    return {
        "changes": changes,
        "preview_blueprint": previewBp
    }


# =============================================================================
# Validation
# =============================================================================

def validate_blueprint(params: Dict[str, Any]) -> Dict[str, Any]:
    """Validate a blueprint against target schema version."""
    blueprint = params.get("blueprint", {})
    targetVer = params.get("target_version", LATEST_VERSION)

    if not blueprint:
        return {"result": {"valid": False, "errors": ["No blueprint"]}}

    errors = []
    warnings = []

    # Required fields check
    required = ["$schema", "id", "name", "version", "states", "transitions",
                "entry_state", "terminal_states"]

    for field in required:
        if field not in blueprint:
            errors.append(f"Missing required field: {field}")

    # Schema version check
    schema = blueprint.get("$schema")
    if schema != targetVer:
        warnings.append(f"Schema version mismatch: {schema} vs {targetVer}")

    # States validation
    states = blueprint.get("states", {})
    entryState = blueprint.get("entry_state")
    terminalStates = blueprint.get("terminal_states", [])

    if entryState and entryState not in states:
        errors.append(f"Entry state '{entryState}' not in states")

    if isinstance(terminalStates, list):
        for ts in terminalStates:
            if ts not in states:
                errors.append(f"Terminal state '{ts}' not in states")
    elif isinstance(terminalStates, str):
        errors.append("terminal_states should be array, not string")

    # Transitions validation
    transitions = blueprint.get("transitions", [])
    if not isinstance(transitions, list):
        errors.append("transitions should be an array")
    else:
        for i, t in enumerate(transitions):
            # Check required transition fields
            if "id" not in t:
                errors.append(f"Transition {i} missing 'id'")
            if "from" not in t:
                errors.append(f"Transition {i} missing 'from'")
            if "to" not in t:
                errors.append(f"Transition {i} missing 'to'")
            if "on_event" not in t:
                errors.append(f"Transition {i} missing 'on_event'")

            # Check state references
            fromState = t.get("from")
            toState = t.get("to")
            if fromState != "*" and fromState not in states:
                errors.append(f"Transition {t.get('id', i)}: "
                              f"unknown from state '{fromState}'")
            if toState != "*" and toState not in states:
                errors.append(f"Transition {t.get('id', i)}: "
                              f"unknown to state '{toState}'")

            # v0.1.2 check: gates should be array
            if targetVer == "lpp/v0.1.2":
                gates = t.get("gates")
                if gates is not None and not isinstance(gates, list):
                    errors.append(f"Transition {t.get('id', i)}: "
                                  "gates should be array")

    # Gates validation
    gates = blueprint.get("gates", {})
    if not isinstance(gates, dict):
        errors.append("gates should be an object")

    # Actions validation
    actions = blueprint.get("actions", {})
    if not isinstance(actions, dict):
        errors.append("actions should be an object")

    # v0.1.2 specific: display field
    if targetVer == "lpp/v0.1.2":
        if "display" not in blueprint:
            warnings.append("Missing optional 'display' field for v0.1.2")

    result = {
        "valid": len(errors) == 0,
        "errors": errors,
        "warnings": warnings
    }

    return {"result": result}


# =============================================================================
# Report Generation
# =============================================================================

def generate_report(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate a migration report."""
    bpPath = params.get("blueprint_path", "unknown")
    sourceVer = params.get("source_version", "unknown")
    targetVer = params.get("target_version", "unknown")
    plan = params.get("migration_plan", [])
    changes = params.get("migration_changes", [])
    validation = params.get("validation_result", {})
    dryRun = params.get("dry_run_mode", False)

    lines = []
    lines.append("=" * 70)
    lines.append("  L++ Schema Migration Report")
    lines.append("=" * 70)
    lines.append("")
    lines.append(f"  Blueprint: {bpPath}")
    lines.append(f"  Mode: {'DRY RUN (preview only)' if dryRun else 'LIVE'}")
    lines.append("")
    lines.append(f"  Source Version: {sourceVer}")
    lines.append(f"  Target Version: {targetVer}")
    lines.append("")

    # Migration Plan
    lines.append("-" * 70)
    lines.append("  MIGRATION PLAN")
    lines.append("-" * 70)

    if not plan:
        if sourceVer == targetVer:
            lines.append("  No migration needed - already at target version")
        else:
            lines.append("  No migration path found")
    else:
        for i, step in enumerate(plan, 1):
            lines.append(f"  Step {i}: {step['from']} -> {step['to']}")
            lines.append(
                f"          {step.get('description', 'No description')}")
    lines.append("")

    # Changes
    if changes:
        lines.append("-" * 70)
        lines.append("  CHANGES")
        lines.append("-" * 70)

        for change in changes:
            chType = change.get("type", "unknown")
            desc = change.get("description", "")
            count = change.get("affected_count", 0)
            mig = change.get("migration", "")
            lines.append(f"  [{chType.upper()}] {desc}")
            if mig:
                lines.append(f"          (migration: {mig})")
        lines.append("")

    # Validation Results
    if validation:
        lines.append("-" * 70)
        lines.append("  VALIDATION")
        lines.append("-" * 70)

        if validation.get("valid"):
            lines.append("  Status: PASSED")
        else:
            lines.append("  Status: FAILED")

        errors = validation.get("errors", [])
        if errors:
            lines.append("  Errors:")
            for err in errors:
                lines.append(f"    - {err}")

        warnings = validation.get("warnings", [])
        if warnings:
            lines.append("  Warnings:")
            for warn in warnings:
                lines.append(f"    - {warn}")
    lines.append("")

    # Summary
    lines.append("-" * 70)
    lines.append("  SUMMARY")
    lines.append("-" * 70)
    lines.append(f"  Migration Steps: {len(plan)}")
    lines.append(f"  Total Changes: {len(changes)}")
    if validation:
        lines.append(
            f"  Validation: {'PASSED' if validation.get('valid') else 'FAILED'}")
    if dryRun:
        lines.append("  Note: This was a dry run. No changes were written.")
    lines.append("")
    lines.append("=" * 70)

    return {"report": "\n".join(lines)}


# =============================================================================
# Export
# =============================================================================

def export_migrated(params: Dict[str, Any]) -> Dict[str, Any]:
    """Export the migrated blueprint to a file."""
    blueprint = params.get("blueprint")
    path = params.get("path")

    if not blueprint:
        return {"error": "No migrated blueprint to export"}
    if not path:
        return {"error": "No export path specified"}

    try:
        outPath = Path(path)
        outPath.parent.mkdir(parents=True, exist_ok=True)

        with open(outPath, "w") as f:
            json.dump(blueprint, f, indent=2)

        return {"error": None}
    except Exception as e:
        return {"error": f"Export failed: {str(e)}"}


# =============================================================================
# Batch Migration
# =============================================================================

def batch_migrate(params: Dict[str, Any]) -> Dict[str, Any]:
    """Migrate multiple blueprints."""
    paths = params.get("paths", [])
    targetVer = params.get("target_version", LATEST_VERSION)

    results = []

    for path in paths:
        result = {"path": path}

        # Load
        loadRes = load_blueprint({"path": path})
        if loadRes.get("error"):
            result["status"] = "error"
            result["message"] = loadRes["error"]
            results.append(result)
            continue

        blueprint = loadRes["blueprint"]

        # Detect version
        verRes = detect_version({"blueprint": blueprint})
        sourceVer = verRes.get("source_version")

        if sourceVer == targetVer:
            result["status"] = "skipped"
            result["message"] = "Already at target version"
            results.append(result)
            continue

        # List and plan
        migsRes = list_migrations({})
        planRes = plan_migration({
            "source_version": sourceVer,
            "target_version": targetVer,
            "available_migrations": migsRes.get("migrations", [])
        })

        if planRes.get("error"):
            result["status"] = "error"
            result["message"] = planRes["error"]
            results.append(result)
            continue

        # Apply
        migRes = apply_migration({
            "blueprint": blueprint,
            "migration_plan": planRes.get("plan", [])
        })

        if migRes.get("error"):
            result["status"] = "error"
            result["message"] = migRes["error"]
            results.append(result)
            continue

        # Validate
        valRes = validate_blueprint({
            "blueprint": migRes["blueprint"],
            "target_version": targetVer
        })

        if not valRes.get("result", {}).get("valid"):
            result["status"] = "warning"
            result["message"] = "Migration complete with validation warnings"
            result["validation"] = valRes["result"]
        else:
            result["status"] = "success"
            result["message"] = f"Migrated from {sourceVer} to {targetVer}"

        # Export (same path, backup original)
        backupPath = path + ".bak"
        try:
            import shutil
            shutil.copy(path, backupPath)
        except Exception:
            pass

        exportRes = export_migrated({
            "blueprint": migRes["blueprint"],
            "path": path
        })

        if exportRes.get("error"):
            result["status"] = "error"
            result["message"] = exportRes["error"]

        results.append(result)

    return {"results": results}


# =============================================================================
# Utility Functions
# =============================================================================

def clear_migration(params: Dict[str, Any]) -> Dict[str, Any]:
    """Clear migration state."""
    return {
        "plan": None,
        "changes": None,
        "blueprint": None,
        "validation": None,
        "report": None
    }


def unload_blueprint(params: Dict[str, Any]) -> Dict[str, Any]:
    """Unload all blueprint state."""
    return {
        "blueprint": None,
        "path": None,
        "version": None,
        "target": None,
        "plan": None,
        "changes": None,
        "migrated": None,
        "validation": None,
        "report": None
    }


# =============================================================================
# COMPUTE REGISTRY - Maps compute_unit names to functions
# =============================================================================

COMPUTE_REGISTRY = {
    "migrate:load_blueprint": load_blueprint,
    "migrate:detect_version": detect_version,
    "migrate:get_latest_version": get_latest_version,
    "migrate:list_migrations": list_migrations,
    "migrate:plan_migration": plan_migration,
    "migrate:analyze_changes": analyze_changes,
    "migrate:apply_migration": apply_migration,
    "migrate:validate_blueprint": validate_blueprint,
    "migrate:generate_report": generate_report,
    "migrate:export_migrated": export_migrated,
    "migrate:dry_run": dry_run,
    "migrate:batch_migrate": batch_migrate,
    "migrate:clear_migration": clear_migration,
    "migrate:unload_blueprint": unload_blueprint,
}
