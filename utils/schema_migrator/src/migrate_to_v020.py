#!/usr/bin/env python3
"""
Schema Migration Script: v0.1.x -> v0.2.0

Batch migrates all L++ blueprints to v0.2.0 schema.
Key change: terminal_states from array to object with contracts.
"""

import json
import os
import sys
from pathlib import Path
from typing import Any, Dict, List, Tuple


def detect_schema_version(blueprint: Dict[str, Any]) -> str:
    """Detect the schema version of a blueprint."""
    schema = blueprint.get("$schema", "")
    if schema:
        return schema.replace("lpp/", "")
    # Infer from structure
    terminal = blueprint.get("terminal_states")
    if terminal is None:
        return "v0.1.0"
    if isinstance(terminal, list):
        return "v0.1.1"
    if isinstance(terminal, dict):
        # Check if it has contracts
        for state_id, contract in terminal.items():
            if contract.get("output_schema") or contract.get("invariants_guaranteed"):
                return "v0.2.0"
        return "v0.2.0"  # Empty dict is still v0.2.0
    return "unknown"


def migrate_terminal_states(
    blueprint: Dict[str, Any]
) -> Tuple[Dict[str, Any], List[str]]:
    """
    Migrate terminal_states from array to object.

    v0.1.x: ["complete", "error"] or {}
    v0.2.0: {"complete": {...}, "error": {...}}
    """
    changes = []
    terminal = blueprint.get("terminal_states")
    context_props = blueprint.get("context_schema", {}).get("properties", {})

    if terminal is None:
        # No terminal states defined - create defaults
        terminal = {}
        changes.append("Added default terminal_states")

    if isinstance(terminal, list):
        # Convert array to object
        new_terminal = {}
        for state_id in terminal:
            contract = _infer_contract(state_id, context_props)
            new_terminal[state_id] = contract
            changes.append(f"Converted terminal '{state_id}' to object with contract")
        blueprint["terminal_states"] = new_terminal
    elif isinstance(terminal, dict):
        # Already object - check if contracts need enrichment
        for state_id, contract in terminal.items():
            if not contract:
                # Empty contract - add inferred contract
                terminal[state_id] = _infer_contract(state_id, context_props)
                changes.append(f"Added inferred contract to terminal '{state_id}'")
        blueprint["terminal_states"] = terminal

    # Ensure common terminal states exist
    states = blueprint.get("states", {})
    term_states = blueprint.get("terminal_states", {})

    # Check for error state that should be terminal
    if "error" in states and "error" not in term_states:
        term_states["error"] = _infer_contract("error", context_props)
        changes.append("Added 'error' to terminal_states")
        # Remove from states
        del states["error"]
        changes.append("Moved 'error' from states to terminal_states")

    # Check for complete/done states
    for complete_name in ["complete", "done", "success", "finished"]:
        if complete_name in states and complete_name not in term_states:
            term_states[complete_name] = _infer_contract(complete_name, context_props)
            changes.append(f"Added '{complete_name}' to terminal_states")
            del states[complete_name]
            changes.append(f"Moved '{complete_name}' from states to terminal_states")

    blueprint["terminal_states"] = term_states
    blueprint["states"] = states

    return blueprint, changes


def _infer_contract(state_id: str, context_props: Dict[str, Any]) -> Dict[str, Any]:
    """Infer contract for a terminal state based on its name."""
    contract: Dict[str, Any] = {}

    if state_id == "error":
        contract["output_schema"] = {
            "error": {"type": "string", "non_null": True}
        }
        return contract

    if state_id in ("complete", "done", "success", "finished"):
        # Look for result/output fields in context
        output_schema = {}
        for prop_name, prop_def in context_props.items():
            if prop_name in ("result", "output", "data", "response"):
                output_schema[prop_name] = {
                    "type": prop_def.get("type", "object"),
                    "non_null": True
                }
        if output_schema:
            contract["output_schema"] = output_schema
            contract["invariants_guaranteed"] = ["result_produced"]
        return contract

    # For custom terminal states, return empty contract
    return {}


def migrate_blueprint(blueprint: Dict[str, Any]) -> Tuple[Dict[str, Any], List[str]]:
    """Migrate a blueprint to v0.2.0 schema."""
    changes = []

    # Update schema version
    old_schema = blueprint.get("$schema", "")
    if old_schema != "lpp/v0.2.0":
        blueprint["$schema"] = "lpp/v0.2.0"
        changes.append(f"Updated $schema from '{old_schema}' to 'lpp/v0.2.0'")

    # Migrate terminal_states
    blueprint, term_changes = migrate_terminal_states(blueprint)
    changes.extend(term_changes)

    # Ensure actions have proper structure
    actions = blueprint.get("actions", {})
    for action_id, action in actions.items():
        if action.get("type") == "compute":
            # Ensure input_map exists
            if "input_map" not in action:
                action["input_map"] = {}
                changes.append(f"Added empty input_map to action '{action_id}'")
            # Ensure output_map exists
            if "output_map" not in action:
                action["output_map"] = {}
                changes.append(f"Added empty output_map to action '{action_id}'")

    return blueprint, changes


def migrate_file(
    file_path: Path,
    dry_run: bool = False
) -> Dict[str, Any]:
    """Migrate a single blueprint file."""
    result = {
        "path": str(file_path),
        "success": False,
        "changes": [],
        "error": None
    }

    try:
        with open(file_path, "r") as f:
            blueprint = json.load(f)

        # Check if it's a blueprint
        if "states" not in blueprint and "transitions" not in blueprint:
            result["error"] = "Not a blueprint file (no states/transitions)"
            return result

        # Check current version
        current_version = detect_schema_version(blueprint)
        result["from_version"] = current_version

        if current_version == "v0.2.0":
            # Check if contracts are populated
            terminal = blueprint.get("terminal_states", {})
            has_contracts = any(
                t.get("output_schema") or t.get("invariants_guaranteed")
                for t in terminal.values()
            ) if terminal else False

            if has_contracts:
                result["success"] = True
                result["changes"].append("Already at v0.2.0 with contracts")
                return result
            else:
                # Update contracts even if version is 0.2.0
                pass

        # Migrate
        migrated, changes = migrate_blueprint(blueprint)
        result["changes"] = changes
        result["to_version"] = "v0.2.0"

        if not dry_run and changes:
            with open(file_path, "w") as f:
                json.dump(migrated, f, indent=2)
                f.write("\n")

        result["success"] = True

    except json.JSONDecodeError as e:
        result["error"] = f"JSON parse error: {e}"
    except Exception as e:
        result["error"] = str(e)

    return result


def find_blueprints(root_dir: Path) -> List[Path]:
    """Find all blueprint JSON files."""
    blueprints = []

    for json_file in root_dir.rglob("*.json"):
        # Skip certain directories
        skip_dirs = ["node_modules", ".git", "__pycache__", "results"]
        if any(skip in json_file.parts for skip in skip_dirs):
            continue

        # Quick check if it might be a blueprint
        try:
            with open(json_file, "r") as f:
                content = f.read(1000)  # Read first 1000 chars
                if '"states"' in content or '"transitions"' in content:
                    blueprints.append(json_file)
        except:
            continue

    return blueprints


def main():
    import argparse

    parser = argparse.ArgumentParser(
        description="Migrate L++ blueprints to v0.2.0 schema"
    )
    parser.add_argument(
        "path",
        nargs="?",
        default=".",
        help="Path to blueprint file or directory"
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Preview changes without modifying files"
    )
    parser.add_argument(
        "--verbose",
        "-v",
        action="store_true",
        help="Show detailed output"
    )

    args = parser.parse_args()
    path = Path(args.path)

    if path.is_file():
        files = [path]
    else:
        files = find_blueprints(path)

    print(f"{'[DRY RUN] ' if args.dry_run else ''}Migrating {len(files)} blueprint(s) to v0.2.0\n")

    migrated = 0
    skipped = 0
    errors = 0

    for file_path in files:
        result = migrate_file(file_path, dry_run=args.dry_run)

        if result["error"]:
            if args.verbose or "Not a blueprint" not in result["error"]:
                print(f"ERROR: {file_path}")
                print(f"  {result['error']}")
            errors += 1
        elif result["changes"]:
            if "Already at v0.2.0" in str(result["changes"]):
                skipped += 1
                if args.verbose:
                    print(f"SKIP: {file_path} (already v0.2.0)")
            else:
                migrated += 1
                print(f"{'WOULD MIGRATE' if args.dry_run else 'MIGRATED'}: {file_path}")
                if args.verbose:
                    for change in result["changes"]:
                        print(f"  - {change}")
        else:
            skipped += 1

    print(f"\nSummary:")
    print(f"  Migrated: {migrated}")
    print(f"  Skipped:  {skipped}")
    print(f"  Errors:   {errors}")

    if args.dry_run and migrated > 0:
        print(f"\nRun without --dry-run to apply changes")

    return 0 if errors == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
