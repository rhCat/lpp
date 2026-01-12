#!/usr/bin/env python3
"""
Migration script: v0.1.x -> v0.2.0

Converts terminal_states from array to object format.

Before: "terminal_states": ["done", "error"]
After:  "terminal_states": {"done": {}, "error": {}}

Also migrates terminal_contracts if present.
"""

import json
import os
import sys
from pathlib import Path


def migrateBlueprint(bp: dict) -> dict:
    """Migrate a single blueprint to v0.2.0 format."""
    # Check if already migrated (terminal_states is object)
    termStates = bp.get('terminal_states', [])

    if isinstance(termStates, dict):
        # Already in v0.2.0 format
        return bp

    if not isinstance(termStates, list):
        # Unknown format
        return bp

    # Get existing terminal_contracts if any
    contracts = bp.get('terminal_contracts', {})

    # Convert array to object
    newTermStates = {}
    for term in termStates:
        if term in contracts:
            newTermStates[term] = contracts[term]
        else:
            newTermStates[term] = {}

    # Update blueprint
    bp['terminal_states'] = newTermStates

    # Remove old terminal_contracts field
    if 'terminal_contracts' in bp:
        del bp['terminal_contracts']

    # Update schema version
    schema = bp.get('$schema', '')
    if schema.startswith('lpp/v0.1'):
        bp['$schema'] = 'lpp/v0.2.0'

    return bp


def migrateFile(filePath: str, dryRun: bool = False) -> bool:
    """Migrate a single JSON file."""
    try:
        with open(filePath, 'r') as f:
            data = json.load(f)
    except (json.JSONDecodeError, FileNotFoundError):
        return False

    # Check if it's a blueprint (has states and transitions)
    if 'states' not in data or 'transitions' not in data:
        return False

    # Check if it has terminal_states as array
    termStates = data.get('terminal_states', [])
    if not isinstance(termStates, list):
        return False  # Already migrated or not a blueprint

    if len(termStates) == 0:
        # Empty array - convert to empty object
        data['terminal_states'] = {}
        if not dryRun:
            with open(filePath, 'w') as f:
                json.dump(data, f, indent=2)
        return True

    # Migrate
    migrated = migrateBlueprint(data)

    if not dryRun:
        with open(filePath, 'w') as f:
            json.dump(migrated, f, indent=2)

    return True


def migrateDirectory(dirPath: str, dryRun: bool = False) -> dict:
    """Migrate all blueprints in a directory recursively."""
    results = {'migrated': [], 'skipped': [], 'errors': []}

    for root, dirs, files in os.walk(dirPath):
        # Skip hidden directories and results directories
        dirs[:] = [d for d in dirs if not d.startswith('.') and d != 'node_modules']

        for fname in files:
            if not fname.endswith('.json'):
                continue

            fpath = os.path.join(root, fname)
            relPath = os.path.relpath(fpath, dirPath)

            try:
                if migrateFile(fpath, dryRun):
                    results['migrated'].append(relPath)
                else:
                    results['skipped'].append(relPath)
            except Exception as e:
                results['errors'].append((relPath, str(e)))

    return results


def main():
    import argparse

    parser = argparse.ArgumentParser(
        description='Migrate L++ blueprints from v0.1.x to v0.2.0')
    parser.add_argument('path', help='File or directory to migrate')
    parser.add_argument('--dry-run', action='store_true',
                        help='Show what would be changed without modifying files')

    args = parser.parse_args()
    path = args.path

    if os.path.isfile(path):
        if migrateFile(path, args.dry_run):
            print(f"{'Would migrate' if args.dry_run else 'Migrated'}: {path}")
        else:
            print(f"Skipped (not a v0.1.x blueprint): {path}")
    elif os.path.isdir(path):
        print(f"{'Dry run - ' if args.dry_run else ''}Migrating blueprints in: {path}")
        print()

        results = migrateDirectory(path, args.dry_run)

        if results['migrated']:
            print(f"{'Would migrate' if args.dry_run else 'Migrated'} ({len(results['migrated'])}):")
            for f in results['migrated']:
                print(f"  + {f}")

        if results['errors']:
            print(f"\nErrors ({len(results['errors'])}):")
            for f, err in results['errors']:
                print(f"  ! {f}: {err}")

        print(f"\nSummary: {len(results['migrated'])} migrated, "
              f"{len(results['skipped'])} skipped, {len(results['errors'])} errors")
    else:
        print(f"Error: {path} not found")
        sys.exit(1)


if __name__ == '__main__':
    main()
