#!/usr/bin/env python3
"""
Unit tests for L++ Schema Migrator.

Tests migration detection, planning, and application.
"""

from src.migrator_compute import (
    load_blueprint,
    detect_version,
    get_latest_version,
    list_migrations,
    plan_migration,
    analyze_changes,
    apply_migration,
    validate_blueprint,
    dry_run,
    SCHEMA_VERSIONS,
    LATEST_VERSION,
)
import json
import sys
import tempfile
from pathlib import Path

# Add parent paths for imports
HERE = Path(__file__).parent.parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent.parent / "src"))


# =============================================================================
# Test Fixtures - Sample Blueprints
# =============================================================================

BLUEPRINT_V010 = {
    "$schema": "lpp/v0.1.0",
    "id": "test_old_blueprint",
    "name": "Test Old Blueprint",
    "version": "1.0.0",
    "description": "A blueprint using v0.1.0 schema",
    "context": {
        "status": {"type": "string"},
        "count": {"type": "number"}
    },
    "states": {
        "idle": {"description": "Waiting"},
        "active": {"description": "Working"},
        "done": {"description": "Finished"}
    },
    "transitions": [
        {
            "id": "t_start",
            "from": "idle",
            "to": "active",
            "event": "START",
            "guard": "is_ready"
        },
        {
            "id": "t_finish",
            "from": "active",
            "to": "done",
            "event": "COMPLETE"
        }
    ],
    "gates": {
        "is_ready": {
            "type": "expression",
            "expression": "status == 'ready'"
        }
    },
    "actions": {
        "set_active": {
            "type": "set",
            "target": "status",
            "value": "active"
        }
    },
    "entry_state": "idle",
    "terminal_states": "done"
}

BLUEPRINT_V011 = {
    "$schema": "lpp/v0.1.1",
    "id": "test_v011_blueprint",
    "name": "Test v0.1.1 Blueprint",
    "version": "1.0.0",
    "description": "A blueprint using v0.1.1 schema",
    "context_schema": {
        "properties": {
            "status": {"type": "string"},
            "count": {"type": "number"}
        }
    },
    "states": {
        "idle": {"description": "Waiting"},
        "active": {"description": "Working"},
        "done": {"description": "Finished"}
    },
    "transitions": [
        {
            "id": "t_start",
            "from": "idle",
            "to": "active",
            "on_event": "START",
            "guard": "is_ready"
        },
        {
            "id": "t_finish",
            "from": "active",
            "to": "done",
            "on_event": "COMPLETE"
        }
    ],
    "gates": {
        "is_ready": {
            "type": "expression",
            "expression": "status == 'ready'"
        }
    },
    "actions": {
        "set_active": {
            "type": "set",
            "target": "status",
            "value": "active"
        }
    },
    "entry_state": "idle",
    "terminal_states": ["done"]
}

BLUEPRINT_V012 = {
    "$schema": "lpp/v0.1.2",
    "id": "test_v012_blueprint",
    "name": "Test v0.1.2 Blueprint",
    "version": "1.0.0",
    "description": "A blueprint using v0.1.2 schema",
    "context_schema": {
        "properties": {
            "status": {"type": "string"},
            "count": {"type": "number"}
        }
    },
    "states": {
        "idle": {"description": "Waiting"},
        "active": {"description": "Working"},
        "done": {"description": "Finished"}
    },
    "transitions": [
        {
            "id": "t_start",
            "from": "idle",
            "to": "active",
            "on_event": "START",
            "gates": ["is_ready"]
        },
        {
            "id": "t_finish",
            "from": "active",
            "to": "done",
            "on_event": "COMPLETE"
        }
    ],
    "gates": {
        "is_ready": {
            "type": "expression",
            "expression": "status == 'ready'"
        }
    },
    "actions": {
        "set_active": {
            "type": "set",
            "target": "status",
            "value": "active"
        }
    },
    "display": {
        "rules": []
    },
    "entry_state": "idle",
    "terminal_states": ["done"]
}


# =============================================================================
# Test: Version Detection
# =============================================================================

def test_detect_version_explicit():
    """Test detection with explicit $schema field."""
    result = detect_version({"blueprint": BLUEPRINT_V010})
    assert result["source_version"] == "lpp/v0.1.0"

    result = detect_version({"blueprint": BLUEPRINT_V011})
    assert result["source_version"] == "lpp/v0.1.1"

    result = detect_version({"blueprint": BLUEPRINT_V012})
    assert result["source_version"] == "lpp/v0.1.2"


def test_detect_version_heuristic():
    """Test heuristic detection when $schema is missing."""
    # v0.1.0 heuristic: has 'event' not 'on_event'
    bp = {
        "states": {"idle": {}, "active": {}},
        "transitions": [{"id": "t1", "from": "idle", "to": "active", "event": "GO"}],
        "context": {"props": {}}
    }
    result = detect_version({"blueprint": bp})
    assert result["source_version"] == "lpp/v0.1.0"

    # v0.1.1 heuristic: has 'on_event' and 'guard'
    bp = {
        "states": {"idle": {}, "active": {}},
        "transitions": [
            {"id": "t1", "from": "idle", "to": "active",
                "on_event": "GO", "guard": "g1"}
        ],
        "context_schema": {"properties": {}}
    }
    result = detect_version({"blueprint": bp})
    assert result["source_version"] == "lpp/v0.1.1"

    # v0.1.2 heuristic: has 'display' and 'gates'
    bp = {
        "states": {"idle": {}, "active": {}},
        "transitions": [
            {"id": "t1", "from": "idle", "to": "active",
                "on_event": "GO", "gates": ["g1"]}
        ],
        "context_schema": {"properties": {}},
        "display": {"rules": []}
    }
    result = detect_version({"blueprint": bp})
    assert result["source_version"] == "lpp/v0.1.2"


def test_get_latest_version():
    """Test getting the latest schema version."""
    result = get_latest_version({})
    assert result["version"] == LATEST_VERSION


# =============================================================================
# Test: Migration Listing and Planning
# =============================================================================

def test_list_migrations():
    """Test listing available migrations."""
    result = list_migrations({})
    migrations = result["migrations"]

    assert len(migrations) >= 2  # At least the built-in ones
    versions = {(m["from"], m["to"]) for m in migrations}
    assert ("lpp/v0.1.0", "lpp/v0.1.1") in versions
    assert ("lpp/v0.1.1", "lpp/v0.1.2") in versions


def test_plan_migration_single_step():
    """Test planning a single-step migration."""
    migs = list_migrations({})["migrations"]

    result = plan_migration({
        "source_version": "lpp/v0.1.1",
        "target_version": "lpp/v0.1.2",
        "available_migrations": migs
    })

    assert result["error"] is None
    plan = result["plan"]
    assert len(plan) == 1
    assert plan[0]["from"] == "lpp/v0.1.1"
    assert plan[0]["to"] == "lpp/v0.1.2"


def test_plan_migration_multi_step():
    """Test planning a multi-step migration."""
    migs = list_migrations({})["migrations"]

    result = plan_migration({
        "source_version": "lpp/v0.1.0",
        "target_version": "lpp/v0.1.2",
        "available_migrations": migs
    })

    assert result["error"] is None
    plan = result["plan"]
    assert len(plan) == 2
    assert plan[0]["from"] == "lpp/v0.1.0"
    assert plan[0]["to"] == "lpp/v0.1.1"
    assert plan[1]["from"] == "lpp/v0.1.1"
    assert plan[1]["to"] == "lpp/v0.1.2"


def test_plan_migration_same_version():
    """Test planning when already at target version."""
    result = plan_migration({
        "source_version": "lpp/v0.1.2",
        "target_version": "lpp/v0.1.2",
        "available_migrations": []
    })

    assert result["error"] is None
    assert len(result["plan"]) == 0


def test_plan_migration_no_path():
    """Test planning when no path exists."""
    result = plan_migration({
        "source_version": "lpp/v0.1.0",
        "target_version": "lpp/v999.0.0",
        "available_migrations": list_migrations({})["migrations"]
    })

    assert result["error"] is not None
    assert "No migration path" in result["error"]


# =============================================================================
# Test: Change Analysis
# =============================================================================

def test_analyze_changes():
    """Test analyzing changes for a migration."""
    migs = list_migrations({})["migrations"]
    plan = plan_migration({
        "source_version": "lpp/v0.1.1",
        "target_version": "lpp/v0.1.2",
        "available_migrations": migs
    })["plan"]

    result = analyze_changes({
        "blueprint": BLUEPRINT_V011,
        "migration_plan": plan
    })

    changes = result["changes"]
    assert len(changes) > 0

    # Should have rename guard->gates and add display
    changeTypes = [c["type"] for c in changes]
    assert "rename_field" in changeTypes or "add_field" in changeTypes


# =============================================================================
# Test: Migration Application
# =============================================================================

def test_apply_migration_v011_to_v012():
    """Test applying migration from v0.1.1 to v0.1.2."""
    migs = list_migrations({})["migrations"]
    plan = plan_migration({
        "source_version": "lpp/v0.1.1",
        "target_version": "lpp/v0.1.2",
        "available_migrations": migs
    })["plan"]

    result = apply_migration({
        "blueprint": BLUEPRINT_V011,
        "migration_plan": plan
    })

    assert result["error"] is None
    migrated = result["blueprint"]

    # Check schema updated
    assert migrated["$schema"] == "lpp/v0.1.2"

    # Check guard renamed to gates
    for t in migrated["transitions"]:
        assert "guard" not in t
        if "gates" in t:
            assert isinstance(t["gates"], list)

    # Check display added
    assert "display" in migrated

    # Check terminal_states is array
    assert isinstance(migrated["terminal_states"], list)


def test_apply_migration_v010_to_v012():
    """Test applying full migration from v0.1.0 to v0.1.2."""
    migs = list_migrations({})["migrations"]
    plan = plan_migration({
        "source_version": "lpp/v0.1.0",
        "target_version": "lpp/v0.1.2",
        "available_migrations": migs
    })["plan"]

    result = apply_migration({
        "blueprint": BLUEPRINT_V010,
        "migration_plan": plan
    })

    assert result["error"] is None
    migrated = result["blueprint"]

    # Check schema updated
    assert migrated["$schema"] == "lpp/v0.1.2"

    # Check event renamed to on_event
    for t in migrated["transitions"]:
        assert "event" not in t
        assert "on_event" in t

    # Check context renamed to context_schema
    assert "context" not in migrated
    assert "context_schema" in migrated

    # Check display added
    assert "display" in migrated


# =============================================================================
# Test: Validation
# =============================================================================

def test_validate_v012_valid():
    """Test validation of a valid v0.1.2 blueprint."""
    result = validate_blueprint({
        "blueprint": BLUEPRINT_V012,
        "target_version": "lpp/v0.1.2"
    })

    assert result["result"]["valid"] is True
    assert len(result["result"]["errors"]) == 0


def test_validate_missing_required():
    """Test validation catches missing required fields."""
    incomplete = {
        "$schema": "lpp/v0.1.2",
        "id": "test",
        "name": "Test"
        # Missing states, transitions, entry_state, terminal_states
    }

    result = validate_blueprint({
        "blueprint": incomplete,
        "target_version": "lpp/v0.1.2"
    })

    assert result["result"]["valid"] is False
    errors = result["result"]["errors"]
    assert any("states" in e for e in errors)
    assert any("transitions" in e for e in errors)


def test_validate_orphan_state_reference():
    """Test validation catches references to non-existent states."""
    bp = {
        "$schema": "lpp/v0.1.2",
        "id": "test",
        "name": "Test",
        "version": "1.0.0",
        "states": {"idle": {}},
        "transitions": [
            {"id": "t1", "from": "idle", "to": "nonexistent", "on_event": "GO"}
        ],
        "gates": {},
        "actions": {},
        "entry_state": "idle",
        "terminal_states": []
    }

    result = validate_blueprint({
        "blueprint": bp,
        "target_version": "lpp/v0.1.2"
    })

    assert result["result"]["valid"] is False
    errors = result["result"]["errors"]
    assert any("nonexistent" in e for e in errors)


# =============================================================================
# Test: Dry Run
# =============================================================================

def test_dry_run():
    """Test dry run mode."""
    migs = list_migrations({})["migrations"]
    plan = plan_migration({
        "source_version": "lpp/v0.1.1",
        "target_version": "lpp/v0.1.2",
        "available_migrations": migs
    })["plan"]

    result = dry_run({
        "blueprint": BLUEPRINT_V011,
        "migration_plan": plan
    })

    # Should have changes
    assert len(result["changes"]) > 0

    # Should have preview blueprint
    preview = result["preview_blueprint"]
    assert preview is not None
    assert preview["$schema"] == "lpp/v0.1.2"


# =============================================================================
# Test: Load Blueprint
# =============================================================================

def test_load_blueprint():
    """Test loading a blueprint from file."""
    with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
        json.dump(BLUEPRINT_V012, f)
        tmpPath = f.name

    try:
        result = load_blueprint({"path": tmpPath})
        assert result["error"] is None
        assert result["blueprint"]["id"] == "test_v012_blueprint"
        assert result["path"] == tmpPath
    finally:
        Path(tmpPath).unlink()


def test_load_blueprint_not_found():
    """Test loading a non-existent file."""
    result = load_blueprint({"path": "/nonexistent/path.json"})
    assert result["error"] is not None
    assert "not found" in result["error"].lower()


def test_load_blueprint_invalid_json():
    """Test loading an invalid JSON file."""
    with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
        f.write("{ invalid json }")
        tmpPath = f.name

    try:
        result = load_blueprint({"path": tmpPath})
        assert result["error"] is not None
        assert "json" in result["error"].lower()
    finally:
        Path(tmpPath).unlink()


# =============================================================================
# Test Runner
# =============================================================================

def run_tests():
    """Run all tests and report results."""
    import traceback

    tests = [
        test_detect_version_explicit,
        test_detect_version_heuristic,
        test_get_latest_version,
        test_list_migrations,
        test_plan_migration_single_step,
        test_plan_migration_multi_step,
        test_plan_migration_same_version,
        test_plan_migration_no_path,
        test_analyze_changes,
        test_apply_migration_v011_to_v012,
        test_apply_migration_v010_to_v012,
        test_validate_v012_valid,
        test_validate_missing_required,
        test_validate_orphan_state_reference,
        test_dry_run,
        test_load_blueprint,
        test_load_blueprint_not_found,
        test_load_blueprint_invalid_json,
    ]

    passed = 0
    failed = 0

    print("\n" + "=" * 60)
    print("  L++ Schema Migrator Tests")
    print("=" * 60 + "\n")

    for test in tests:
        name = test.__name__
        try:
            test()
            print(f"  [PASS] {name}")
            passed += 1
        except AssertionError as e:
            print(f"  [FAIL] {name}")
            print(f"         {e}")
            failed += 1
        except Exception as e:
            print(f"  [ERROR] {name}")
            print(f"          {e}")
            traceback.print_exc()
            failed += 1

    print("\n" + "-" * 60)
    print(f"  Results: {passed} passed, {failed} failed")
    print("=" * 60 + "\n")

    return failed == 0


if __name__ == "__main__":
    success = run_tests()
    sys.exit(0 if success else 1)
