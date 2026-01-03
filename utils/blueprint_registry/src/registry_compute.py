"""
COMPUTE units for the L++ Blueprint Registry

These are pure computation functions for blueprint management,
version control, dependency tracking, and discovery operations.
"""

import json
import shutil
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Optional


# =============================================================================
# REGISTRY INITIALIZATION & PERSISTENCE
# =============================================================================

def init_registry(params: Dict[str, Any]) -> Dict[str, Any]:
    """Initialize a new empty registry at the specified path."""
    registry_path = params.get("registry_path")
    if not registry_path:
        return {"error": "No registry path provided"}

    try:
        path = Path(registry_path)
        path.mkdir(parents=True, exist_ok=True)

        index = {
            "version": "1.0.0",
            "created_at": datetime.utcnow().isoformat() + "Z",
            "updated_at": datetime.utcnow().isoformat() + "Z",
            "blueprints": {}
        }

        index_path = path / "index.json"
        with open(index_path, "w") as f:
            json.dump(index, f, indent=2)

        # Create versions directory
        (path / "versions").mkdir(exist_ok=True)

        return {
            "path": str(path),
            "index": index,
            "blueprints": {},
            "message": f"Registry initialized at {path}",
            "error": None
        }
    except Exception as e:
        return {"error": str(e)}


def load_registry(params: Dict[str, Any]) -> Dict[str, Any]:
    """Load an existing registry from disk."""
    registry_path = params.get("registry_path")
    if not registry_path:
        return {"error": "No registry path provided"}

    try:
        path = Path(registry_path)
        index_path = path / "index.json"

        if not index_path.exists():
            return {"error": f"Registry not found at {path}"}

        with open(index_path) as f:
            index = json.load(f)

        blueprints = index.get("blueprints", {})
        stats = _compute_stats(blueprints)

        return {
            "path": str(path),
            "index": index,
            "blueprints": blueprints,
            "stats": stats,
            "error": None
        }
    except Exception as e:
        return {"error": str(e)}


def save_registry(params: Dict[str, Any]) -> Dict[str, Any]:
    """Save registry index to disk."""
    registry_path = params.get("registry_path")
    index = params.get("index")

    if not registry_path or not index:
        return {"error": "Missing registry path or index"}

    try:
        path = Path(registry_path)
        index["updated_at"] = datetime.utcnow().isoformat() + "Z"

        index_path = path / "index.json"
        with open(index_path, "w") as f:
            json.dump(index, f, indent=2)

        return {"message": "Registry saved", "error": None}
    except Exception as e:
        return {"error": str(e)}


# =============================================================================
# BLUEPRINT REGISTRATION & UPDATES
# =============================================================================

def register_blueprint(params: Dict[str, Any]) -> Dict[str, Any]:
    """Register a new blueprint in the registry."""
    registry_path = params.get("registry_path")
    index = params.get("index")
    blueprint_path = params.get("blueprint_path")
    tags = params.get("tags", [])
    owner = params.get("owner", "unknown")

    if not blueprint_path:
        return {"error": "No blueprint path provided"}

    try:
        bp_path = Path(blueprint_path)
        if not bp_path.exists():
            return {"error": f"Blueprint not found: {blueprint_path}"}

        with open(bp_path) as f:
            blueprint = json.load(f)

        bp_id = blueprint.get("id")
        if not bp_id:
            return {"error": "Blueprint has no 'id' field"}

        blueprints = index.get("blueprints", {})
        if bp_id in blueprints:
            return {"error": f"Blueprint '{bp_id}' already registered. Use UPDATE."}

        version = blueprint.get("version", "1.0.0")
        now = datetime.utcnow().isoformat() + "Z"

        # Extract dependencies from actions
        deps = _extract_dependencies(blueprint)

        # Create metadata entry
        entry = {
            "current_version": version,
            "versions": [version],
            "description": blueprint.get("description", ""),
            "name": blueprint.get("name", bp_id),
            "tags": tags if isinstance(tags, list) else [tags] if tags else [],
            "dependencies": deps,
            "deprecated": False,
            "deprecated_reason": None,
            "created_at": now,
            "updated_at": now,
            "owner": owner,
            "source_path": str(bp_path.absolute())
        }

        blueprints[bp_id] = entry
        index["blueprints"] = blueprints

        # Copy blueprint to versions directory
        reg_path = Path(registry_path)
        version_dir = reg_path / "versions" / bp_id
        version_dir.mkdir(parents=True, exist_ok=True)
        shutil.copy(bp_path, version_dir / f"{version}.json")

        return {
            "index": index,
            "blueprints": blueprints,
            "message": f"Registered {bp_id} v{version}",
            "error": None
        }
    except Exception as e:
        return {"error": str(e)}


def update_blueprint(params: Dict[str, Any]) -> Dict[str, Any]:
    """Update an existing blueprint with version bump."""
    registry_path = params.get("registry_path")
    index = params.get("index")
    blueprint_id = params.get("blueprint_id")
    blueprint_path = params.get("blueprint_path")
    bump = params.get("bump", "patch")  # major, minor, patch

    blueprints = index.get("blueprints", {})

    if blueprint_id and blueprint_id not in blueprints:
        return {"error": f"Blueprint '{blueprint_id}' not found in registry"}

    try:
        bp_path = Path(blueprint_path)
        if not bp_path.exists():
            return {"error": f"Blueprint file not found: {blueprint_path}"}

        with open(bp_path) as f:
            blueprint = json.load(f)

        bp_id = blueprint_id or blueprint.get("id")
        if not bp_id:
            return {"error": "No blueprint ID provided or found in file"}

        if bp_id not in blueprints:
            return {"error": f"Blueprint '{bp_id}' not registered. Use REGISTER."}

        entry = blueprints[bp_id]
        old_version = entry["current_version"]
        new_version = _bump_version(old_version, bump)

        # Update entry
        entry["current_version"] = new_version
        entry["versions"].append(new_version)
        entry["updated_at"] = datetime.utcnow().isoformat() + "Z"
        entry["description"] = blueprint.get("description", entry["description"])
        entry["name"] = blueprint.get("name", entry["name"])
        entry["dependencies"] = _extract_dependencies(blueprint)
        entry["source_path"] = str(bp_path.absolute())

        blueprints[bp_id] = entry
        index["blueprints"] = blueprints

        # Copy to versions directory
        reg_path = Path(registry_path)
        version_dir = reg_path / "versions" / bp_id
        version_dir.mkdir(parents=True, exist_ok=True)
        shutil.copy(bp_path, version_dir / f"{new_version}.json")

        return {
            "index": index,
            "blueprints": blueprints,
            "updated": entry,
            "message": f"Updated {bp_id}: {old_version} -> {new_version}",
            "error": None
        }
    except Exception as e:
        return {"error": str(e)}


# =============================================================================
# BLUEPRINT RETRIEVAL
# =============================================================================

def get_blueprint(params: Dict[str, Any]) -> Dict[str, Any]:
    """Get a blueprint by ID and optionally version."""
    registry_path = params.get("registry_path")
    index = params.get("index")
    blueprint_id = params.get("blueprint_id")
    version = params.get("version")

    if not blueprint_id:
        return {"error": "No blueprint ID provided"}

    blueprints = index.get("blueprints", {})
    if blueprint_id not in blueprints:
        return {"error": f"Blueprint '{blueprint_id}' not found"}

    entry = blueprints[blueprint_id]
    target_version = version or entry["current_version"]

    if target_version not in entry["versions"]:
        return {"error": f"Version {target_version} not found for {blueprint_id}"}

    try:
        reg_path = Path(registry_path)
        bp_file = reg_path / "versions" / blueprint_id / f"{target_version}.json"

        if bp_file.exists():
            with open(bp_file) as f:
                blueprint_data = json.load(f)
        else:
            # Fall back to source path for current version
            if target_version == entry["current_version"]:
                source = entry.get("source_path")
                if source and Path(source).exists():
                    with open(source) as f:
                        blueprint_data = json.load(f)
                else:
                    blueprint_data = None
            else:
                blueprint_data = None

        result = {
            "metadata": entry,
            "data": blueprint_data
        }

        return {
            "blueprint": result,
            "blueprint_id": blueprint_id,
            "version": target_version,
            "error": None
        }
    except Exception as e:
        return {"error": str(e)}


def list_blueprints(params: Dict[str, Any]) -> Dict[str, Any]:
    """List all blueprints with optional filtering."""
    index = params.get("index")
    filter_tag = params.get("filter_tag")
    show_deprecated = params.get("filter_deprecated", False)

    if not index:
        return {"results": [], "stats": {}}

    blueprints = index.get("blueprints", {})
    results = []

    for bp_id, entry in blueprints.items():
        # Filter deprecated
        if not show_deprecated and entry.get("deprecated", False):
            continue

        # Filter by tag
        if filter_tag and filter_tag not in entry.get("tags", []):
            continue

        results.append({
            "id": bp_id,
            "name": entry.get("name", bp_id),
            "version": entry["current_version"],
            "description": entry.get("description", "")[:80],
            "tags": entry.get("tags", []),
            "deprecated": entry.get("deprecated", False),
            "updated_at": entry.get("updated_at", "")
        })

    # Sort by name
    results.sort(key=lambda x: x["name"].lower())
    stats = _compute_stats(blueprints)

    return {"results": results, "stats": stats}


def search_blueprints(params: Dict[str, Any]) -> Dict[str, Any]:
    """Search blueprints by query string."""
    index = params.get("index")
    query = params.get("query", "").lower()
    search_tags = params.get("search_tags", True)
    search_description = params.get("search_description", True)

    if not index or not query:
        return {"results": [], "query": query}

    blueprints = index.get("blueprints", {})
    results = []

    for bp_id, entry in blueprints.items():
        score = 0

        # Match ID
        if query in bp_id.lower():
            score += 10

        # Match name
        if query in entry.get("name", "").lower():
            score += 8

        # Match description
        if search_description and query in entry.get("description", "").lower():
            score += 5

        # Match tags
        if search_tags:
            for tag in entry.get("tags", []):
                if query in tag.lower():
                    score += 3

        if score > 0:
            results.append({
                "id": bp_id,
                "name": entry.get("name", bp_id),
                "version": entry["current_version"],
                "description": entry.get("description", "")[:80],
                "tags": entry.get("tags", []),
                "score": score,
                "deprecated": entry.get("deprecated", False)
            })

    # Sort by score descending
    results.sort(key=lambda x: -x["score"])

    return {"results": results, "query": query}


# =============================================================================
# VERSION CONTROL
# =============================================================================

def get_versions(params: Dict[str, Any]) -> Dict[str, Any]:
    """Get version history for a blueprint."""
    index = params.get("index")
    blueprint_id = params.get("blueprint_id")

    if not blueprint_id:
        return {"error": "No blueprint ID provided"}

    blueprints = index.get("blueprints", {})
    if blueprint_id not in blueprints:
        return {"error": f"Blueprint '{blueprint_id}' not found"}

    entry = blueprints[blueprint_id]
    versions = entry.get("versions", [])

    # Build version info
    version_info = []
    for v in reversed(versions):  # Most recent first
        info = {
            "version": v,
            "is_current": v == entry["current_version"]
        }
        version_info.append(info)

    return {
        "versions": version_info,
        "blueprint_id": blueprint_id,
        "error": None
    }


def compare_versions(params: Dict[str, Any]) -> Dict[str, Any]:
    """Compare two versions of a blueprint."""
    registry_path = params.get("registry_path")
    blueprint_id = params.get("blueprint_id")
    version_a = params.get("version_a")
    version_b = params.get("version_b")

    if not all([blueprint_id, version_a, version_b]):
        return {"error": "Missing blueprint_id, version_a, or version_b"}

    try:
        reg_path = Path(registry_path)
        file_a = reg_path / "versions" / blueprint_id / f"{version_a}.json"
        file_b = reg_path / "versions" / blueprint_id / f"{version_b}.json"

        if not file_a.exists():
            return {"error": f"Version {version_a} not found"}
        if not file_b.exists():
            return {"error": f"Version {version_b} not found"}

        with open(file_a) as f:
            bp_a = json.load(f)
        with open(file_b) as f:
            bp_b = json.load(f)

        diff = _diff_blueprints(bp_a, bp_b, version_a, version_b)

        return {"diff": diff, "error": None}
    except Exception as e:
        return {"error": str(e)}


def rollback_version(params: Dict[str, Any]) -> Dict[str, Any]:
    """Rollback to a previous version."""
    registry_path = params.get("registry_path")
    index = params.get("index")
    blueprint_id = params.get("blueprint_id")
    target_version = params.get("target_version")

    if not all([blueprint_id, target_version]):
        return {"error": "Missing blueprint_id or target_version"}

    blueprints = index.get("blueprints", {})
    if blueprint_id not in blueprints:
        return {"error": f"Blueprint '{blueprint_id}' not found"}

    entry = blueprints[blueprint_id]
    if target_version not in entry["versions"]:
        return {"error": f"Version {target_version} not found"}

    # Create a new version entry that points to the rollback
    old_current = entry["current_version"]
    new_version = _bump_version(old_current, "patch")

    try:
        reg_path = Path(registry_path)
        source_file = reg_path / "versions" / blueprint_id / f"{target_version}.json"
        target_file = reg_path / "versions" / blueprint_id / f"{new_version}.json"

        if source_file.exists():
            shutil.copy(source_file, target_file)

        entry["current_version"] = new_version
        entry["versions"].append(new_version)
        entry["updated_at"] = datetime.utcnow().isoformat() + "Z"

        blueprints[blueprint_id] = entry
        index["blueprints"] = blueprints

        return {
            "index": index,
            "blueprints": blueprints,
            "blueprint": entry,
            "message": f"Rolled back {blueprint_id} to {target_version} as {new_version}",
            "error": None
        }
    except Exception as e:
        return {"error": str(e)}


# =============================================================================
# DEPENDENCY MANAGEMENT
# =============================================================================

def get_dependencies(params: Dict[str, Any]) -> Dict[str, Any]:
    """Get dependency graph for a blueprint."""
    registry_path = params.get("registry_path")
    index = params.get("index")
    blueprint_id = params.get("blueprint_id")

    if not blueprint_id:
        return {"error": "No blueprint ID provided"}

    blueprints = index.get("blueprints", {})
    if blueprint_id not in blueprints:
        return {"error": f"Blueprint '{blueprint_id}' not found"}

    entry = blueprints[blueprint_id]
    direct_deps = entry.get("dependencies", [])

    # Build dependency tree
    graph = {
        "root": blueprint_id,
        "nodes": {},
        "edges": []
    }

    visited = set()
    _build_dep_tree(blueprint_id, blueprints, graph, visited)

    # Also find reverse dependencies (who depends on this)
    dependents = []
    for bp_id, bp_entry in blueprints.items():
        if bp_id != blueprint_id:
            if blueprint_id in bp_entry.get("dependencies", []):
                dependents.append(bp_id)

    graph["dependents"] = dependents

    return {"graph": graph, "error": None}


def check_circular_deps(params: Dict[str, Any]) -> Dict[str, Any]:
    """Check for circular dependencies."""
    index = params.get("index")
    blueprint_id = params.get("blueprint_id")

    blueprints = index.get("blueprints", {})

    if blueprint_id:
        # Check specific blueprint
        cycle = _detect_cycle(blueprint_id, blueprints)
        if cycle:
            return {
                "result": {
                    "has_cycle": True,
                    "cycle": cycle,
                    "message": f"Circular dependency detected: {' -> '.join(cycle)}"
                },
                "error": None
            }
        return {
            "result": {
                "has_cycle": False,
                "message": f"No circular dependencies for {blueprint_id}"
            },
            "error": None
        }
    else:
        # Check all blueprints
        all_cycles = []
        for bp_id in blueprints:
            cycle = _detect_cycle(bp_id, blueprints)
            if cycle and cycle not in all_cycles:
                all_cycles.append(cycle)

        if all_cycles:
            return {
                "result": {
                    "has_cycles": True,
                    "cycles": all_cycles,
                    "message": f"Found {len(all_cycles)} circular dependencies"
                },
                "error": None
            }
        return {
            "result": {
                "has_cycles": False,
                "message": "No circular dependencies found"
            },
            "error": None
        }


# =============================================================================
# LIFECYCLE MANAGEMENT
# =============================================================================

def deprecate_blueprint(params: Dict[str, Any]) -> Dict[str, Any]:
    """Mark a blueprint as deprecated."""
    index = params.get("index")
    blueprint_id = params.get("blueprint_id")
    reason = params.get("reason", "No reason provided")

    if not blueprint_id:
        return {"error": "No blueprint ID provided"}

    blueprints = index.get("blueprints", {})
    if blueprint_id not in blueprints:
        return {"error": f"Blueprint '{blueprint_id}' not found"}

    entry = blueprints[blueprint_id]
    entry["deprecated"] = True
    entry["deprecated_reason"] = reason
    entry["updated_at"] = datetime.utcnow().isoformat() + "Z"

    blueprints[blueprint_id] = entry
    index["blueprints"] = blueprints

    return {
        "index": index,
        "blueprints": blueprints,
        "message": f"Deprecated {blueprint_id}: {reason}",
        "error": None
    }


def delete_blueprint(params: Dict[str, Any]) -> Dict[str, Any]:
    """Delete a blueprint from the registry."""
    registry_path = params.get("registry_path")
    index = params.get("index")
    blueprint_id = params.get("blueprint_id")
    delete_files = params.get("delete_files", False)

    if not blueprint_id:
        return {"error": "No blueprint ID provided"}

    blueprints = index.get("blueprints", {})
    if blueprint_id not in blueprints:
        return {"error": f"Blueprint '{blueprint_id}' not found"}

    # Check for dependents
    dependents = []
    for bp_id, entry in blueprints.items():
        if bp_id != blueprint_id:
            if blueprint_id in entry.get("dependencies", []):
                dependents.append(bp_id)

    if dependents:
        return {
            "error": f"Cannot delete: {blueprint_id} is depended on by: "
                     f"{', '.join(dependents)}"
        }

    del blueprints[blueprint_id]
    index["blueprints"] = blueprints

    # Optionally delete version files
    if delete_files and registry_path:
        try:
            version_dir = Path(registry_path) / "versions" / blueprint_id
            if version_dir.exists():
                shutil.rmtree(version_dir)
        except Exception:
            pass  # Non-critical

    return {
        "index": index,
        "blueprints": blueprints,
        "message": f"Deleted {blueprint_id}",
        "error": None
    }


# =============================================================================
# EXPORT & STATISTICS
# =============================================================================

def export_registry(params: Dict[str, Any]) -> Dict[str, Any]:
    """Export registry metadata."""
    index = params.get("index")
    fmt = params.get("format", "json")

    if not index:
        return {"error": "No index loaded"}

    blueprints = index.get("blueprints", {})
    stats = _compute_stats(blueprints)

    export_data = {
        "registry_version": index.get("version", "1.0.0"),
        "exported_at": datetime.utcnow().isoformat() + "Z",
        "statistics": stats,
        "blueprints": {}
    }

    for bp_id, entry in blueprints.items():
        export_data["blueprints"][bp_id] = {
            "name": entry.get("name", bp_id),
            "current_version": entry["current_version"],
            "description": entry.get("description", ""),
            "tags": entry.get("tags", []),
            "dependencies": entry.get("dependencies", []),
            "deprecated": entry.get("deprecated", False),
            "owner": entry.get("owner", "unknown")
        }

    if fmt == "markdown":
        md_lines = ["# L++ Blueprint Registry Export", ""]
        md_lines.append(f"Exported: {export_data['exported_at']}")
        md_lines.append(f"Total: {stats['total']} blueprints")
        md_lines.append("")
        md_lines.append("| ID | Name | Version | Tags |")
        md_lines.append("|---|---|---|---|")
        for bp_id, bp in export_data["blueprints"].items():
            tags = ", ".join(bp["tags"][:3])
            md_lines.append(f"| {bp_id} | {bp['name']} | {bp['current_version']} | {tags} |")

        return {"data": {"format": "markdown", "content": "\n".join(md_lines)}, "error": None}

    return {"data": export_data, "error": None}


def get_stats(params: Dict[str, Any]) -> Dict[str, Any]:
    """Get registry statistics."""
    index = params.get("index")
    if not index:
        return {"stats": {}}

    blueprints = index.get("blueprints", {})
    return {"stats": _compute_stats(blueprints)}


# =============================================================================
# HELPER FUNCTIONS
# =============================================================================

def _compute_stats(blueprints: Dict) -> Dict[str, Any]:
    """Compute registry statistics."""
    total = len(blueprints)
    deprecated = sum(1 for b in blueprints.values() if b.get("deprecated", False))
    active = total - deprecated

    # Tag counts
    tag_counts = {}
    for entry in blueprints.values():
        for tag in entry.get("tags", []):
            tag_counts[tag] = tag_counts.get(tag, 0) + 1

    # Top tags
    top_tags = sorted(tag_counts.items(), key=lambda x: -x[1])[:5]

    return {
        "total": total,
        "active": active,
        "deprecated": deprecated,
        "top_tags": [{"tag": t, "count": c} for t, c in top_tags]
    }


def _bump_version(version: str, bump: str) -> str:
    """Bump semantic version."""
    try:
        parts = version.split(".")
        major = int(parts[0]) if len(parts) > 0 else 1
        minor = int(parts[1]) if len(parts) > 1 else 0
        patch = int(parts[2]) if len(parts) > 2 else 0

        if bump == "major":
            major += 1
            minor = 0
            patch = 0
        elif bump == "minor":
            minor += 1
            patch = 0
        else:  # patch
            patch += 1

        return f"{major}.{minor}.{patch}"
    except Exception:
        return "1.0.1"


def _extract_dependencies(blueprint: Dict) -> List[str]:
    """Extract dependencies from blueprint actions."""
    deps = set()
    actions = blueprint.get("actions", {})

    for action in actions.values():
        if action.get("type") == "compute":
            cu = action.get("compute_unit", "")
            # External dependencies have format "external_blueprint:function"
            if ":" in cu:
                ns = cu.split(":")[0]
                # Skip internal compute units (common prefixes)
                if ns not in ["viz", "rdm", "compose", "bpreg", "registry"]:
                    deps.add(ns)

    return list(deps)


def _diff_blueprints(bp_a: Dict, bp_b: Dict, v_a: str, v_b: str) -> Dict:
    """Compare two blueprint versions."""
    diff = {
        "version_a": v_a,
        "version_b": v_b,
        "changes": []
    }

    # Compare states
    states_a = set(bp_a.get("states", {}).keys())
    states_b = set(bp_b.get("states", {}).keys())

    added_states = states_b - states_a
    removed_states = states_a - states_b

    if added_states:
        diff["changes"].append({
            "type": "states_added",
            "items": list(added_states)
        })
    if removed_states:
        diff["changes"].append({
            "type": "states_removed",
            "items": list(removed_states)
        })

    # Compare transitions
    trans_a = {t["id"] for t in bp_a.get("transitions", [])}
    trans_b = {t["id"] for t in bp_b.get("transitions", [])}

    added_trans = trans_b - trans_a
    removed_trans = trans_a - trans_b

    if added_trans:
        diff["changes"].append({
            "type": "transitions_added",
            "items": list(added_trans)
        })
    if removed_trans:
        diff["changes"].append({
            "type": "transitions_removed",
            "items": list(removed_trans)
        })

    # Compare actions
    actions_a = set(bp_a.get("actions", {}).keys())
    actions_b = set(bp_b.get("actions", {}).keys())

    added_actions = actions_b - actions_a
    removed_actions = actions_a - actions_b

    if added_actions:
        diff["changes"].append({
            "type": "actions_added",
            "items": list(added_actions)
        })
    if removed_actions:
        diff["changes"].append({
            "type": "actions_removed",
            "items": list(removed_actions)
        })

    # Compare gates
    gates_a = set(bp_a.get("gates", {}).keys())
    gates_b = set(bp_b.get("gates", {}).keys())

    added_gates = gates_b - gates_a
    removed_gates = gates_a - gates_b

    if added_gates:
        diff["changes"].append({
            "type": "gates_added",
            "items": list(added_gates)
        })
    if removed_gates:
        diff["changes"].append({
            "type": "gates_removed",
            "items": list(removed_gates)
        })

    diff["summary"] = f"{len(diff['changes'])} change categories"

    return diff


def _build_dep_tree(bp_id: str, blueprints: Dict, graph: Dict, visited: set):
    """Recursively build dependency tree."""
    if bp_id in visited:
        return
    visited.add(bp_id)

    entry = blueprints.get(bp_id)
    if not entry:
        graph["nodes"][bp_id] = {"exists": False}
        return

    graph["nodes"][bp_id] = {
        "exists": True,
        "name": entry.get("name", bp_id),
        "version": entry["current_version"]
    }

    for dep in entry.get("dependencies", []):
        graph["edges"].append({"from": bp_id, "to": dep})
        _build_dep_tree(dep, blueprints, graph, visited)


def _detect_cycle(start: str, blueprints: Dict) -> Optional[List[str]]:
    """Detect circular dependencies using DFS."""
    visited = set()
    path = []

    def dfs(node):
        if node in path:
            cycle_start = path.index(node)
            return path[cycle_start:] + [node]

        if node in visited:
            return None

        visited.add(node)
        path.append(node)

        entry = blueprints.get(node)
        if entry:
            for dep in entry.get("dependencies", []):
                cycle = dfs(dep)
                if cycle:
                    return cycle

        path.pop()
        return None

    return dfs(start)


# =============================================================================
# COMPUTE REGISTRY - Maps compute_unit names to functions
# =============================================================================

COMPUTE_REGISTRY = {
    "bpreg:init_registry": init_registry,
    "bpreg:load_registry": load_registry,
    "bpreg:save_registry": save_registry,
    "bpreg:register_blueprint": register_blueprint,
    "bpreg:update_blueprint": update_blueprint,
    "bpreg:get_blueprint": get_blueprint,
    "bpreg:list_blueprints": list_blueprints,
    "bpreg:search_blueprints": search_blueprints,
    "bpreg:get_versions": get_versions,
    "bpreg:compare_versions": compare_versions,
    "bpreg:rollback_version": rollback_version,
    "bpreg:get_dependencies": get_dependencies,
    "bpreg:check_circular_deps": check_circular_deps,
    "bpreg:deprecate_blueprint": deprecate_blueprint,
    "bpreg:delete_blueprint": delete_blueprint,
    "bpreg:export_registry": export_registry,
    "bpreg:get_stats": get_stats,
}
