"""
COMPUTE units for Skill Registry.
Pure functions: params: dict -> result: dict.
Scans L++ blueprints and generates agent context.
"""

import json
import os
from pathlib import Path
from typing import Any, Dict, List


def scan(params: Dict[str, Any]) -> Dict[str, Any]:
    """
    Scan directory for L++ skill blueprints.
    Input: basePath
    Output: skills (list of skill summaries), error
    """
    basePath = params.get("basePath", "")
    if not basePath:
        return {"skills": None, "error": "No basePath provided"}

    try:
        base = Path(basePath)
        if not base.exists():
            return {"skills": None, "error": f"Path not found: {basePath}"}

        skills = []
        for item in base.iterdir():
            if not item.is_dir():
                continue
            # Look for blueprint JSON
            for f in item.glob("*.json"):
                if f.name.startswith(".") or "compiled" in f.name:
                    continue
                try:
                    bp = json.loads(f.read_text())
                    if bp.get("$schema", "").startswith("lpp"):
                        skills.append({
                            "id": bp.get("id", f.stem),
                            "name": bp.get("name", f.stem),
                            "version": bp.get("version", "0.0.0"),
                            "description": bp.get("description", ""),
                            "path": str(f),
                            "dir": str(item),
                            "stateCount": len(bp.get("states", {})),
                            "transitionCount": len(bp.get("transitions", [])),
                            "gateCount": len(bp.get("gates", {})),
                            "actionCount": len(bp.get("actions", {}))
                        })
                except (json.JSONDecodeError, KeyError):
                    continue

        return {"skills": skills, "error": None}

    except Exception as e:
        return {"skills": None, "error": f"Scan error: {e}"}


def loadDetail(params: Dict[str, Any]) -> Dict[str, Any]:
    """
    Load full detail for a skill.
    Input: skillId, basePath
    Output: selectedSkill (full metadata), error
    """
    skillId = params.get("skillId", "")
    basePath = params.get("basePath", "")

    if not skillId:
        return {"selectedSkill": None, "error": "No skillId provided"}

    try:
        base = Path(basePath)
        skillDir = base / skillId
        if not skillDir.exists():
            # Try finding by ID in any subdir
            for d in base.iterdir():
                for f in d.glob("*.json"):
                    try:
                        bp = json.loads(f.read_text())
                        if bp.get("id") == skillId:
                            skillDir = d
                            break
                    except:
                        continue

        bpFile = None
        for f in skillDir.glob("*.json"):
            if not f.name.startswith(".") and "compiled" not in f.name:
                try:
                    bp = json.loads(f.read_text())
                    if bp.get("$schema", "").startswith("lpp"):
                        bpFile = f
                        break
                except:
                    continue

        if not bpFile:
            return {"selectedSkill": None, "error": f"Blueprint not found: {skillId}"}

        bp = json.loads(bpFile.read_text())

        # Extract context schema for flange spec
        ctxSchema = bp.get("context_schema", {}).get("properties", {})
        flangeSpec = {k: v.get("type", "any") for k, v in ctxSchema.items()}

        # Extract compute units from actions
        computeUnits = []
        for aName, action in bp.get("actions", {}).items():
            if action.get("type") == "compute":
                computeUnits.append({
                    "action": aName,
                    "unit": action.get("compute_unit", ""),
                    "inputs": list(action.get("input_map", {}).keys()),
                    "outputs": list(action.get("output_map", {}).keys())
                })

        # Load COMPUTE registry if exists
        srcDir = skillDir / "src"
        registryFns = []
        if srcDir.exists():
            for pyFile in srcDir.glob("*_compute.py"):
                content = pyFile.read_text()
                # Parse COMPUTE_REGISTRY
                if "COMPUTE_REGISTRY" in content:
                    import re
                    matches = re.findall(
                        r'"([^"]+)":\s*(\w+)',
                        content.split("COMPUTE_REGISTRY")[1][:500]
                    )
                    registryFns = [{"key": m[0], "fn": m[1]} for m in matches]

        detail = {
            "id": bp.get("id"),
            "name": bp.get("name"),
            "version": bp.get("version"),
            "description": bp.get("description"),
            "path": str(bpFile),
            "states": list(bp.get("states", {}).keys()),
            "entryState": bp.get("entry_state"),
            "terminalStates": bp.get("terminal_states", []),
            "gates": list(bp.get("gates", {}).keys()),
            "actions": list(bp.get("actions", {}).keys()),
            "transitions": [
                {
                    "id": t.get("id"),
                    "from": t.get("from"),
                    "to": t.get("to"),
                    "event": t.get("on_event"),
                    "gates": t.get("gates", []),
                    "actions": t.get("actions", [])
                }
                for t in bp.get("transitions", [])
            ],
            "flangeSpec": flangeSpec,
            "computeUnits": computeUnits,
            "registryFunctions": registryFns
        }

        return {"selectedSkill": detail, "error": None}

    except Exception as e:
        return {"selectedSkill": None, "error": f"Load error: {e}"}


def export(params: Dict[str, Any]) -> Dict[str, Any]:
    """
    Export full registry as agent context.
    Input: skills, basePath
    Output: registry (structured context for agent), error
    """
    skills = params.get("skills", [])
    basePath = params.get("basePath", "")

    if not skills:
        return {"registry": None, "error": "No skills to export"}

    try:
        registry = {
            "meta": {
                "basePath": basePath,
                "skillCount": len(skills),
                "generatedAt": __import__("datetime").datetime.now().isoformat()
            },
            "skills": {},
            "patterns": {
                "commonStates": {},
                "commonGates": {},
                "commonActions": {}
            }
        }

        allStates = {}
        allGates = {}
        allActions = {}

        for skill in skills:
            # Load full detail for each skill
            detail = loadDetail({
                "skillId": skill["id"],
                "basePath": basePath
            })["selectedSkill"]

            if not detail:
                continue

            registry["skills"][skill["id"]] = {
                "name": detail["name"],
                "version": detail["version"],
                "description": detail["description"],
                "states": detail["states"],
                "entryState": detail["entryState"],
                "gates": detail["gates"],
                "actions": detail["actions"],
                "flangeSpec": detail["flangeSpec"],
                "computeUnits": detail["computeUnits"],
                "transitionGraph": [
                    f"{t['from']} --[{t['event']}]--> {t['to']}"
                    for t in detail["transitions"]
                ]
            }

            # Collect patterns
            for s in detail["states"]:
                allStates[s] = allStates.get(s, 0) + 1
            for g in detail["gates"]:
                allGates[g] = allGates.get(g, 0) + 1
            for a in detail["actions"]:
                allActions[a] = allActions.get(a, 0) + 1

        # Find common patterns (appear in > 1 skill)
        registry["patterns"]["commonStates"] = {
            k: v for k, v in allStates.items() if v > 1
        }
        registry["patterns"]["commonGates"] = {
            k: v for k, v in allGates.items() if v > 1
        }
        registry["patterns"]["commonActions"] = {
            k: v for k, v in allActions.items() if v > 1
        }

        return {"registry": registry, "error": None}

    except Exception as e:
        return {"registry": None, "error": f"Export error: {e}"}


def formatContext(params: Dict[str, Any]) -> Dict[str, Any]:
    """
    Format registry as markdown for agent context.
    Input: registry
    Output: markdown, error
    """
    registry = params.get("registry")
    if not registry:
        return {"markdown": None, "error": "No registry provided"}

    try:
        lines = [
            "# L++ Skill Registry",
            f"Generated: {registry['meta']['generatedAt']}",
            f"Skills: {registry['meta']['skillCount']}",
            "",
            "## Available Skills",
            ""
        ]

        for sid, skill in registry.get("skills", {}).items():
            lines.append(f"### {skill['name']} ({sid})")
            lines.append(f"_{skill['description']}_")
            lines.append("")
            lines.append(f"**States**: {', '.join(skill['states'])}")
            lines.append(f"**Entry**: {skill['entryState']}")
            lines.append("")
            lines.append("**Flange Spec (Context Schema)**:")
            for k, v in skill.get("flangeSpec", {}).items():
                lines.append(f"  - `{k}`: {v}")
            lines.append("")
            lines.append("**COMPUTE Units**:")
            for cu in skill.get("computeUnits", []):
                lines.append(
                    f"  - `{cu['unit']}`: {cu['inputs']} -> {cu['outputs']}")
            lines.append("")
            lines.append("**Transition Graph**:")
            for t in skill.get("transitionGraph", []):
                lines.append(f"  - {t}")
            lines.append("")

        if registry.get("patterns", {}).get("commonStates"):
            lines.append("## Common Patterns")
            lines.append("")
            lines.append("**Reusable States**:")
            for s, cnt in registry["patterns"]["commonStates"].items():
                lines.append(f"  - `{s}` (used in {cnt} skills)")
            lines.append("")

        return {"markdown": "\n".join(lines), "error": None}

    except Exception as e:
        return {"markdown": None, "error": f"Format error: {e}"}


COMPUTE_REGISTRY = {
    "registry:scan": scan,
    "registry:loadDetail": loadDetail,
    "registry:export": export,
    "registry:formatContext": formatContext,
}
