"""
Python to L++ Refactorer - Compute Functions

Orchestrates existing L++ utils to refactor Python projects into L++ blueprints.
This workflow USES utils tools rather than reimplementing functionality.
"""
import os
import sys
import json
from pathlib import Path
from typing import Dict, Any

# Add utils to path for imports
_WORKFLOW_DIR = Path(__file__).parent.parent
_LPP_ROOT = _WORKFLOW_DIR.parent.parent
_UTILS_DIR = _LPP_ROOT / "utils"

# Global state for the workflow
_state: Dict[str, Any] = {}

# Lazy-loaded util registries
_utils_loaded = False
_DOC_REGISTRY = None
_LEGACY_REGISTRY = None
_LOGIC_REGISTRY = None
_DASHBOARD_REGISTRY = None
_BLUEPRINT_REGISTRY = None


def _load_utils():
    """Lazy load utils to avoid import errors if utils don't exist."""
    global _utils_loaded, _DOC_REGISTRY, _LEGACY_REGISTRY
    global _LOGIC_REGISTRY, _DASHBOARD_REGISTRY, _BLUEPRINT_REGISTRY
    import importlib.util

    if _utils_loaded:
        return

    def load_module(util_name, module_file, registry_name):
        """Load a module by file path and extract registry."""
        module_path = _UTILS_DIR / util_name / "src" / module_file
        if not module_path.exists():
            return None
        try:
            spec = importlib.util.spec_from_file_location(
                f"{util_name}_{module_file}", module_path)
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            return getattr(module, registry_name, None)
        except Exception:
            return None

    _DOC_REGISTRY = load_module("doc_generator", "docgen_compute.py",
                                 "COMPUTE_REGISTRY")
    _LEGACY_REGISTRY = load_module("legacy_extractor", "extractor_compute.py",
                                    "EXTRACT_REGISTRY")
    _LOGIC_REGISTRY = load_module("logic_decoder", "logic_compute.py",
                                   "COMPUTE_REGISTRY")
    _DASHBOARD_REGISTRY = load_module("dashboard", "dashboard_compute.py",
                                       "COMPUTE_REGISTRY")
    _BLUEPRINT_REGISTRY = load_module("blueprint_builder", "blueprint_compute.py",
                                       "COMPUTE_REGISTRY")

    _utils_loaded = True


def init(params: dict) -> dict:
    """Initialize the refactoring workflow."""
    global _state
    _state = {
        "projectPath": params.get("projectPath", ""),
        "outputPath": params.get("outputPath", ""),
        "projectName": params.get("projectName", ""),
        "options": params.get("options", {}),
        "pythonFiles": [],
        "extractedModules": [],
        "blueprints": [],
        "results": {"modulesFound": 0, "blueprintsGenerated": 0,
                    "docsGenerated": 0, "errors": []},
        "error": None
    }
    _load_utils()
    return {
        "initialized": True,
        "utilsAvailable": {
            "doc_generator": _DOC_REGISTRY is not None,
            "legacy_extractor": _LEGACY_REGISTRY is not None,
            "logic_decoder": _LOGIC_REGISTRY is not None,
            "dashboard": _DASHBOARD_REGISTRY is not None,
            "blueprint_builder": _BLUEPRINT_REGISTRY is not None
        }
    }


def scanProject(params: dict) -> dict:
    """Scan the Python project for source files."""
    projectPath = _state.get("projectPath") or params.get("projectPath", "")
    if not projectPath or not os.path.isdir(projectPath):
        return {"error": f"Invalid project path: {projectPath}", "files": []}

    _state["projectPath"] = projectPath
    _state["outputPath"] = _state.get("outputPath") or \
        os.path.join(projectPath, "lpp_output")
    _state["projectName"] = _state.get("projectName") or \
        os.path.basename(projectPath.rstrip("/"))

    pythonFiles = []
    includeTests = _state["options"].get("includeTests", False)
    skipDirs = {"__pycache__", ".git", ".venv", "venv", "env", "node_modules",
                ".tox", ".pytest_cache", "dist", "build", "lpp_output"}

    for root, dirs, files in os.walk(projectPath):
        dirs[:] = [d for d in dirs if d not in skipDirs]
        if not includeTests:
            dirs[:] = [d for d in dirs if d not in ["tests", "test"]]
        for f in files:
            if f.endswith(".py") and (includeTests or not f.startswith("test_")):
                filepath = os.path.join(root, f)
                relpath = os.path.relpath(filepath, projectPath)
                pythonFiles.append({
                    "path": filepath, "relpath": relpath, "name": f,
                    "module": relpath.replace("/", ".").replace(".py", "")
                })

    _state["pythonFiles"] = pythonFiles
    return {"files": pythonFiles, "count": len(pythonFiles)}


def extractPatterns(params: dict) -> dict:
    """Extract patterns using legacy_extractor util."""
    pythonFiles = _state.get("pythonFiles", [])

    if not _LEGACY_REGISTRY:
        return {"error": "legacy_extractor util not available", "count": 0}

    extractedModules = []
    for fileInfo in pythonFiles:
        try:
            # Use existing extractor pipeline
            result = _LEGACY_REGISTRY["extract:loadSource"](
                {"filePath": fileInfo["path"]})
            if result.get("error"):
                continue
            source = result["sourceCode"]

            result = _LEGACY_REGISTRY["extract:parseAst"]({"sourceCode": source})
            if result.get("error"):
                continue
            astDict = result["ast"]

            result = _LEGACY_REGISTRY["extract:findStatePatterns"](
                {"ast": astDict, "sourceCode": source})
            patterns = result.get("patterns", {})

            # Check if we found meaningful patterns
            if patterns.get("stateClasses") or patterns.get("eventHandlers"):
                # Extract states for module info
                stateResult = _LEGACY_REGISTRY["extract:extractStates"](
                    {"ast": astDict, "patterns": patterns})
                states = stateResult.get("states", [])

                # Build module from class info
                for cls in patterns.get("stateClasses", []):
                    extractedModules.append({
                        "name": cls["name"],
                        "file": fileInfo,
                        "methods": cls.get("methods", []),
                        "states": [s["id"] for s in states],
                        "patterns": patterns,
                        "docstring": "",
                        "source": "legacy_extractor"
                    })
        except Exception as e:
            _state["results"]["errors"].append((fileInfo["relpath"], str(e)))

    _state["extractedModules"] = extractedModules
    _state["results"]["modulesFound"] = len(extractedModules)
    return {"modules": extractedModules, "count": len(extractedModules)}


def decodeLogic(params: dict) -> dict:
    """Decode logic patterns using logic_decoder util."""
    modules = _state.get("extractedModules", [])

    if not _LOGIC_REGISTRY:
        _state["decodedLogic"] = modules
        return {"decoded": modules, "count": len(modules)}

    decodedLogic = []
    for module in modules:
        try:
            result = _LOGIC_REGISTRY["logic:decode"]({
                "module": module, "filePath": module["file"]["path"]
            })
            decodedLogic.append({
                **module,
                "gates": result.get("gates", []),
                "actions": result.get("actions", []),
                "controlFlow": result.get("controlFlow", {})
            })
        except Exception as e:
            _state["results"]["errors"].append(
                (module["file"]["relpath"], str(e)))
            decodedLogic.append(module)

    _state["decodedLogic"] = decodedLogic
    return {"decoded": decodedLogic, "count": len(decodedLogic)}


def generateBlueprints(params: dict) -> dict:
    """Generate L++ blueprints using blueprint_builder util."""
    modules = _state.get("decodedLogic") or _state.get("extractedModules", [])
    outputPath = _state.get("outputPath", "")

    if not _BLUEPRINT_REGISTRY:
        return {"error": "blueprint_builder util not available", "count": 0}

    _BLUEPRINT_REGISTRY["blueprint:init"]({})
    blueprints = []

    for module in modules:
        try:
            # Build blueprint using the util
            result = _BLUEPRINT_REGISTRY["blueprint:buildFromClass"](
                {"module": module})
            bp = result.get("blueprint")

            if bp:
                blueprints.append(bp)
                # Write to output
                if outputPath:
                    bpDir = os.path.join(outputPath, bp["id"])
                    os.makedirs(bpDir, exist_ok=True)
                    with open(os.path.join(bpDir, f"{bp['id']}.json"), "w") as f:
                        json.dump(bp, f, indent=2)
        except Exception as e:
            _state["results"]["errors"].append(
                (module.get("name", "unknown"), str(e)))

    _state["blueprints"] = blueprints
    _state["results"]["blueprintsGenerated"] = len(blueprints)
    return {"blueprints": blueprints, "count": len(blueprints)}


def generateCompute(params: dict) -> dict:
    """Generate compute function stubs for blueprints."""
    blueprints = _state.get("blueprints", [])
    outputPath = _state.get("outputPath", "")
    generated = 0

    stub = '''"""Compute functions for {name}."""
from typing import Dict, Any

_state: Dict[str, Any] = {{}}

def execute(params: dict) -> dict:
    """Execute main action."""
    # TODO: Implement
    return {{"success": True}}

COMPUTE_REGISTRY = {{
    "{id}:execute": execute,
}}
'''

    for bp in blueprints:
        try:
            computeDir = os.path.join(outputPath, bp["id"], "src")
            os.makedirs(computeDir, exist_ok=True)
            code = stub.format(name=bp["name"], id=bp["id"])
            with open(os.path.join(computeDir, f"{bp['id']}_compute.py"), "w") as f:
                f.write(code)
            generated += 1
        except Exception as e:
            _state["results"]["errors"].append((bp["id"], str(e)))

    return {"generated": generated}


def generateDocs(params: dict) -> dict:
    """Generate documentation using doc_generator util."""
    outputPath = _state.get("outputPath", "")
    if not outputPath or not _state.get("blueprints"):
        return {"generated": 0}

    if not _DOC_REGISTRY:
        return {"error": "doc_generator util not available", "generated": 0}

    try:
        _DOC_REGISTRY["docgen:init"]({"options": {"all": True}})
        _DOC_REGISTRY["docgen:discoverBlueprints"]({"utilsPath": outputPath})
        g = _DOC_REGISTRY["docgen:generateGraphs"]({}).get("generated", 0)
        m = _DOC_REGISTRY["docgen:generateMermaid"]({}).get("generated", 0)
        r = _DOC_REGISTRY["docgen:updateReadmes"]({}).get("updated", 0)
        _DOC_REGISTRY["docgen:generateReport"]({"utilsPath": outputPath})
        total = g + m + r + 1
        _state["results"]["docsGenerated"] = total
        return {"generated": total}
    except Exception as e:
        _state["results"]["errors"].append(("doc_generator", str(e)))
        return {"generated": 0, "error": str(e)}


def generateDashboard(params: dict) -> dict:
    """Generate dashboard using dashboard util."""
    outputPath = _state.get("outputPath", "")
    if not outputPath or not _DASHBOARD_REGISTRY:
        return {"generated": False}

    try:
        result = _DASHBOARD_REGISTRY["dashboard:scanTools"](
            {"utilsPath": outputPath})
        if result.get("hasTools"):
            tools = _DASHBOARD_REGISTRY["dashboard:analyzeTools"](
                {"tools": result["tools"]}).get("tools", [])
            cats = _DASHBOARD_REGISTRY["dashboard:categorizeTools"](
                {"tools": tools})
            result = _DASHBOARD_REGISTRY["dashboard:generateDashboard"]({
                "tools": tools, "categories": cats.get("categories", {}),
                "statistics": cats.get("statistics", {}),
                "basePath": outputPath,
                "outputPath": os.path.join(outputPath, "dashboard.html")
            })
            return {"generated": result.get("hasHtml", False)}
    except Exception as e:
        _state["results"]["errors"].append(("dashboard", str(e)))
    return {"generated": False}


def validate(params: dict) -> dict:
    """Validate generated blueprints using blueprint_builder."""
    blueprints = _state.get("blueprints", [])

    if _BLUEPRINT_REGISTRY:
        all_errors, all_warnings = [], []
        for bp in blueprints:
            result = _BLUEPRINT_REGISTRY["blueprint:validate"](
                {"blueprint": bp})
            all_errors.extend(result.get("errors", []))
            all_warnings.extend(result.get("warnings", []))
        return {"valid": len(all_errors) == 0,
                "errors": all_errors, "warnings": all_warnings}

    # Fallback minimal validation
    errors = []
    for bp in blueprints:
        for field in ["id", "name", "states", "entry_state"]:
            if field not in bp:
                errors.append(f"{bp.get('id', '?')}: Missing '{field}'")
    return {"valid": len(errors) == 0, "errors": errors, "warnings": []}


def finalize(params: dict) -> dict:
    """Finalize refactoring and create summary."""
    outputPath = _state.get("outputPath", "")
    blueprints = _state.get("blueprints", [])
    results = _state.get("results", {})

    summary = {
        "projectName": _state.get("projectName", ""),
        "outputPath": outputPath,
        "modulesFound": results.get("modulesFound", 0),
        "blueprintsGenerated": results.get("blueprintsGenerated", 0),
        "docsGenerated": results.get("docsGenerated", 0),
        "errors": results.get("errors", []),
        "blueprints": [bp["id"] for bp in blueprints],
        "utilsUsed": {
            "blueprint_builder": _BLUEPRINT_REGISTRY is not None,
            "doc_generator": _DOC_REGISTRY is not None,
            "legacy_extractor": _LEGACY_REGISTRY is not None,
            "logic_decoder": _LOGIC_REGISTRY is not None,
            "dashboard": _DASHBOARD_REGISTRY is not None
        }
    }

    if outputPath:
        with open(os.path.join(outputPath, "refactor_summary.json"), "w") as f:
            json.dump(summary, f, indent=2)
        with open(os.path.join(outputPath, "README.md"), "w") as f:
            f.write(f"# {summary['projectName']} - L++ Refactored\n\n"
                    f"Modules: {summary['modulesFound']} | "
                    f"Blueprints: {summary['blueprintsGenerated']}\n")

    return summary


COMPUTE_REGISTRY = {
    "py2lpp:init": init,
    "py2lpp:scanProject": scanProject,
    "py2lpp:extractPatterns": extractPatterns,
    "py2lpp:decodeLogic": decodeLogic,
    "py2lpp:generateBlueprints": generateBlueprints,
    "py2lpp:generateCompute": generateCompute,
    "py2lpp:generateDocs": generateDocs,
    "py2lpp:generateDashboard": generateDashboard,
    "py2lpp:validate": validate,
    "py2lpp:finalize": finalize,
}
