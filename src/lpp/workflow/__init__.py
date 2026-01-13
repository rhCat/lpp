"""
L++ Workflows

Pre-built workflows for common L++ tasks.

Available Workflows:
    python_to_lpp              - Convert Python projects to L++ blueprints
    logic_vulnerability_pointer - Security analysis and vulnerability detection
    lpp_canvas                 - Interactive blueprint design studio

Usage:
    from lpp.workflow.python_to_lpp import run
    result = run(project_path="/path/to/project", output_path="./output")

    from lpp.workflow import list_workflows, get_workflow
    workflows = list_workflows()
    lvp = get_workflow("logic_vulnerability_pointer")
"""

from pathlib import Path
from typing import Dict, List, Optional, Any

# Package directory
WORKFLOW_DIR = Path(__file__).parent

# All available workflows
WORKFLOWS = [
    "python_to_lpp",
    "logic_vulnerability_pointer",
    "lpp_canvas",
]


def list_workflows() -> List[str]:
    """List all available workflow names."""
    return WORKFLOWS.copy()


def get_workflow(name: str) -> Optional[Any]:
    """
    Get a workflow module by name.

    Args:
        name: Workflow name (e.g., "python_to_lpp")

    Returns:
        The workflow module or None if not found

    Example:
        py2lpp = get_workflow("python_to_lpp")
        result = py2lpp.run(project_path="/my/project")
    """
    if name not in WORKFLOWS:
        return None

    import importlib
    try:
        return importlib.import_module(f".{name}", package="lpp.workflow")
    except ImportError:
        return None


def get_workflow_info(name: str) -> Optional[Dict[str, Any]]:
    """
    Get information about a workflow.

    Returns dict with:
        - name: Workflow name
        - assembly_path: Path to assembly/blueprint JSON
        - description: From blueprint
        - phases: List of workflow phases
    """
    wf = get_workflow(name)
    if not wf:
        return None

    info = {
        "name": name,
        "assembly_path": str(getattr(wf, "ASSEMBLY_PATH", None)),
    }

    # Try to load assembly for more info
    bp_path = getattr(wf, "ASSEMBLY_PATH", None) or getattr(wf, "BLUEPRINT_PATH", None)
    if bp_path and Path(bp_path).exists():
        import json
        with open(bp_path) as f:
            bp = json.load(f)
        info["description"] = bp.get("description", "")
        info["version"] = bp.get("version", "")
        # Get phases from states
        states = bp.get("states", {})
        info["phases"] = [s for s in states.keys() if s.startswith("phase_")]

    return info


__all__ = [
    "WORKFLOWS",
    "list_workflows",
    "get_workflow",
    "get_workflow_info",
]
