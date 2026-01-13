"""
L++ Utility Tools

A collection of 29 utility tools for L++ development.

Categories:
    Blueprint Tools:
        blueprint_builder    - Build blueprints from code patterns
        blueprint_composer   - Compose blueprints hierarchically
        blueprint_debugger   - Step-through debugging
        blueprint_differ     - Semantic diff/merge
        blueprint_linter     - Static analysis
        blueprint_playground - Interactive web editor
        blueprint_registry   - Version management

    Code Analysis:
        logic_decoder       - Python to L++ reverse engineering
        legacy_extractor    - Extract state machines from legacy code
        function_decoder    - Analyze Python modularity

    Testing:
        test_generator      - Auto-generate comprehensive tests
        event_simulator     - Interactive simulation
        coverage_analyzer   - Runtime coverage tracking
        compliance_checker  - Policy verification

    Verification:
        tlaps_seal          - TLC + TLAPS certification
        tlaps_prover        - TLA+ proof generation

    Documentation:
        doc_generator       - Generate all documentation
        graph_visualizer    - Interactive visualization
        dashboard           - Project dashboard
        visualizer          - State machine diagrams

    Discovery:
        skill_registry      - Scan and catalog skills
        skill_contractor    - Autonomous skill generation
        task_orchestrator   - Task decomposition

    Integration:
        llm_assistant       - LLM-powered automation
        research_scraper    - Academic paper search
        scholar_chat        - Research synthesis

    Migration:
        schema_migrator     - Blueprint schema migration

    Search:
        interactive_search  - Refined interactive search with drill-down

Usage:
    from lpp.util.logic_decoder import run, COMPUTE_REGISTRY
    from lpp.util import list_utilities, get_utility
"""

from pathlib import Path
from typing import Dict, List, Optional, Any

# Package directory
UTIL_DIR = Path(__file__).parent

# All available utilities
UTILITIES = [
    "blueprint_builder",
    "blueprint_composer",
    "blueprint_debugger",
    "blueprint_differ",
    "blueprint_linter",
    "blueprint_playground",
    "blueprint_registry",
    "compliance_checker",
    "coverage_analyzer",
    "dashboard",
    "doc_generator",
    "event_simulator",
    "execution_tracer",
    "function_decoder",
    "graph_visualizer",
    "interactive_search",
    "legacy_extractor",
    "llm_assistant",
    "logic_decoder",
    "research_scraper",
    "schema_migrator",
    "scholar_chat",
    "skill_contractor",
    "skill_registry",
    "task_orchestrator",
    "test_generator",
    "tlaps_prover",
    "tlaps_seal",
    "visualizer",
]


def list_utilities() -> List[str]:
    """List all available utility names."""
    return UTILITIES.copy()


def get_utility(name: str) -> Optional[Any]:
    """
    Get a utility module by name.

    Args:
        name: Utility name (e.g., "logic_decoder")

    Returns:
        The utility module or None if not found

    Example:
        decoder = get_utility("logic_decoder")
        result = decoder.run({"target": "myfile.py"})
    """
    if name not in UTILITIES:
        return None

    import importlib
    try:
        return importlib.import_module(f".{name}", package="lpp.util")
    except ImportError:
        return None


def get_utility_info(name: str) -> Optional[Dict[str, Any]]:
    """
    Get information about a utility.

    Returns dict with:
        - name: Utility name
        - blueprint_path: Path to blueprint JSON
        - description: From blueprint
        - compute_units: List of compute unit names
    """
    util = get_utility(name)
    if not util:
        return None

    info = {
        "name": name,
        "blueprint_path": str(getattr(util, "BLUEPRINT_PATH", None)),
    }

    # Try to load blueprint for more info
    bp_path = getattr(util, "BLUEPRINT_PATH", None)
    if bp_path and Path(bp_path).exists():
        import json
        with open(bp_path) as f:
            bp = json.load(f)
        info["description"] = bp.get("description", "")
        info["version"] = bp.get("version", "")

    # Get compute units
    registry = getattr(util, "COMPUTE_REGISTRY", {})
    info["compute_units"] = list(registry.keys())

    return info


__all__ = [
    "UTILITIES",
    "list_utilities",
    "get_utility",
    "get_utility_info",
]
