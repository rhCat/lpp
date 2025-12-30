"""
COMPUTE units for the L++ Visualizer

These are the pure computation functions
that the compiled visualizer operator calls.
All rendering logic delegates to readme_compute.py (single source of truth).
"""

import json
from pathlib import Path
from typing import Any, Dict

from frame_py.loader import BlueprintLoader


def load_blueprint(params: Dict[str, Any]) -> Dict[str, Any]:
    """Load an L++ blueprint from a JSON file."""
    path = params.get("path")
    if not path:
        return {"blueprint": None, "error": "No path provided"}

    try:
        path = Path(path)
        if not path.exists():
            return {"blueprint": None, "error": f"File not found: {path}"}

        with open(path) as f:
            raw = json.load(f)

        loader = BlueprintLoader(raw)
        blueprint = loader.load()

        # Convert to a dict-like structure for easy access in gates/display
        bp_data = {
            "id": blueprint.id,
            "name": blueprint.name,
            "version": blueprint.version,
            "description": blueprint.description,
            "states": {
                sid: {
                    "description": s.description
                } for sid, s in blueprint.states.items()},
            "transitions": [
                {
                    "id": t.id,
                    "from": t.from_state,
                    "to": t.to_state,
                    "on_event": t.on_event,
                    "gate": t.gates[0] if t.gates else None,
                    "gates": list(t.gates),
                    "actions": list(t.actions)
                }
                for t in blueprint.transitions
            ],
            "gates": {
                gid: {
                    "expression": g.expression
                } for gid, g in blueprint.gates.items()
            },
            "actions": {
                aid: {
                    "type": a.type.value
                } for aid, a in blueprint.actions.items()
            },
            "entry_state": blueprint.entry_state,
            "terminal_states": list(blueprint.terminal_states)
        }
        return {
            "blueprint": bp_data,
            "blueprint_name": blueprint.name,
            "blueprint_id": blueprint.id,
            "error": None
        }
    except Exception as e:
        return {"blueprint": None, "error": str(e)}


def zoom(params: Dict[str, Any]) -> Dict[str, Any]:
    """Adjust zoom level."""
    current = params.get("current", 1.0)
    direction = params.get("direction", 0)
    step = 0.25
    new_level = max(0.5, min(2.0, current + (direction * step)))
    return {"new_level": round(new_level, 2)}


def toggle(params: Dict[str, Any]) -> Dict[str, Any]:
    """Toggle a boolean value."""
    current = params.get("current", False)
    return {"result": not current}


def init_defaults(params: Dict[str, Any]) -> Dict[str, Any]:
    """Initialize default visualization settings."""
    return {
        "view_mode": "graph",
        "zoom_level": 1.0,
        "show_gates": True,
        "show_actions": True
    }


def render_graph(params: Dict[str, Any]) -> Dict[str, Any]:
    """Render blueprint as ASCII graph."""
    bp = params.get("blueprint")
    selected = params.get("selected")
    show_gates = params.get("show_gates", True)
    show_actions = params.get("show_actions", True)

    if not bp:
        return {"rendered": "No blueprint loaded"}

    lines = []
    lines.append("=" * 60)
    lines.append(f"  📊 {bp['name']} (v{bp['version']})")
    lines.append("=" * 60)

    # States section
    lines.append(
        "\n┌─ STATES ─────────────────────────────────────────────────┐")
    for sid, state in bp["states"].items():
        marker = "●" if sid == bp["entry_state"] else "○"
        if sid in bp["terminal_states"]:
            marker = "◉"
        sel = " ◀" if sid == selected else ""
        desc = state.get("description", "")[:40]
        lines.append(f"│  {marker} {sid:20} {desc}{sel}")
    lines.append(
        "└──────────────────────────────────────────────────────────┘")

    # Transitions section
    lines.append(
        "\n┌─ TRANSITIONS ────────────────────────────────────────────┐")
    for t in bp["transitions"]:
        arrow = f"{t['from']} ──[{t['on_event']}]──▶ {t['to']}"
        sel = " ◀" if t["id"] == selected else ""
        lines.append(f"│  {arrow}{sel}")

        if show_gates and t.get("gate"):
            gate_expr = bp["gates"].get(t["gate"], {}).get("expression", "?")
            lines.append(f"│    └─ gate: {t['gate']} = {gate_expr[:35]}")

        if show_actions and t.get("actions"):
            actions_str = ", ".join(t["actions"][:3])
            if len(t["actions"]) > 3:
                actions_str += f" (+{len(t['actions'])-3} more)"
            lines.append(f"│    └─ actions: {actions_str}")
    lines.append(
        "└──────────────────────────────────────────────────────────┘")

    return {"rendered": "\n".join(lines)}


def render_table(params: Dict[str, Any]) -> Dict[str, Any]:
    """Render blueprint as markdown tables - delegates to readme_compute."""
    bp = params.get("blueprint")
    if not bp:
        return {"rendered": "No blueprint loaded"}

    from .readme_compute import (
        states_table, gates_table, actions_table, transitions_table
    )

    parts = [
        states_table({"blueprint": bp})["table"],
        gates_table({"blueprint": bp})["table"],
        actions_table({"blueprint": bp})["table"],
        transitions_table({"blueprint": bp})["table"],
    ]

    return {"rendered": "\n".join(parts)}


def render_mermaid(params: Dict[str, Any]) -> Dict[str, Any]:
    """Render blueprint as Mermaid diagram - delegates to readme_compute."""
    bp = params.get("blueprint")
    if not bp:
        return {"rendered": "No blueprint loaded"}

    from .readme_compute import mermaid
    return {"rendered": mermaid({"blueprint": bp})["mermaid"]}


# =============================================================================
# COMPUTE REGISTRY - Maps compute_unit names to functions
# =============================================================================

COMPUTE_REGISTRY = {
    "viz:load_blueprint": load_blueprint,
    "viz:zoom": zoom,
    "viz:toggle": toggle,
    "viz:init_defaults": init_defaults,
    "viz:render_graph": render_graph,
    "viz:render_table": render_table,
    "viz:render_mermaid": render_mermaid,
}
