"""
COMPUTE units for the L++ README Generator

These are the pure computation functions that the compiled L++ operator calls.
"""

from typing import Any, Dict
from pathlib import Path


def header(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate README header section."""
    bp = params.get("blueprint", {})

    lines = [
        f"# {bp.get('name', 'Untitled Blueprint')}",
        "",
    ]

    if bp.get("description"):
        lines.append(bp["description"])
        lines.append("")

    lines.append(f"**Version:** {bp.get('version', '0.0.0')}  ")
    lines.append(f"**ID:** `{bp.get('id', 'unknown')}`")
    lines.append("")

    return {"sections": lines}


def mermaid(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate mermaid state diagram."""
    bp = params.get("blueprint", {})

    lines = [
        "## State Machine",
        "",
        "```mermaid",
        "stateDiagram-v2",
        f"    [*] --> {bp.get('entry_state', 'init')}",
        "",
    ]

    # State definitions
    for sid in bp.get("states", {}).keys():
        lines.append(f"    {sid}: {sid}")
    lines.append("")

    # Transitions - expand wildcards, skip self-loops for cleaner diagram
    all_states = list(bp.get("states", {}).keys())
    for t in bp.get("transitions", []):
        label = t["on_event"]
        if t.get("gate"):
            label = f"{t['on_event']} [{t['gate']}]"

        from_states = all_states if t["from"] == "*" else [t["from"]]
        for from_state in from_states:
            if from_state != t["to"]:  # Skip self-loops
                lines.append(f"    {from_state} --> {t['to']}: {label}")

    # Terminal states
    for ts in bp.get("terminal_states", []):
        lines.append(f"    {ts} --> [*]")

    lines.append("```")
    lines.append("")

    return {"mermaid": "\n".join(lines)}


def states_table(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate states documentation table."""
    bp = params.get("blueprint", {})
    entry = bp.get("entry_state")
    terminals = bp.get("terminal_states", [])

    lines = [
        "## States",
        "",
        "| State | Description |",
        "|-------|-------------|",
    ]

    for sid, state in bp.get("states", {}).items():
        marker = ""
        if sid == entry:
            marker = "● "
        elif sid in terminals:
            marker = "◉ "
        desc = state.get("description", "")
        lines.append(f"| {marker}`{sid}` | {desc} |")

    lines.append("")
    return {"table": "\n".join(lines)}


def gates_table(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate gates documentation table."""
    bp = params.get("blueprint", {})
    gates = bp.get("gates", {})

    if not gates:
        return {"table": ""}

    lines = [
        "## Gates",
        "",
        "| Gate | Expression |",
        "|------|------------|",
    ]

    for gid, gate in gates.items():
        expr = gate.get("expression", "")
        lines.append(f"| `{gid}` | `{expr}` |")

    lines.append("")
    return {"table": "\n".join(lines)}


def actions_table(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate actions documentation table."""
    bp = params.get("blueprint", {})
    actions = bp.get("actions", {})

    if not actions:
        return {"table": ""}

    lines = [
        "## Actions",
        "",
        "| Action | Type |",
        "|--------|------|",
    ]

    for aid, action in actions.items():
        atype = action.get("type", "unknown")
        lines.append(f"| `{aid}` | {atype} |")

    lines.append("")
    return {"table": "\n".join(lines)}


def transitions_table(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate transitions documentation table."""
    bp = params.get("blueprint", {})
    transitions = bp.get("transitions", [])

    if not transitions:
        return {"table": ""}

    lines = [
        "## Transitions",
        "",
        "| ID | From | To | Event | Gate | Actions |",
        "|----|------|-----|-------|------|---------|",
    ]

    for t in transitions:
        tid = t.get("id", "-")
        frm = t.get("from", "-")
        to = t.get("to", "-")
        event = t.get("on_event", "-")
        gate = t.get("gate") or "-"
        actions = ", ".join(t.get("actions", [])) or "-"
        lines.append(
            f"| `{tid}` | {frm} | {to} | {event} | {gate} | {actions} |")

    lines.append("")
    return {"table": "\n".join(lines)}


def assemble(params: Dict[str, Any]) -> Dict[str, Any]:
    """Assemble all sections into final README."""
    sections = params.get("sections", [])
    mermaid = params.get("mermaid", "")
    states = params.get("states_table", "")
    gates = params.get("gates_table", "")
    actions = params.get("actions_table", "")
    transitions = params.get("transitions_table", "")

    parts = [
        "\n".join(sections) if isinstance(sections, list) else sections,
        mermaid,
        states,
        gates,
        actions,
        transitions,
        "---",
        "",
        "*Generated by L++ README Generator (compiled L++ operator)*",
    ]

    return {"content": "\n".join(parts)}


def write(params: Dict[str, Any]) -> Dict[str, Any]:
    """Write README to file."""
    content = params.get("content", "")
    path = params.get("path", "")

    if not path:
        return {"result": "No output path specified"}

    try:
        p = Path(path)
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(content)
        return {"result": f"Written to {path}"}
    except Exception as e:
        return {"result": f"Error: {e}"}


# Registry for the L++ COMPUTE dispatcher
COMPUTE_REGISTRY = {
    "rdm:header": header,
    "rdm:mermaid": mermaid,
    "rdm:states_table": states_table,
    "rdm:gates_table": gates_table,
    "rdm:actions_table": actions_table,
    "rdm:transitions_table": transitions_table,
    "rdm:assemble": assemble,
    "rdm:write": write,
}
