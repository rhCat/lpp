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


# =========================================================================
# HIERARCHICAL TREE VISUALIZATION
# =========================================================================

def tree_ascii(params: Dict[str, Any]) -> Dict[str, Any]:
    """Render hierarchical feature tree as ASCII art."""
    tree = params.get("tree", {})
    show_status = params.get("show_status", True)
    show_desc = params.get("show_desc", False)
    max_width = params.get("max_width", 60)

    if not tree:
        return {"rendered": "No tree provided"}

    lines = []
    _render_node(tree, lines, "", True, show_status, show_desc, max_width)
    return {"rendered": "\n".join(lines)}


def _render_node(node: dict, lines: list, prefix: str, is_last: bool,
                 show_status: bool, show_desc: bool, max_width: int):
    """Recursively render a tree node."""
    connector = "└── " if is_last else "├── "
    name = node.get("name", node.get("id", "?"))

    # Status indicator
    status = node.get("status", "pending")
    status_map = {
        "pending": "○",
        "expanded": "◐",
        "complete": "●",
        "failed": "✗",
        "in-progress": "◑"
    }
    marker = status_map.get(status, "○") if show_status else ""

    # Build line
    line = f"{prefix}{connector}{marker} {name}"
    if show_desc and node.get("desc"):
        desc = node["desc"][:max_width - len(line) - 3]
        line += f" - {desc}"
    lines.append(line)

    # Process children
    children = node.get("children", [])
    child_prefix = prefix + ("    " if is_last else "│   ")
    for i, child in enumerate(children):
        _render_node(child, lines, child_prefix, i == len(children) - 1,
                     show_status, show_desc, max_width)


def tree_mermaid(params: Dict[str, Any]) -> Dict[str, Any]:
    """Render hierarchical tree as Mermaid flowchart."""
    tree = params.get("tree", {})
    title = params.get("title", "Feature Tree")
    direction = params.get("direction", "TB")  # TB, LR, BT, RL

    if not tree:
        return {"mermaid": "No tree provided"}

    lines = [
        f"## {title}",
        "",
        "```mermaid",
        f"flowchart {direction}",
    ]

    # Collect all nodes and edges
    nodes = []
    edges = []
    _collect_tree(tree, nodes, edges, None)

    # Render nodes with styling
    for node_id, name, status in nodes:
        safe_name = name.replace('"', "'")
        shape = _node_shape(status)
        lines.append(f'    {node_id}{shape[0]}"{safe_name}"{shape[1]}')

    lines.append("")

    # Render edges
    for parent_id, child_id in edges:
        lines.append(f"    {parent_id} --> {child_id}")

    # Add status styling
    lines.extend([
        "",
        "    classDef pending fill:#f9f9f9,stroke:#999",
        "    classDef expanded fill:#e1f5fe,stroke:#0288d1",
        "    classDef complete fill:#c8e6c9,stroke:#388e3c",
        "    classDef failed fill:#ffcdd2,stroke:#d32f2f",
        "    classDef inprogress fill:#fff9c4,stroke:#f9a825",
    ])

    # Apply classes
    for node_id, _, status in nodes:
        cls = status.replace("-", "")
        lines.append(f"    class {node_id} {cls}")

    lines.append("```")
    lines.append("")

    return {"mermaid": "\n".join(lines)}


def _collect_tree(node: dict, nodes: list, edges: list, parent_id: str):
    """Recursively collect nodes and edges from tree."""
    node_id = node.get("id", f"n{len(nodes)}")
    name = node.get("name", node_id)
    status = node.get("status", "pending")

    nodes.append((node_id, name, status))

    if parent_id:
        edges.append((parent_id, node_id))

    for child in node.get("children", []):
        _collect_tree(child, nodes, edges, node_id)


def _node_shape(status: str) -> tuple:
    """Return Mermaid shape brackets based on status."""
    shapes = {
        "pending": ("[", "]"),
        "expanded": ("([", "])"),
        "complete": ("[[", "]]"),
        "failed": ("((", "))"),
        "in-progress": ("{", "}"),
    }
    return shapes.get(status, ("[", "]"))


def tree_summary(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate summary statistics for a hierarchical tree."""
    tree = params.get("tree", {})

    if not tree:
        return {"summary": {}, "table": "No tree provided"}

    stats = {"total": 0, "leaves": 0, "max_depth": 0, "by_status": {}}
    _count_tree(tree, stats, 0)

    # Build markdown table
    lines = [
        "## Tree Summary",
        "",
        "| Metric | Value |",
        "|--------|-------|",
        f"| Total Nodes | {stats['total']} |",
        f"| Leaf Nodes | {stats['leaves']} |",
        f"| Max Depth | {stats['max_depth']} |",
    ]

    for status, count in stats["by_status"].items():
        lines.append(f"| {status.title()} | {count} |")

    lines.append("")

    return {"summary": stats, "table": "\n".join(lines)}


def _count_tree(node: dict, stats: dict, depth: int):
    """Recursively count tree statistics."""
    stats["total"] += 1
    stats["max_depth"] = max(stats["max_depth"], depth)

    status = node.get("status", "pending")
    stats["by_status"][status] = stats["by_status"].get(status, 0) + 1

    children = node.get("children", [])
    if not children:
        stats["leaves"] += 1
    else:
        for child in children:
            _count_tree(child, stats, depth + 1)


def leaf_queue_table(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate table of leaf nodes from queue."""
    queue = params.get("leaf_queue", [])
    exec_count = params.get("exec_count", 0)

    if not queue:
        return {"table": "No leaves in queue"}

    lines = [
        "## Execution Queue",
        "",
        "| # | ID | Name | Status |",
        "|---|-----|------|--------|",
    ]

    for i, leaf in enumerate(queue):
        marker = "▶" if i == exec_count else ""
        status = leaf.get("status", "pending")
        name = leaf.get("name", leaf.get("id", "?"))[:40]
        lines.append(f"| {i+1}{marker} | `{leaf.get('id', '-')}` | {name} | {status} |")

    lines.append("")
    lines.append(f"**Progress:** {exec_count}/{len(queue)}")
    lines.append("")

    return {"table": "\n".join(lines)}


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
    # Hierarchical tree visualization
    "rdm:tree_ascii": tree_ascii,
    "rdm:tree_mermaid": tree_mermaid,
    "rdm:tree_summary": tree_summary,
    "rdm:leaf_queue_table": leaf_queue_table,
}
