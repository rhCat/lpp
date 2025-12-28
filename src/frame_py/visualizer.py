"""
L++ Blueprint Visualizer

Generates flowchart visualizations from L++ blueprints.
Supports: ASCII art, Mermaid (GitHub/VS Code), DOT (Graphviz)
"""

import json
from typing import Dict, List, Tuple


# =========================================================================
# AUTO-SORT UTILITIES
# =========================================================================

def _sort_states(bp: dict) -> List[str]:
    """
    Sort states for optimal visualization:
    1. Entry state first
    2. States by reachability order (BFS from entry)
    3. Terminal states last
    """
    states = list(bp.get("states", {}).keys())
    entry = bp.get("entry_state", "")
    terminal = set(bp.get("terminal_states", []))
    transitions = bp.get("transitions", [])

    # Build adjacency
    adj: Dict[str, List[str]] = {s: [] for s in states}
    for trans in transitions:
        f = trans.get("from", "*")
        t = trans.get("to", "")
        if f == "*":
            for s in states:
                if t not in adj[s]:
                    adj[s].append(t)
        elif f in adj and t not in adj[f]:
            adj[f].append(t)

    # BFS from entry
    visited = []
    queue = [entry] if entry in states else []
    while queue:
        current = queue.pop(0)
        if current in visited:
            continue
        visited.append(current)
        for neighbor in adj.get(current, []):
            if neighbor not in visited:
                queue.append(neighbor)

    # Add any unvisited states
    for s in states:
        if s not in visited:
            visited.append(s)

    # Move terminal states to end
    result = [s for s in visited if s not in terminal]
    result.extend([s for s in visited if s in terminal])

    return result


def _sort_transitions(bp: dict) -> List[dict]:
    """
    Sort transitions for optimal visualization:
    1. Group by from-state (in state order)
    2. Within group: by event name
    3. Wildcard (*) transitions last
    """
    transitions = bp.get("transitions", [])
    sorted_states = _sort_states(bp)

    # Separate wildcard and specific
    wildcards = [t for t in transitions if t.get("from") == "*"]
    specific = [t for t in transitions if t.get("from") != "*"]

    # Sort specific by state order, then by event
    def sort_key(t):
        f = t.get("from", "")
        e = t.get("on_event", "")
        idx = sorted_states.index(f) if f in sorted_states else 999
        return (idx, e)

    specific.sort(key=sort_key)

    # Wildcards sorted by event
    wildcards.sort(key=lambda t: t.get("on_event", ""))

    return specific + wildcards


def visualize_blueprint(blueprint_path: str) -> str:
    """
    Generate ASCII flowchart from blueprint file.

    Args:
        blueprint_path: Path to JSON blueprint

    Returns:
        ASCII art representation
    """
    with open(blueprint_path, "r") as f:
        bp = json.load(f)
    return visualize_blueprint_dict(bp)


def visualize_blueprint_dict(bp: dict) -> str:
    """Generate ASCII flowchart from blueprint dictionary."""
    lines = []

    # Header
    name = bp.get("name", "Unnamed")
    version = bp.get("version", "0.0.0")
    lines.append("┌" + "─" * 60 + "┐")
    lines.append(f"│ {name} v{version}".ljust(61) + "│")
    lines.append("└" + "─" * 60 + "┘")
    lines.append("")

    # States section (auto-sorted)
    states = bp.get("states", {})
    sorted_state_ids = _sort_states(bp)
    entry = bp.get("entry_state", "")
    terminal = set(bp.get("terminal_states", []))

    lines.append("STATES")
    lines.append("=" * 40)
    for state_id in sorted_state_ids:
        state = states.get(state_id, {})
        marker = "►" if state_id == entry else " "
        term = " [TERMINAL]" if state_id in terminal else ""
        desc = state.get("description", "")
        box = _draw_state_box(state_id, desc, is_entry=(
            state_id == entry), is_terminal=(state_id in terminal))
        lines.extend(box)
        lines.append("")
    lines.append("")

    # Transitions as flowchart (auto-sorted)
    sorted_transitions = _sort_transitions(bp)
    gates = bp.get("gates", {})
    actions = bp.get("actions", {})

    lines.append("TRANSITIONS")
    lines.append("=" * 40)

    for trans in sorted_transitions:
        flow = _draw_transition(trans, gates, actions)
        lines.extend(flow)
        lines.append("")

    # Full flow diagram
    lines.append("")
    lines.append("FLOW DIAGRAM")
    lines.append("=" * 40)
    flow_diagram = _draw_flow_diagram(bp)
    lines.extend(flow_diagram)

    return "\n".join(lines)


def _draw_state_box(state_id: str, desc: str = "", is_entry: bool = False, is_terminal: bool = False) -> List[str]:
    """Draw a state as an ASCII box."""
    width = max(len(state_id) + 4, len(desc) + 4, 20)

    if is_terminal:
        # Double border for terminal
        top = "╔" + "═" * width + "╗"
        bot = "╚" + "═" * width + "╝"
        side = "║"
    else:
        top = "┌" + "─" * width + "┐"
        bot = "└" + "─" * width + "┘"
        side = "│"

    prefix = "► " if is_entry else "  "

    lines = [prefix + top]
    lines.append(prefix + side + f" {state_id}".ljust(width) + side)
    if desc:
        lines.append(prefix + side + f" {desc[:width-2]}".ljust(width) + side)
    lines.append(prefix + bot)

    return lines


def _draw_transition(trans: dict, gates: dict, actions: dict) -> List[str]:
    """Draw a single transition as flowchart."""
    lines = []

    tid = trans.get("id", "?")
    from_state = trans.get("from", "*")
    to_state = trans.get("to", "?")
    event = trans.get("on_event", "?")
    gate_ids = trans.get("gates", [])
    action_ids = trans.get("actions", [])

    # Transition header
    lines.append(f"  [{tid}] {from_state} ──({event})──► {to_state}")

    # Gates (diamond shape in ASCII)
    if gate_ids:
        lines.append("  │")
        for gid in gate_ids:
            gate = gates.get(gid, {})
            expr = gate.get("expression", "?")
            lines.append(f"  ◇── {gid}: {expr}")

    # Actions
    if action_ids:
        lines.append("  │")
        for aid in action_ids:
            action = actions.get(aid, {})
            atype = action.get("type", "?")
            if atype == "set":
                target = action.get("target", "?")
                if action.get("value") is not None:
                    lines.append(f"  ■── {aid}: {target} = {action['value']}")
                elif action.get("value_from"):
                    lines.append(
                        f"  ■── {aid}: {target} ← {action['value_from']}")
            elif atype == "compute":
                unit = action.get("compute_unit", "?")
                lines.append(f"  ■── {aid}: COMPUTE {unit}")

    return lines


def _draw_flow_diagram(bp: dict) -> List[str]:
    """Draw complete flow diagram showing state relationships."""
    lines = []

    # Use sorted states
    sorted_state_ids = _sort_states(bp)
    states_dict = bp.get("states", {})
    transitions = bp.get("transitions", [])
    entry = bp.get("entry_state", "")
    terminal = set(bp.get("terminal_states", []))

    # Build adjacency: from_state -> [(event, to_state, gates)]
    adj: Dict[str, List[Tuple[str, str, List[str]]]] = {
        s: [] for s in sorted_state_ids}
    adj["*"] = []  # wildcard

    for trans in transitions:
        f = trans.get("from", "*")
        t = trans.get("to", "")
        e = trans.get("on_event", "")
        g = trans.get("gates", [])
        if f in adj:
            adj[f].append((e, t, g))
        elif f == "*":
            adj["*"].append((e, t, g))

    # Calculate box widths
    max_state_len = max(len(s)
                        for s in sorted_state_ids) if sorted_state_ids else 10
    box_width = max_state_len + 4

    # Draw each state and its outgoing transitions (in sorted order)
    for state in sorted_state_ids:
        is_entry = state == entry
        is_term = state in terminal

        # State box
        prefix = "►" if is_entry else " "
        if is_term:
            lines.append(f"{prefix} ╔{'═' * box_width}╗")
            lines.append(f"  ║ {state.center(box_width - 2)} ║")
            lines.append(f"  ╚{'═' * box_width}╝")
        else:
            lines.append(f"{prefix} ┌{'─' * box_width}┐")
            lines.append(f"  │ {state.center(box_width - 2)} │")
            lines.append(f"  └{'─' * box_width}┘")

        # Outgoing transitions (sorted by event)
        outgoing = adj.get(state, []) + adj.get("*", [])
        outgoing.sort(key=lambda x: x[0])  # Sort by event name
        for event, to_state, gate_ids in outgoing:
            gate_str = f" [{','.join(gate_ids)}]" if gate_ids else ""
            arrow = f"  │──({event}){gate_str}──► {to_state}"
            lines.append(arrow)

        lines.append("  │")

    # Legend
    lines.append("")
    lines.append("  LEGEND")
    lines.append("  ──────")
    lines.append("  ►     = Entry state")
    lines.append("  ╔═══╗ = Terminal state")
    lines.append("  ┌───┐ = Normal state")
    lines.append("  ◇     = Gate (condition)")
    lines.append("  ■     = Action")
    lines.append("  (EVT) = Event trigger")

    return lines


def print_blueprint(blueprint_path: str) -> None:
    """Print ASCII visualization to stdout."""
    print(visualize_blueprint(blueprint_path))


# =========================================================================
# MERMAID FORMAT (GitHub, VS Code, Notion, etc.)
# =========================================================================

def to_mermaid(bp: dict) -> str:
    """
    Generate Mermaid flowchart from blueprint.

    Renders in GitHub markdown, VS Code, Notion, and mermaid.live
    """
    lines = []
    lines.append("```mermaid")
    lines.append("stateDiagram-v2")

    # Entry point
    entry = bp.get("entry_state", "")
    if entry:
        lines.append(f"    [*] --> {entry}")

    # Terminal states
    for term in bp.get("terminal_states", []):
        lines.append(f"    {term} --> [*]")

    # State descriptions (sorted)
    sorted_state_ids = _sort_states(bp)
    states_dict = bp.get("states", {})
    for state_id in sorted_state_ids:
        state = states_dict.get(state_id, {})
        desc = state.get("description", "")
        if desc:
            lines.append(f"    {state_id} : {desc}")

    # Transitions (sorted)
    sorted_transitions = _sort_transitions(bp)
    for trans in sorted_transitions:
        f = trans.get("from", "*")
        t = trans.get("to", "")
        e = trans.get("on_event", "")
        gates = trans.get("gates", [])

        # Handle wildcard - expand to all states
        if f == "*":
            from_states = sorted_state_ids
        else:
            from_states = [f]

        label = e
        if gates:
            label += f" [{','.join(gates)}]"

        for src in from_states:
            lines.append(f"    {src} --> {t} : {label}")

    lines.append("```")
    return "\n".join(lines)


def to_mermaid_flowchart(bp: dict) -> str:
    """
    Generate Mermaid flowchart (LR direction) showing full logic.
    """
    lines = []
    lines.append("```mermaid")
    lines.append("flowchart LR")

    # States as nodes (sorted)
    sorted_state_ids = _sort_states(bp)
    states_dict = bp.get("states", {})
    entry = bp.get("entry_state", "")
    terminal = set(bp.get("terminal_states", []))

    for state_id in sorted_state_ids:
        state = states_dict.get(state_id, {})
        desc = state.get("description", state_id)
        if state_id == entry:
            lines.append(f"    {state_id}[[\"{state_id}<br/>{desc}\"]]")
        elif state_id in terminal:
            lines.append(f"    {state_id}((\"{state_id}\"))")
        else:
            lines.append(f"    {state_id}[\"{state_id}<br/>{desc}\"]")

    # Transitions (sorted)
    gates = bp.get("gates", {})
    sorted_transitions = _sort_transitions(bp)
    for trans in sorted_transitions:
        f = trans.get("from", "*")
        t = trans.get("to", "")
        e = trans.get("on_event", "")
        gate_ids = trans.get("gates", [])

        # Build label
        label = e
        if gate_ids:
            gate_exprs = [gates.get(g, {}).get("expression", g)
                          for g in gate_ids]
            # Truncate long expressions
            short = [expr[:20] +
                     "..." if len(expr) > 20 else expr for expr in gate_exprs]
            label += f"<br/>({', '.join(short)})"

        if f == "*":
            from_states = sorted_state_ids
        else:
            from_states = [f]

        for src in from_states:
            lines.append(f"    {src} -->|\"{label}\"| {t}")

    lines.append("```")
    return "\n".join(lines)


# =========================================================================
# GRAPHVIZ DOT FORMAT
# =========================================================================

def to_dot(bp: dict) -> str:
    """
    Generate Graphviz DOT format.

    Render with: dot -Tpng blueprint.dot -o blueprint.png
    Or use online: https://dreampuf.github.io/GraphvizOnline/
    """
    lines = []
    name = bp.get("name", "blueprint").replace(" ", "_")

    lines.append(f"digraph {name} {{")
    lines.append("    rankdir=TB;")
    lines.append("    node [shape=box, style=rounded];")
    lines.append("")

    entry = bp.get("entry_state", "")
    terminal = set(bp.get("terminal_states", []))

    # Entry point
    if entry:
        lines.append("    __start__ [shape=point, width=0.2];")
        lines.append(f"    __start__ -> {entry};")
        lines.append("")

    # States (sorted)
    sorted_state_ids = _sort_states(bp)
    states_dict = bp.get("states", {})
    for state_id in sorted_state_ids:
        state = states_dict.get(state_id, {})
        desc = state.get("description", "")
        label = f"{state_id}\\n{desc}" if desc else state_id

        if state_id in terminal:
            lines.append(
                f'    {state_id} [label="{label}", shape=doublecircle];')
        elif state_id == entry:
            lines.append(
                f'    {state_id} [label="{label}", style="rounded,bold"];')
        else:
            lines.append(f'    {state_id} [label="{label}"];')

    lines.append("")

    # Transitions (sorted)
    gates = bp.get("gates", {})
    sorted_transitions = _sort_transitions(bp)
    for trans in sorted_transitions:
        f = trans.get("from", "*")
        t = trans.get("to", "")
        e = trans.get("on_event", "")
        gate_ids = trans.get("gates", [])

        label = e
        if gate_ids:
            label += f"\\n[{','.join(gate_ids)}]"

        if f == "*":
            from_states = sorted_state_ids
        else:
            from_states = [f]

        for src in from_states:
            lines.append(f'    {src} -> {t} [label="{label}"];')

    # Terminal exits
    if terminal:
        lines.append("")
        lines.append("    __end__ [shape=point, width=0.2];")
        for term in terminal:
            lines.append(f"    {term} -> __end__;")

    lines.append("}")
    return "\n".join(lines)


# =========================================================================
# FILE OUTPUT HELPERS
# =========================================================================

def save_visualization(blueprint_path: str, output_path: str, fmt: str = "ascii") -> None:
    """
    Save visualization to file.

    Args:
        blueprint_path: Path to JSON blueprint
        output_path: Path for output file
        fmt: Format - 'ascii', 'mermaid', 'mermaid-flow', 'dot'
    """
    with open(blueprint_path, "r") as f:
        bp = json.load(f)

    if fmt == "ascii":
        content = visualize_blueprint_dict(bp)
    elif fmt == "mermaid":
        content = to_mermaid(bp)
    elif fmt == "mermaid-flow":
        content = to_mermaid_flowchart(bp)
    elif fmt == "dot":
        content = to_dot(bp)
    else:
        raise ValueError(f"Unknown format: {fmt}")

    with open(output_path, "w") as f:
        f.write(content)


# CLI
if __name__ == "__main__":
    import sys

    usage = """Usage: python -m frame_py.visualizer <blueprint.json> [options]

Options:
    --compact, -c       Compact ASCII output
    --mermaid, -m       Mermaid state diagram (for GitHub/VS Code)
    --mermaid-flow      Mermaid flowchart (detailed)
    --dot, -d           Graphviz DOT format
    --output, -o FILE   Save to file instead of stdout

Examples:
    python -m frame_py.visualizer blueprint.json
    python -m frame_py.visualizer blueprint.json --mermaid
    python -m frame_py.visualizer blueprint.json --dot -o flow.dot
"""

    if len(sys.argv) < 2 or "--help" in sys.argv or "-h" in sys.argv:
        print(usage)
        sys.exit(0)

    # Parse args
    args = sys.argv[1:]
    bp_path = None
    output_path = None
    fmt = "ascii"
    compact = False

    i = 0
    while i < len(args):
        arg = args[i]
        if arg in ("--output", "-o") and i + 1 < len(args):
            output_path = args[i + 1]
            i += 2
        elif arg in ("--compact", "-c"):
            compact = True
            i += 1
        elif arg in ("--mermaid", "-m"):
            fmt = "mermaid"
            i += 1
        elif arg == "--mermaid-flow":
            fmt = "mermaid-flow"
            i += 1
        elif arg in ("--dot", "-d"):
            fmt = "dot"
            i += 1
        elif not arg.startswith("-"):
            bp_path = arg
            i += 1
        else:
            i += 1

    if not bp_path:
        print("Error: No blueprint file specified")
        print(usage)
        sys.exit(1)

    # Load blueprint
    with open(bp_path) as f:
        bp = json.load(f)

    # Generate output
    if compact and fmt == "ascii":
        lines = []
        lines.append(f"╔═ {bp.get('name', '?')} ═╗")
        lines.append("")
        for trans in bp.get("transitions", []):
            f, t = trans.get("from", "*"), trans.get("to", "?")
            e = trans.get("on_event", "?")
            g = trans.get("gates", [])
            gate_str = f" ?{','.join(g)}" if g else ""
            lines.append(f"  {f} ──({e}){gate_str}──► {t}")
        content = "\n".join(lines)
    elif fmt == "ascii":
        content = visualize_blueprint_dict(bp)
    elif fmt == "mermaid":
        content = to_mermaid(bp)
    elif fmt == "mermaid-flow":
        content = to_mermaid_flowchart(bp)
    elif fmt == "dot":
        content = to_dot(bp)
    else:
        content = visualize_blueprint_dict(bp)

    # Output
    if output_path:
        with open(output_path, "w") as f:
            f.write(content)
        print(f"Saved to: {output_path}")
    else:
        print(content)
