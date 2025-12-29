#!/usr/bin/env python3
"""
L++ Blueprint Visualizer (Logic CAD Edition)

Generates deterministic visualizations from L++ blueprints.
Focuses on the 4 Atomic Units:
EVALUATE (Gate),
DISPATCH (Action),
MUTATE,
TRANSITION.
"""

import json
import argparse
import sys
from typing import Dict, List, Any, Set


class LppVisualizer:
    def __init__(self, bp: Dict[str, Any]):
        self.bp = bp
        self.name = bp.get("name", "Unnamed Logic")
        self.version = bp.get("version", "0.0.0")
        self.entry = bp.get("entry_state", "")
        self.terminal = set(bp.get("terminal_states", []))
        self.states = bp.get("states", {})
        self.gates = bp.get("gates", {})
        self.actions = bp.get("actions", {})
        self.transitions = bp.get("transitions", [])

        # Pre-calculate sorted order for deterministic output
        self.sorted_state_ids = self._compute_sort_states()

    def _compute_sort_states(self) -> List[str]:
        """BFS-based reachability sorting."""
        all_ids = list(self.states.keys())
        if not self.entry:
            return sorted(all_ids)

        visited = []
        queue = [self.entry]

        # Build simple adjacency
        adj = {s: set() for s in all_ids}
        for t in self.transitions:
            f, to = t.get("from"), t.get("to")
            if f == "*":
                for s in all_ids:
                    adj[s].add(to)
            elif f in adj:
                adj[f].add(to)

        while queue:
            curr = queue.pop(0)
            if curr not in visited and curr in adj:
                visited.append(curr)
                queue.extend(sorted(list(adj[curr] - set(visited))))

        # Append orphans
        for s in sorted(all_ids):
            if s not in visited:
                visited.append(s)
        return visited

    def _get_transition_label(self, t: Dict) -> str:
        event = t.get("on_event", "ANY")
        gates = t.get("gates", [])
        return f"{event} [{', '.join(gates)}]" if gates else event

    # =========================================================================
    # MERMAID LOGIC (The "Logic CAD" View)
    # =========================================================================

    def as_mermaid_logic(self) -> str:
        """
        Generates a Logic-First flowchart with
        Diamonds (Gates) and Rects (Actions).
        """
        lines = ["flowchart TD", "    %% L++ Logic CAD Export"]

        # Define States
        for s_id in self.sorted_state_ids:
            desc = self.states.get(s_id, {}).get("description", "")
            label = f"<b>{s_id}</b><br/>{desc}" if desc else s_id
            shape = f'state_{s_id}(["{label}"])'
            if s_id == self.entry:
                shape += ":::entry"
            if s_id in self.terminal:
                shape += ":::terminal"
            lines.append(f"    {shape}")

        # Define Transitions
        for i, t in enumerate(self.transitions):
            f, to, event = t.get("from"), t.get("to"), t.get("on_event", "ANY")
            gate_ids = t.get("gates", [])
            action_ids = t.get("actions", [])

            sources = self.sorted_state_ids if f == "*" else [f]

            for s_idx, src in enumerate(sources):
                path_id = f"t_{i}_{s_idx}"
                curr = f"state_{src}"

                # 1. Evaluate (Gate)
                if gate_ids:
                    g_node = f"gate_{path_id}"
                    gate_label = ", ".join(gate_ids)
                    lines.append(f'    {g_node}{{{{"{gate_label}?"}}}}')
                    lines.append(f'    {curr} -- "{event}" --> {g_node}')
                    curr = g_node
                    link = " -- True --> "
                else:
                    link = f' -- "{event}" --> '

                # 2. Dispatch/Mutate (Actions)
                if action_ids:
                    a_node = f"act_{path_id}"
                    action_label = ", ".join(action_ids)
                    lines.append(f'    {a_node}[["{action_label}"]]')
                    lines.append(f'    {curr}{link}{a_node}')
                    curr = a_node
                    link = " --> "

                # 3. Transition
                lines.append(f"    {curr}{link}state_{to}")

        # Styling
        lines.append(
            "    classDef entry fill:#e1f5fe,stroke:#01579b,stroke-width:4px")
        lines.append(
            "    classDef terminal fill:"
            "#eceff1,stroke:#263238,stroke-width:4px")
        return "\n".join(lines)

    # =========================================================================
    # ASCII LOGIC TABLE (The "Audit" View)
    # =========================================================================

    def as_ascii(self) -> str:
        """Generates a clean logic audit table."""
        col_widths = [15, 12, 20, 25, 15]
        headers = ["FROM", "EVENT", "GATE (IF)", "ACTIONS (DO)", "TO"]

        def row(data):
            return "│ " + " │ ".join(
                str(d).ljust(w) for d, w in zip(data, col_widths)
            ) + " │"

        sep = "├" + "─" * (sum(col_widths) + 14) + "┤"

        output = [
            f"L++ Blueprint: {self.name} v{self.version}",
            "═" * (sum(col_widths) + 16),
            row(headers),
            sep.replace("├", "╟").replace("─", "═").replace("┤", "╢")
        ]

        for t in self.transitions:
            actions = ", ".join(t.get("actions", []))
            gates = ", ".join(t.get("gates", []))
            output.append(row([
                t.get("from"),
                t.get("on_event", "ANY"),
                gates if gates else "-",
                actions if actions else "-",
                t.get("to")
            ]))

        output.append(sep.replace("├", "└").replace(
            "─", "─").replace("┤", "┘"))
        return "\n".join(output)

    # =========================================================================
    # GRAPHVIZ DOT
    # =========================================================================

    def as_dot(self) -> str:
        lines = [f'digraph "{self.name}" {{', "    rankdir=LR;",
                 "    node [shape=box, style=rounded];"]

        for s_id in self.sorted_state_ids:
            attr = 'style="filled,rounded", ' \
                'fillcolor="#e1f5fe"' if s_id == self.entry else ""
            if s_id in self.terminal:
                attr = 'shape=doubleoracle'
            lines.append(f'    "{s_id}" [{attr}];')

        for t in self.transitions:
            f, to = t.get("from"), t.get("to")
            label = self._get_transition_label(t)
            sources = self.sorted_state_ids if f == "*" else [f]
            for src in sources:
                lines.append(f'    "{src}" -> "{to}" [label="{label}"];')

        lines.append("}")
        return "\n".join(lines)

# =========================================================================
# CLI ENTRY
# =========================================================================


def main():
    parser = argparse.ArgumentParser(description="L++ Blueprint Visualizer")
    parser.add_argument("file", help="Path to JSON blueprint")
    parser.add_argument(
        "-f", "--format", choices=["ascii", "mermaid", "dot"], default="ascii")
    parser.add_argument("-o", "--output", help="Output file path")

    args = parser.parse_args()

    try:
        with open(args.file, "r") as f:
            bp = json.load(f)

        viz = LppVisualizer(bp)

        if args.format == "ascii":
            result = viz.as_ascii()
        elif args.format == "mermaid":
            result = viz.as_mermaid_logic()
        else:
            result = viz.as_dot()

        if args.output:
            with open(args.output, "w") as f:
                f.write(result)
            print(f"Successfully wrote {args.format} to {args.output}")
        else:
            print(result)

    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
