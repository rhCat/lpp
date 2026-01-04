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

    def _get_gate_expression(self, gate_id: str) -> str:
        """Get the actual gate expression for display."""
        gate = self.gates.get(gate_id, {})
        if isinstance(gate, dict):
            expr = gate.get("expression", gate.get("condition", ""))
            if expr:
                # Truncate long expressions
                if len(expr) > 30:
                    return expr[:27] + "..."
                return expr
        return gate_id

    def _classify_transition(self, t: Dict) -> str:
        """Classify transition type for styling."""
        to_state = t.get("to", "")
        event = t.get("on_event", "").upper()

        if to_state == "error" or "ERROR" in event:
            return "error"
        if to_state == "idle" or "RESET" in event:
            return "reset"
        if to_state in self.terminal:
            return "terminal"
        return "normal"

    def _group_states_by_phase(self) -> Dict[str, List[str]]:
        """Group states into workflow phases based on naming patterns."""
        phases = {
            "init": [],
            "validate": [],
            "process": [],
            "complete": [],
            "error": []
        }

        for s_id in self.sorted_state_ids:
            s_lower = s_id.lower()
            if s_id == self.entry or "init" in s_lower or "start" in s_lower:
                phases["init"].append(s_id)
            elif "valid" in s_lower or "check" in s_lower or "verify" in s_lower:
                phases["validate"].append(s_id)
            elif "error" in s_lower or "fail" in s_lower:
                phases["error"].append(s_id)
            elif s_id in self.terminal or "complete" in s_lower or "done" in s_lower:
                phases["complete"].append(s_id)
            else:
                phases["process"].append(s_id)

        # Remove empty phases
        return {k: v for k, v in phases.items() if v}

    def as_mermaid_logic(self) -> str:
        """
        Generates a Logic-First flowchart with
        Diamonds (Gates) and Rects (Actions).
        Enhanced with gate expressions and transition styling.
        """
        lines = ["flowchart TD", f"    %% L++ Logic CAD: {self.name}"]

        # Group states into phases
        phases = self._group_states_by_phase()

        # Define States with subgraph grouping
        phase_labels = {
            "init": "Initialization",
            "validate": "Validation",
            "process": "Processing",
            "complete": "Completion",
            "error": "Error Handling"
        }

        for phase, state_ids in phases.items():
            if len(state_ids) > 1 and phase != "error":
                lines.append(f"    subgraph {phase_labels.get(phase, phase)}")

            for s_id in state_ids:
                state_info = self.states.get(s_id, {})
                desc = state_info.get("description", "") if isinstance(state_info, dict) else ""
                # Escape quotes and truncate description
                if desc:
                    desc = desc.replace('"', "'")[:40]
                    label = f"{s_id}<br>{desc}"
                else:
                    label = s_id

                # Different shapes for different state types - ALL have explicit fill
                if s_id == self.entry:
                    shape = f'state_{s_id}(["{label}"]):::entry'
                elif s_id in self.terminal:
                    shape = f'state_{s_id}[["{label}"]]:::terminal'
                elif "error" in s_id.lower():
                    shape = f'state_{s_id}[["{label}"]]:::errorState'
                else:
                    shape = f'state_{s_id}(["{label}"]):::state'
                lines.append(f"        {shape}")

            if len(state_ids) > 1 and phase != "error":
                lines.append("    end")

        lines.append("")
        lines.append("    %% Transitions")

        # Track which transitions to skip (wildcards expanded)
        seen_transitions = set()

        # Define Transitions with enhanced gate display
        for i, t in enumerate(self.transitions):
            f, to = t.get("from"), t.get("to")
            event = t.get("on_event", "ANY")
            gate_ids = t.get("gates", [])
            action_ids = t.get("actions", [])
            trans_type = self._classify_transition(t)

            # Skip invalid targets
            if to not in self.states:
                continue

            # Handle wildcard source
            if f == "*":
                sources = [s for s in self.sorted_state_ids
                           if s != to and s not in self.terminal]
            elif f in self.states:
                sources = [f]
            else:
                continue

            for s_idx, src in enumerate(sources):
                # Deduplicate transitions
                trans_key = f"{src}->{to}:{event}"
                if trans_key in seen_transitions:
                    continue
                seen_transitions.add(trans_key)

                path_id = f"t{i}s{s_idx}"
                curr = f"state_{src}"

                # Build link style based on transition type
                if trans_type == "error":
                    link_style = "stroke:#ff6b6b,stroke-width:2px"
                    arrow_class = ":::errorLink"
                elif trans_type == "reset":
                    link_style = "stroke:#ffaa00,stroke-dasharray:5"
                    arrow_class = ":::resetLink"
                else:
                    link_style = ""
                    arrow_class = ""

                # 1. Evaluate (Gate) - Show actual expression
                if gate_ids:
                    g_node = f"gate_{path_id}"
                    # Get actual gate expressions
                    gate_exprs = [self._get_gate_expression(g) for g in gate_ids]
                    gate_label = " && ".join(gate_exprs)
                    # Escape for mermaid
                    gate_label = gate_label.replace('"', "'")
                    lines.append(f'    {g_node}{{{{"{gate_label}?"}}}}:::gate')
                    lines.append(f'    {curr} -- "{event}" --> {g_node}')
                    curr = g_node
                    link = " -- ✓ --> "
                else:
                    link = f' -- "{event}" --> '

                # 2. Dispatch/Mutate (Actions)
                if action_ids:
                    a_node = f"act_{path_id}"
                    action_label = ", ".join(action_ids[:3])  # Limit display
                    if len(action_ids) > 3:
                        action_label += f" +{len(action_ids)-3}"
                    lines.append(f'    {a_node}[["{action_label}"]]:::action')
                    lines.append(f'    {curr}{link}{a_node}')
                    curr = a_node
                    link = " --> "

                # 3. Transition to target
                lines.append(f"    {curr}{link}state_{to}")

        lines.append("")
        lines.append("    %% Styling - ALL shapes have explicit fill and black text")
        # State styles - all with color:#000 for black text
        lines.append("    classDef entry fill:#e1f5fe,stroke:#01579b,stroke-width:3px,color:#000")
        lines.append("    classDef terminal fill:#c8e6c9,stroke:#2e7d32,stroke-width:3px,color:#000")
        lines.append("    classDef errorState fill:#ffcdd2,stroke:#c62828,stroke-width:2px,color:#000")
        lines.append("    classDef state fill:#ffffff,stroke:#6a6aaa,stroke-width:2px,color:#000")
        # Gate and action styles
        lines.append("    classDef gate fill:#fff3e0,stroke:#e65100,stroke-width:2px,color:#000")
        lines.append("    classDef action fill:#e3f2fd,stroke:#1565c0,stroke-width:1px,color:#000")

        return "\n".join(lines)

    def as_mermaid_simple(self) -> str:
        """
        Generates a simplified state diagram without intermediate nodes.
        Good for high-level overview.
        """
        lines = ["stateDiagram-v2", f"    %% L++ State Diagram: {self.name}"]

        # Entry point
        if self.entry:
            lines.append(f"    [*] --> {self.entry}")

        # Transitions with gate conditions as notes
        for t in self.transitions:
            f, to = t.get("from"), t.get("to")
            event = t.get("on_event", "")
            gate_ids = t.get("gates", [])

            if to not in self.states:
                continue

            sources = [s for s in self.sorted_state_ids if s != to] if f == "*" else [f]

            for src in sources:
                if src not in self.states:
                    continue

                label = event
                if gate_ids:
                    gate_exprs = [self._get_gate_expression(g) for g in gate_ids]
                    label += f" [{' && '.join(gate_exprs)}]"

                lines.append(f"    {src} --> {to} : {label}")

        # Terminal states
        for term in self.terminal:
            if term in self.states:
                lines.append(f"    {term} --> [*]")

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
        "-f", "--format",
        choices=["ascii", "mermaid", "mermaid-simple", "dot"],
        default="ascii")
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
        elif args.format == "mermaid-simple":
            result = viz.as_mermaid_simple()
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
