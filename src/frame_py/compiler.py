"""
L++ Compiler

Compiles JSON blueprints into executable Python operator scripts.
Transforms declarative blueprints into code using the four atomic operations.
"""

import json
# from pathlib import Path
# from typing import Any


def compile_blueprint(blueprint_path: str, output_path: str = None) -> str:
    """
    Compile a JSON blueprint into a Python operator script.

    Args:
        blueprint_path: Path to the JSON blueprint file
        output_path: Optional path to write the compiled script

    Returns:
        The generated Python code as a string
    """
    with open(blueprint_path, "r") as f:
        bp = json.load(f)

    code = _generate_code(bp)

    if output_path:
        with open(output_path, "w") as f:
            f.write(code)

    return code


def compile_blueprint_dict(blueprint: dict) -> str:
    """
    Compile a blueprint dictionary into Python code.

    Args:
        blueprint: The blueprint as a dictionary

    Returns:
        The generated Python code as a string
    """
    return _generate_code(blueprint)


def _generate_code(bp: dict) -> str:
    """Generate Python code from a blueprint dictionary."""
    lines = []

    # Header
    lines.append('"""')
    lines.append(f"L++ Compiled Operator: {bp.get('name', 'Unnamed')}")
    lines.append(f"Version: {bp.get('version', '0.0.0')}")
    if bp.get("description"):
        lines.append(f"Description: {bp['description']}")
    lines.append("")
    lines.append("Auto-generated from JSON blueprint. Do not edit directly.")
    lines.append('"""')
    lines.append("")

    # Imports
    lines.append("from frame_py.lpp_core import (")
    lines.append("    atom_EVALUATE,")
    lines.append("    atom_TRANSITION,")
    lines.append("    atom_MUTATE,")
    lines.append("    atom_DISPATCH,")
    lines.append("    TransitionTrace,")
    lines.append(")")
    lines.append("")
    lines.append("")

    # Constants
    lines.append("# " + "=" * 70)
    lines.append("# BLUEPRINT CONSTANTS")
    lines.append("# " + "=" * 70)
    lines.append("")
    lines.append(f"BLUEPRINT_ID = {repr(bp.get('id', 'unknown'))}")
    lines.append(f"BLUEPRINT_NAME = {repr(bp.get('name', 'Unnamed'))}")
    lines.append(f"BLUEPRINT_VERSION = {repr(bp.get('version', '0.0.0'))}")
    lines.append(f"ENTRY_STATE = {repr(bp.get('entry_state', 'start'))}")
    lines.append(
        f"TERMINAL_STATES = {repr(set(bp.get('terminal_states', [])))}")
    lines.append("")

    # States
    lines.append("STATES = {")
    for state_id, state in bp.get("states", {}).items():
        name = state.get("name", state_id)
        desc = state.get("description", "")
        lines.append(f"    {repr(state_id)}: {repr(name)},  # {desc}")
    lines.append("}")
    lines.append("")

    # Gates as expressions
    lines.append("GATES = {")
    for gate_id, gate in bp.get("gates", {}).items():
        expr = gate.get("expression", "True")
        lines.append(f"    {repr(gate_id)}: {repr(expr)},")
    lines.append("}")
    lines.append("")

    # Actions
    lines.append("ACTIONS = {")
    for action_id, action in bp.get("actions", {}).items():
        lines.append(f"    {repr(action_id)}: {{")
        lines.append(f"        'type': {repr(action.get('type', 'set'))},")
        if action.get("target"):
            lines.append(f"        'target': {repr(action['target'])},")
        if action.get("value") is not None:
            lines.append(f"        'value': {repr(action['value'])},")
        if action.get("value_from"):
            lines.append(
                f"        'value_from': {repr(action['value_from'])},")
        if action.get("compute_unit"):
            lines.append(
                f"        'compute_unit': {repr(action['compute_unit'])},")
        if action.get("input_map"):
            lines.append(f"        'input_map': {repr(action['input_map'])},")
        if action.get("output_map"):
            lines.append(
                f"        'output_map': {repr(action['output_map'])},")
        lines.append("    },")
    lines.append("}")
    lines.append("")

    # Transitions
    lines.append("TRANSITIONS = [")
    for trans in bp.get("transitions", []):
        lines.append("    {")
        lines.append(f"        'id': {repr(trans.get('id', ''))},")
        lines.append(f"        'from': {repr(trans.get('from', '*'))},")
        lines.append(f"        'to': {repr(trans.get('to', ''))},")
        lines.append(f"        'on_event': {repr(trans.get('on_event', ''))},")
        lines.append(f"        'gates': {repr(trans.get('gates', []))},")
        lines.append(f"        'actions': {repr(trans.get('actions', []))},")
        lines.append("    },")
    lines.append("]")
    lines.append("")
    lines.append("")

    # Helper functions
    lines.append("# " + "=" * 70)
    lines.append("# HELPER FUNCTIONS")
    lines.append("# " + "=" * 70)
    lines.append("")
    lines.append("def _resolve_path(path: str, data: dict):")
    lines.append('    """Resolve a dotted path in a dictionary."""')
    lines.append("    parts = path.split('.')")
    lines.append("    obj = data")
    lines.append("    for part in parts:")
    lines.append("        if isinstance(obj, dict):")
    lines.append("            obj = obj.get(part)")
    lines.append("        else:")
    lines.append("            return None")
    lines.append("        if obj is None:")
    lines.append("            return None")
    lines.append("    return obj")
    lines.append("")
    lines.append("")

    # Main operator class
    lines.append("# " + "=" * 70)
    lines.append("# COMPILED OPERATOR")
    lines.append("# " + "=" * 70)
    lines.append("")
    lines.append("class Operator:")
    lines.append('    """')
    lines.append(f"    Compiled L++ Operator: {bp.get('name', 'Unnamed')}")
    lines.append('    """')
    lines.append("")
    lines.append("    def __init__(self, compute_registry: dict = None):")
    lines.append("        self.context = {'_state': ENTRY_STATE}")
    lines.append("        self.traces: list[TransitionTrace] = []")
    lines.append("        self.compute_registry = compute_registry or {}")
    lines.append("")
    lines.append("    @property")
    lines.append("    def state(self) -> str:")
    lines.append("        return self.context.get('_state', ENTRY_STATE)")
    lines.append("")
    lines.append("    @property")
    lines.append("    def is_terminal(self) -> bool:")
    lines.append("        return self.state in TERMINAL_STATES")
    lines.append("")

    # Dispatch method
    lines.append(
        "    def dispatch(self, event_name: str, payload: dict = None):")
    lines.append('        """')
    lines.append("        Dispatch an event to the operator.")
    lines.append("")
    lines.append("        Args:")
    lines.append("            event_name: Name of the event")
    lines.append("            payload: Event payload data")
    lines.append("")
    lines.append("        Returns:")
    lines.append("            Tuple of (success, new_state, error)")
    lines.append('        """')
    lines.append("        payload = payload or {}")
    lines.append("        current = self.state")
    lines.append("")
    lines.append("        # Check terminal")
    lines.append("        if self.is_terminal:")
    lines.append(
        "            return False, current, 'Already in terminal state'")
    lines.append("")
    lines.append("        # Find matching transition")
    lines.append("        trans = None")
    lines.append("        for t in TRANSITIONS:")
    lines.append("            if t['on_event'] != event_name:")
    lines.append("                continue")
    lines.append("            if t['from'] == '*' or t['from'] == current:")
    lines.append("                trans = t")
    lines.append("                break")
    lines.append("")
    lines.append("        if not trans:")
    lines.append(
        "            return False, current, f'No transition for {event_name}'")
    lines.append("")
    lines.append("        # Build evaluation scope")
    lines.append("        scope = dict(self.context)")
    lines.append(
        "        scope['event'] = {'name': event_name, 'payload': payload}")
    lines.append("")
    lines.append("        # EVALUATE: Check gates")
    lines.append("        for gate_id in trans['gates']:")
    lines.append("            expr = GATES.get(gate_id, 'True')")
    lines.append("            if not atom_EVALUATE(expr, scope):")
    lines.append(
        "                return False, current, f'Gate {gate_id} blocked'")
    lines.append("")
    lines.append("        # Execute actions")
    lines.append("        for action_id in trans['actions']:")
    lines.append("            action = ACTIONS.get(action_id)")
    lines.append("            if not action:")
    lines.append("                continue")
    lines.append("")
    lines.append("            if action['type'] == 'set':")
    lines.append("                # MUTATE")
    lines.append("                target = action.get('target')")
    lines.append("                if action.get('value') is not None:")
    lines.append("                    value = action['value']")
    lines.append("                elif action.get('value_from'):")
    lines.append(
        "                    value = _resolve_path("
        "action['value_from'], scope)")
    lines.append("                else:")
    lines.append("                    value = None")
    lines.append(
        "                self.context = atom_MUTATE("
        "self.context, target, value)")
    lines.append("")
    lines.append("            elif action['type'] == 'compute':")
    lines.append("                # DISPATCH")
    lines.append("                unit = action.get('compute_unit', '')")
    lines.append("                parts = unit.split(':')")
    lines.append("                if len(parts) == 2:")
    lines.append("                    sys_id, op_id = parts")
    lines.append("                    inp = {")
    lines.append("                        k: _resolve_path(v, scope)")
    lines.append(
        "                        for k, v in action.get("
        "'input_map', {}).items()")
    lines.append("                    }")
    lines.append("                    result = atom_DISPATCH(")
    lines.append(
        "                        sys_id, op_id, inp, self.compute_registry")
    lines.append("                    )")
    lines.append(
        "                    for ctx_path, res_key in action.get("
        "'output_map', {}).items():")
    lines.append("                        if res_key in result:")
    lines.append("                            self.context = atom_MUTATE(")
    lines.append(
        "                                self.context, ctx_path,"
        " result[res_key]")
    lines.append("                            )")
    lines.append("")
    lines.append("        # TRANSITION")
    lines.append(
        "        new_state, trace = atom_TRANSITION(current, trans['to'])")
    lines.append(
        "        self.context = atom_MUTATE("
        "self.context, '_state', new_state)")
    lines.append("        self.traces.append(trace)")
    lines.append("")
    lines.append("        return True, new_state, None")
    lines.append("")

    # Get context value helper
    lines.append("    def get(self, path: str):")
    lines.append('        """Get a value from context by path."""')
    lines.append("        return _resolve_path(path, self.context)")
    lines.append("")

    # Set context value helper
    lines.append("    def set(self, path: str, value):")
    lines.append('        """Set a value in context by path."""')
    lines.append(
        "        self.context = atom_MUTATE(self.context, path, value)")
    lines.append("")

    # Reset
    lines.append("    def reset(self):")
    lines.append('        """Reset to initial state."""')
    lines.append("        self.context = {'_state': ENTRY_STATE}")
    lines.append("        self.traces = []")
    lines.append("")
    lines.append("")

    # Factory function
    lines.append(
        "def create_operator(compute_registry: dict = None) -> Operator:")
    lines.append(
        '    """Factory function to create a new Operator instance."""')
    lines.append("    return Operator(compute_registry)")
    lines.append("")
    lines.append("")

    # Main block for testing
    bp_name = bp.get("name", "Unnamed")
    lines.append("if __name__ == '__main__':")
    lines.append(f"    print('L++ Compiled Operator: {bp_name}')")
    lines.append("    print('States:', list(STATES.keys()))")
    lines.append("    print('Entry:', ENTRY_STATE)")
    lines.append("    print('Transitions:', len(TRANSITIONS))")
    lines.append("")

    return "\n".join(lines)


# CLI
if __name__ == "__main__":
    import sys

    if len(sys.argv) < 2:
        print(
            "Usage: python -m frame_py.compiler <blueprint.json> [output.py]")
        sys.exit(1)

    bp_path = sys.argv[1]
    out_path = sys.argv[2] if len(sys.argv) > 2 else None

    code = compile_blueprint(bp_path, out_path)

    if out_path:
        print(f"Compiled: {bp_path} -> {out_path}")
    else:
        print(code)
