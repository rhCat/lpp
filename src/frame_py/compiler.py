"""
L++ Compiler

Compiles JSON blueprints into executable Python operator scripts.
Transforms declarative blueprints into code using the four atomic operations.

State Machine (from compiler_blueprint.json):
    idle → loading → validating → generating → writing → generating_tla → complete
             ↓           ↓            ↓           ↓            ↓
           error       error        error       error        error

Transitions:
    COMPILE: idle → loading
    LOAD_DONE: loading → validating
    LOAD_ERROR: loading → error
    VALIDATION_PASSED: validating → generating
    VALIDATION_FAILED: validating → error
    GENERATE_DONE: generating → writing|generating_tla|complete
    GENERATE_ERROR: generating → error
    WRITE_DONE: writing → generating_tla|complete
    WRITE_ERROR: writing → error
    TLA_DONE: generating_tla → complete
    TLA_ERROR: generating_tla → error
    RESET: * → idle
"""

import json
from typing import Optional, Tuple
from enum import Enum

from frame_py.validator import validate_blueprint


class CompilerState(Enum):
    """Compiler state machine states."""
    IDLE = "idle"
    LOADING = "loading"
    VALIDATING = "validating"
    GENERATING = "generating"
    WRITING = "writing"
    GENERATING_TLA = "generating_tla"
    COMPLETE = "complete"
    ERROR = "error"


def compile_blueprint(
    blueprint_path: str,
    output_path: str = None,
    tla_output_dir: str = None
) -> Tuple[Optional[str], Optional[str]]:
    """
    Compile a JSON blueprint into a Python operator script.

    Args:
        blueprint_path: Path to the JSON blueprint file
        output_path: Optional path to write the compiled script
        tla_output_dir: Optional directory to save TLA+ spec

    Returns:
        Tuple of (code, error):
        - code: Generated Python code on success, None on error
        - error: None on success, error message on failure

    State machine: idle → loading → validating → generating → writing → complete | error
    """
    state = CompilerState.IDLE

    # =========================================================================
    # COMPILE: idle → loading
    # =========================================================================
    state = CompilerState.LOADING

    try:
        with open(blueprint_path, "r") as f:
            bp = json.load(f)
    except FileNotFoundError:
        return None, f"LOAD_ERROR: File not found: {blueprint_path}"
    except json.JSONDecodeError as e:
        return None, f"LOAD_ERROR: Invalid JSON: {e}"
    except Exception as e:
        return None, f"LOAD_ERROR: {str(e)}"

    # =========================================================================
    # LOAD_DONE: loading → validating
    # =========================================================================
    state = CompilerState.VALIDATING

    try:
        validate_blueprint(bp)
    except Exception as e:
        return None, f"VALIDATION_FAILED: {str(e)}"

    # =========================================================================
    # VALIDATION_PASSED: validating → generating
    # =========================================================================
    state = CompilerState.GENERATING

    try:
        code = _generate_code(bp)
    except Exception as e:
        return None, f"GENERATE_ERROR: {str(e)}"

    # =========================================================================
    # GENERATE_DONE: generating → writing (if output_path)
    # =========================================================================
    if output_path:
        state = CompilerState.WRITING
        try:
            with open(output_path, "w") as f:
                f.write(code)
        except Exception as e:
            return None, f"WRITE_ERROR: {str(e)}"

    # =========================================================================
    # WRITE_DONE: writing → generating_tla (if tla_output_dir)
    # =========================================================================
    if tla_output_dir:
        state = CompilerState.GENERATING_TLA
        try:
            from frame_py.tla_validator import save_tla
            save_tla(bp, tla_output_dir)
        except Exception as e:
            return None, f"TLA_ERROR: {str(e)}"

    # =========================================================================
    # TLA_DONE / WRITE_DONE / GENERATE_DONE: → complete
    # =========================================================================
    state = CompilerState.COMPLETE

    return code, None


def compile_blueprint_dict(
    blueprint: dict,
    tla_output_dir: str = None
) -> Tuple[Optional[str], Optional[str]]:
    """
    Compile a blueprint dictionary into Python code.

    Args:
        blueprint: The blueprint as a dictionary
        tla_output_dir: Optional directory to save TLA+ spec

    Returns:
        Tuple of (code, error):
        - code: Generated Python code on success, None on error
        - error: None on success, error message on failure
    """
    state = CompilerState.VALIDATING

    try:
        validate_blueprint(blueprint)
    except Exception as e:
        return None, f"VALIDATION_FAILED: {str(e)}"

    state = CompilerState.GENERATING

    try:
        code = _generate_code(blueprint)
    except Exception as e:
        return None, f"GENERATE_ERROR: {str(e)}"

    if tla_output_dir:
        state = CompilerState.GENERATING_TLA
        try:
            from frame_py.tla_validator import save_tla
            save_tla(blueprint, tla_output_dir)
        except Exception as e:
            return None, f"TLA_ERROR: {str(e)}"

    state = CompilerState.COMPLETE
    return code, None


def _generate_code(bp: dict) -> str:
    """Generate Python code from a blueprint dictionary."""
    # Validate first
    validate_blueprint(bp)

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

    # Display rules
    display_rules = bp.get("display", {}).get("rules", [])
    lines.append("DISPLAY_RULES = [")
    for rule in display_rules:
        lines.append(f"    {repr(rule)},")
    lines.append("]")
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

    # Build initial context from context_schema
    context_schema = bp.get("context_schema", {})
    properties = context_schema.get("properties", {})
    init_ctx = {"_state": "ENTRY_STATE"}  # placeholder
    for prop in properties.keys():
        init_ctx[prop] = None

    # Generate context initialization
    ctx_items = ["'_state': ENTRY_STATE"]
    for prop in properties.keys():
        ctx_items.append(f"{repr(prop)}: None")
    ctx_init = "{" + ", ".join(ctx_items) + "}"

    lines.append("class Operator:")
    lines.append('    """')
    lines.append(f"    Compiled L++ Operator: {bp.get('name', 'Unnamed')}")
    lines.append('    """')
    lines.append("")
    lines.append("    def __init__(self, compute_registry: dict = None):")
    lines.append(f"        self.context = {ctx_init}")
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
    lines.append("        # Build evaluation scope")
    lines.append("        scope = dict(self.context)")
    lines.append(
        "        scope['event'] = {'name': event_name, 'payload': payload}")
    lines.append("")
    lines.append("        # Find matching transition (checks gates)")
    lines.append("        trans = None")
    lines.append("        for t in TRANSITIONS:")
    lines.append("            if t['on_event'] != event_name:")
    lines.append("                continue")
    lines.append("            if t['from'] != '*' and t['from'] != current:")
    lines.append("                continue")
    lines.append("            # Check gates")
    lines.append("            gates_pass = True")
    lines.append("            for gate_id in t.get('gates', []):")
    lines.append("                expr = GATES.get(gate_id, 'True')")
    lines.append("                if not atom_EVALUATE(expr, scope):")
    lines.append("                    gates_pass = False")
    lines.append("                    break")
    lines.append("            if gates_pass:")
    lines.append("                trans = t")
    lines.append("                break")
    lines.append("")
    lines.append("        if not trans:")
    lines.append(
        "            return False, current, f'No transition for {event_name}'")
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
    lines.append(
        "                scope.update(self.context)  "
        "# Sync scope for chained actions")
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
    lines.append(
        "                    scope.update(self.context)  "
        "# Sync scope for chained actions")
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

    # Display method - evaluate display rules from blueprint
    lines.append("    def display(self) -> str:")
    lines.append(
        '        """Evaluate display rules and return formatted string."""')
    lines.append("        for rule in DISPLAY_RULES:")
    lines.append("            gate = rule.get('gate')")
    lines.append("            if gate:")
    lines.append("                expr = GATES.get(gate, 'False')")
    lines.append("                if not atom_EVALUATE(expr, self.context):")
    lines.append("                    continue")
    lines.append("            # Gate passed or no gate, format template")
    lines.append("            template = rule.get('template', '')")
    lines.append("            try:")
    lines.append("                return template.format(**self.context)")
    lines.append("            except (KeyError, ValueError):")
    lines.append("                return template")
    lines.append("        return ''")
    lines.append("")

    # Reset
    lines.append("    def reset(self):")
    lines.append('        """Reset to initial state."""')
    lines.append(f"        self.context = {ctx_init}")
    lines.append("        self.traces = []")
    lines.append("")

    # Save state
    lines.append("    def save_state(self, path: str = None):")
    lines.append('        """')
    lines.append("        Save current state to JSON file.")
    lines.append("")
    lines.append("        Args:")
    lines.append("            path: File path (default: ./states/{id}.json)")
    lines.append("")
    lines.append("        Returns:")
    lines.append("            Path where state was saved")
    lines.append('        """')
    lines.append("        import json")
    lines.append("        from pathlib import Path")
    lines.append("")
    lines.append("        if not path:")
    lines.append(
        "            states_dir = Path('./states')")
    lines.append("            states_dir.mkdir(exist_ok=True)")
    lines.append("            path = states_dir / f'{BLUEPRINT_ID}.json'")
    lines.append("        else:")
    lines.append("            path = Path(path)")
    lines.append("            path.parent.mkdir(parents=True, exist_ok=True)")
    lines.append("")
    lines.append("        state_data = {")
    lines.append("            'blueprint_id': BLUEPRINT_ID,")
    lines.append("            'blueprint_version': BLUEPRINT_VERSION,")
    lines.append("            'context': self.context,")
    lines.append("            'traces': [")
    lines.append("                {")
    lines.append("                    'timestamp': t.timestamp.isoformat(),")
    lines.append("                    'from_id': t.from_id,")
    lines.append("                    'to_id': t.to_id,")
    lines.append("                }")
    lines.append("                for t in self.traces")
    lines.append("            ]")
    lines.append("        }")
    lines.append("")
    lines.append("        with open(path, 'w') as f:")
    lines.append("            json.dump(state_data, f, indent=2)")
    lines.append("")
    lines.append("        return str(path)")
    lines.append("")

    # Load state
    lines.append("    def load_state(self, path: str = None) -> bool:")
    lines.append('        """')
    lines.append("        Load state from JSON file.")
    lines.append("")
    lines.append("        Args:")
    lines.append("            path: File path (default: ./states/{id}.json)")
    lines.append("")
    lines.append("        Returns:")
    lines.append("            True if loaded successfully, False otherwise")
    lines.append('        """')
    lines.append("        import json")
    lines.append("        from pathlib import Path")
    lines.append("        from datetime import datetime, timezone")
    lines.append("")
    lines.append("        if not path:")
    lines.append(
        "            path = Path('./states') / f'{BLUEPRINT_ID}.json'")
    lines.append("        else:")
    lines.append("            path = Path(path)")
    lines.append("")
    lines.append("        if not path.exists():")
    lines.append("            return False")
    lines.append("")
    lines.append("        try:")
    lines.append("            with open(path, 'r') as f:")
    lines.append("                state_data = json.load(f)")
    lines.append("")
    lines.append("            # Validate blueprint ID matches")
    lines.append(
        "            if state_data.get('blueprint_id') != BLUEPRINT_ID:")
    lines.append(
        "                print(f'[L++ WARNING] "
        "Blueprint ID mismatch: {state_data.get(\"blueprint_id\")}')")
    lines.append("                return False")
    lines.append("")
    lines.append("            self.context = state_data.get('context', {})")
    lines.append("")
    lines.append("            # Restore traces")
    lines.append("            self.traces = []")
    lines.append("            for t in state_data.get('traces', []):")
    lines.append("                self.traces.append(TransitionTrace(")
    lines.append("                    timestamp=datetime.fromisoformat(")
    lines.append("                        t['timestamp']")
    lines.append("                    ).replace(tzinfo=timezone.utc),")
    lines.append("                    from_id=t['from_id'],")
    lines.append("                    to_id=t['to_id'],")
    lines.append("                ))")
    lines.append("")
    lines.append("            return True")
    lines.append("        except Exception as e:")
    lines.append(
        "            print(f'[L++ ERROR] Failed to load state: {e}')")
    lines.append("            return False")
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

    code, error = compile_blueprint(bp_path, out_path)

    if error:
        print(f"[L++ COMPILE ERROR] {error}")
        sys.exit(1)

    if out_path:
        print(f"Compiled: {bp_path} -> {out_path}")
    else:
        print(code)
