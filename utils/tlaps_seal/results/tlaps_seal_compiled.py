"""
L++ Compiled Operator: TLAPS Seal Certifier
Version: 1.0.0
Description: Certify L++ blueprints with formal verification - transition from empirical to axiomatic certainty

Auto-generated from JSON blueprint. Do not edit directly.
"""

from frame_py.lpp_core import (
    atom_EVALUATE,
    atom_TRANSITION,
    atom_MUTATE,
    atom_DISPATCH,
    TransitionTrace,
)


# ======================================================================
# BLUEPRINT CONSTANTS
# ======================================================================

BLUEPRINT_ID = 'tlaps_seal'
BLUEPRINT_NAME = 'TLAPS Seal Certifier'
BLUEPRINT_VERSION = '1.0.0'
ENTRY_STATE = 'idle'
TERMINAL_STATES = {'certified', 'rejected'}

STATES = {
    'idle': 'idle',  # Ready to receive blueprint for certification
    'loading': 'loading',  # Loading and parsing blueprint
    'auditing': 'auditing',  # Auditing Trinity and Flange structure
    'generating_tla': 'generating_tla',  # Generating TLA+ specification
    'tlc_verifying': 'tlc_verifying',  # Running TLC model checker (empirical)
    'tlc_verified': 'tlc_verified',  # TLC verification passed
    # Running TLAPS theorem prover (axiomatic)
    'tlaps_proving': 'tlaps_proving',
    'certified': 'certified',  # TLAPS certification complete - Seal granted
    'rejected': 'rejected',  # Blueprint failed verification
    'error': 'error',  # Error during certification process
}

GATES = {
    'hasBlueprint': 'blueprint is not None',
    'hasTlaSpec': 'tlaSpec is not None',
    'trinityValid': "trinityAudit is not None and trinityAudit['valid']",
    'flangeValid': "flangeAudit is not None and flangeAudit['valid']",
    'tlcPassed': "tlcResult is not None and tlcResult['passed']",
    'tlapsPassed': "tlapsResult is not None and tlapsResult['passed']",
    'hasError': 'error is not None',
    'noError': 'error is None',
}

DISPLAY_RULES = [
    {'state': 'idle', 'message': 'Ready - provide blueprint path to certify'},
    {'state': 'certified', 'message': 'TLAPS Seal Granted - Logic Certified'},
    {'state': 'rejected', 'message': 'Certification Failed - See audit report'},
]

ACTIONS = {
    'setPath': {
        'type': 'set',
        'target': 'blueprintPath',
        'value_from': 'event.payload.path',
    },
    'loadBlueprint': {
        'type': 'compute',
        'compute_unit': 'seal:loadBlueprint',
        'input_map': {'blueprintPath': 'blueprintPath'},
        'output_map': {'blueprint': 'blueprint', 'error': 'error'},
    },
    'auditTrinity': {
        'type': 'compute',
        'compute_unit': 'seal:auditTrinity',
        'input_map': {'blueprint': 'blueprint'},
        'output_map': {'trinityAudit': 'trinityAudit', 'error': 'error'},
    },
    'auditFlange': {
        'type': 'compute',
        'compute_unit': 'seal:auditFlange',
        'input_map': {'blueprint': 'blueprint'},
        'output_map': {'flangeAudit': 'flangeAudit', 'error': 'error'},
    },
    'generateTla': {
        'type': 'compute',
        'compute_unit': 'seal:generateTla',
        'input_map': {'blueprint': 'blueprint', 'blueprintPath': 'blueprintPath'},
        'output_map': {'tlaSpec': 'tlaSpec', 'tlaPath': 'tlaPath', 'error': 'error'},
    },
    'runTlc': {
        'type': 'compute',
        'compute_unit': 'seal:runTlc',
        'input_map': {'tlaPath': 'tlaPath'},
        'output_map': {'tlcResult': 'tlcResult', 'sealStatus': 'sealStatus', 'error': 'error'},
    },
    'runTlaps': {
        'type': 'compute',
        'compute_unit': 'seal:runTlaps',
        'input_map': {'tlaPath': 'tlaPath', 'invariants': 'invariants'},
        'output_map': {'tlapsResult': 'tlapsResult', 'sealStatus': 'sealStatus', 'error': 'error'},
    },
    'generateCertificate': {
        'type': 'compute',
        'compute_unit': 'seal:generateCertificate',
        'input_map': {'blueprint': 'blueprint', 'trinityAudit': 'trinityAudit', 'flangeAudit': 'flangeAudit', 'tlcResult': 'tlcResult', 'tlapsResult': 'tlapsResult'},
        'output_map': {'sealCertificate': 'sealCertificate', 'sealStatus': 'sealStatus'},
    },
    'setRejected': {
        'type': 'set',
        'target': 'sealStatus',
        'value': 'rejected',
    },
    'clearError': {
        'type': 'set',
        'target': 'error',
    },
    'resetContext': {
        'type': 'compute',
        'compute_unit': 'seal:resetContext',
        'output_map': {'blueprint': 'blueprint', 'tlaSpec': 'tlaSpec', 'tlcResult': 'tlcResult', 'tlapsResult': 'tlapsResult', 'trinityAudit': 'trinityAudit', 'flangeAudit': 'flangeAudit', 'sealCertificate': 'sealCertificate', 'sealStatus': 'sealStatus', 'error': 'error'},
    },
}

TRANSITIONS = [
    {
        'id': 't1_certify',
        'from': 'idle',
        'to': 'loading',
        'on_event': 'CERTIFY',
        'gates': [],
        'actions': ['setPath'],
    },
    {
        'id': 't2_load',
        'from': 'loading',
        'to': 'auditing',
        'on_event': 'AUTO',
        'gates': ['noError'],
        'actions': ['loadBlueprint'],
    },
    {
        'id': 't3_audit',
        'from': 'auditing',
        'to': 'generating_tla',
        'on_event': 'AUTO',
        'gates': ['hasBlueprint', 'noError'],
        'actions': ['auditTrinity', 'auditFlange'],
    },
    {
        'id': 't4_generate',
        'from': 'generating_tla',
        'to': 'tlc_verifying',
        'on_event': 'AUTO',
        'gates': ['trinityValid', 'flangeValid', 'noError'],
        'actions': ['generateTla'],
    },
    {
        'id': 't5_tlc',
        'from': 'tlc_verifying',
        'to': 'tlc_verified',
        'on_event': 'AUTO',
        'gates': ['hasTlaSpec', 'noError'],
        'actions': ['runTlc'],
    },
    {
        'id': 't6_tlaps_start',
        'from': 'tlc_verified',
        'to': 'tlaps_proving',
        'on_event': 'PROVE',
        'gates': ['tlcPassed'],
        'actions': [],
    },
    {
        'id': 't7_tlaps_complete',
        'from': 'tlaps_proving',
        'to': 'certified',
        'on_event': 'AUTO',
        'gates': ['noError'],
        'actions': ['runTlaps', 'generateCertificate'],
    },
    {
        'id': 't8_quick_seal',
        'from': 'tlc_verified',
        'to': 'certified',
        'on_event': 'SEAL_TLC',
        'gates': ['tlcPassed'],
        'actions': ['generateCertificate'],
    },
    {
        'id': 't9_audit_fail',
        'from': 'auditing',
        'to': 'rejected',
        'on_event': 'AUTO',
        'gates': ['hasError'],
        'actions': ['setRejected'],
    },
    {
        'id': 't10_tlc_fail',
        'from': 'tlc_verifying',
        'to': 'rejected',
        'on_event': 'AUTO',
        'gates': ['hasError'],
        'actions': ['setRejected'],
    },
    {
        'id': 't11_tlaps_fail',
        'from': 'tlaps_proving',
        'to': 'rejected',
        'on_event': 'AUTO',
        'gates': ['hasError'],
        'actions': ['setRejected'],
    },
    {
        'id': 't12_error_any',
        'from': '*',
        'to': 'error',
        'on_event': 'ERROR',
        'gates': ['hasError'],
        'actions': [],
    },
    {
        'id': 't13_reset',
        'from': '*',
        'to': 'idle',
        'on_event': 'RESET',
        'gates': [],
        'actions': ['resetContext'],
    },
    {
        'id': 't14_view_cert',
        'from': 'certified',
        'to': 'certified',
        'on_event': 'VIEW',
        'gates': ['tlapsPassed'],
        'actions': [],
    },
]


# ======================================================================
# HELPER FUNCTIONS
# ======================================================================

def _resolve_path(path: str, data: dict):
    """Resolve a dotted path in a dictionary."""
    parts = path.split('.')
    obj = data
    for part in parts:
        if isinstance(obj, dict):
            obj = obj.get(part)
        else:
            return None
        if obj is None:
            return None
    return obj


# ======================================================================
# COMPILED OPERATOR
# ======================================================================

class Operator:
    """
    Compiled L++ Operator: TLAPS Seal Certifier
    """

    def __init__(self, compute_registry: dict = None):
        self.context = {'_state': ENTRY_STATE, 'blueprintPath': None, 'blueprint': None, 'tlaPath': None, 'tlaSpec': None, 'tlcResult': None,
                        'tlapsResult': None, 'trinityAudit': None, 'flangeAudit': None, 'invariants': None, 'sealStatus': None, 'sealCertificate': None, 'error': None}
        self.traces: list[TransitionTrace] = []
        self.compute_registry = compute_registry or {}

    @property
    def state(self) -> str:
        return self.context.get('_state', ENTRY_STATE)

    @property
    def is_terminal(self) -> bool:
        return self.state in TERMINAL_STATES

    def dispatch(self, event_name: str, payload: dict = None):
        """
        Dispatch an event to the operator.

        Args:
            event_name: Name of the event
            payload: Event payload data

        Returns:
            Tuple of (success, new_state, error)
        """
        payload = payload or {}
        current = self.state

        # Check terminal
        if self.is_terminal:
            return False, current, 'Already in terminal state'

        # Build evaluation scope
        scope = dict(self.context)
        scope['event'] = {'name': event_name, 'payload': payload}

        # Find matching transition (checks gates)
        trans = None
        for t in TRANSITIONS:
            if t['on_event'] != event_name:
                continue
            if t['from'] != '*' and t['from'] != current:
                continue
            # Check gates
            gates_pass = True
            for gate_id in t.get('gates', []):
                expr = GATES.get(gate_id, 'True')
                if not atom_EVALUATE(expr, scope):
                    gates_pass = False
                    break
            if gates_pass:
                trans = t
                break

        if not trans:
            return False, current, f'No transition for {event_name}'

        # Execute actions
        for action_id in trans['actions']:
            action = ACTIONS.get(action_id)
            if not action:
                continue

            if action['type'] == 'set':
                # MUTATE
                target = action.get('target')
                if action.get('value') is not None:
                    value = action['value']
                elif action.get('value_from'):
                    value = _resolve_path(action['value_from'], scope)
                else:
                    value = None
                self.context = atom_MUTATE(self.context, target, value)
                scope.update(self.context)  # Sync scope for chained actions

            elif action['type'] == 'compute':
                # DISPATCH
                unit = action.get('compute_unit', '')
                parts = unit.split(':')
                if len(parts) == 2:
                    sys_id, op_id = parts
                    inp = {
                        k: _resolve_path(v, scope)
                        for k, v in action.get('input_map', {}).items()
                    }
                    result = atom_DISPATCH(
                        sys_id, op_id, inp, self.compute_registry
                    )
                    for ctx_path, res_key in action.get('output_map', {}).items():
                        if res_key in result:
                            self.context = atom_MUTATE(
                                self.context, ctx_path, result[res_key]
                            )
                    # Sync scope for chained actions
                    scope.update(self.context)

        # TRANSITION
        new_state, trace = atom_TRANSITION(current, trans['to'])
        self.context = atom_MUTATE(self.context, '_state', new_state)
        self.traces.append(trace)

        return True, new_state, None

    def get(self, path: str):
        """Get a value from context by path."""
        return _resolve_path(path, self.context)

    def set(self, path: str, value):
        """Set a value in context by path."""
        self.context = atom_MUTATE(self.context, path, value)

    def display(self) -> str:
        """Evaluate display rules and return formatted string."""
        for rule in DISPLAY_RULES:
            gate = rule.get('gate')
            if gate:
                expr = GATES.get(gate, 'False')
                if not atom_EVALUATE(expr, self.context):
                    continue
            # Gate passed or no gate, format template
            template = rule.get('template', '')
            try:
                return template.format(**self.context)
            except (KeyError, ValueError):
                return template
        return ''

    def reset(self):
        """Reset to initial state."""
        self.context = {'_state': ENTRY_STATE, 'blueprintPath': None, 'blueprint': None, 'tlaPath': None, 'tlaSpec': None, 'tlcResult': None,
                        'tlapsResult': None, 'trinityAudit': None, 'flangeAudit': None, 'invariants': None, 'sealStatus': None, 'sealCertificate': None, 'error': None}
        self.traces = []

    def save_state(self, path: str = None):
        """
        Save current state to JSON file.

        Args:
            path: File path (default: ./states/{id}.json)

        Returns:
            Path where state was saved
        """
        import json
        from pathlib import Path

        if not path:
            states_dir = Path('./states')
            states_dir.mkdir(exist_ok=True)
            path = states_dir / f'{BLUEPRINT_ID}.json'
        else:
            path = Path(path)
            path.parent.mkdir(parents=True, exist_ok=True)

        state_data = {
            'blueprint_id': BLUEPRINT_ID,
            'blueprint_version': BLUEPRINT_VERSION,
            'context': self.context,
            'traces': [
                {
                    'timestamp': t.timestamp.isoformat(),
                    'from_id': t.from_id,
                    'to_id': t.to_id,
                }
                for t in self.traces
            ]
        }

        with open(path, 'w') as f:
            json.dump(state_data, f, indent=2)

        return str(path)

    def load_state(self, path: str = None) -> bool:
        """
        Load state from JSON file.

        Args:
            path: File path (default: ./states/{id}.json)

        Returns:
            True if loaded successfully, False otherwise
        """
        import json
        from pathlib import Path
        from datetime import datetime, timezone

        if not path:
            path = Path('./states') / f'{BLUEPRINT_ID}.json'
        else:
            path = Path(path)

        if not path.exists():
            return False

        try:
            with open(path, 'r') as f:
                state_data = json.load(f)

            # Validate blueprint ID matches
            if state_data.get('blueprint_id') != BLUEPRINT_ID:
                print(
                    f'[L++ WARNING] Blueprint ID mismatch: {state_data.get("blueprint_id")}')
                return False

            self.context = state_data.get('context', {})

            # Restore traces
            self.traces = []
            for t in state_data.get('traces', []):
                self.traces.append(TransitionTrace(
                    timestamp=datetime.fromisoformat(
                        t['timestamp']
                    ).replace(tzinfo=timezone.utc),
                    from_id=t['from_id'],
                    to_id=t['to_id'],
                ))

            return True
        except Exception as e:
            print(f'[L++ ERROR] Failed to load state: {e}')
            return False


def create_operator(compute_registry: dict = None) -> Operator:
    """Factory function to create a new Operator instance."""
    return Operator(compute_registry)


if __name__ == '__main__':
    print('L++ Compiled Operator: TLAPS Seal Certifier')
    print('States:', list(STATES.keys()))
    print('Entry:', ENTRY_STATE)
    print('Transitions:', len(TRANSITIONS))
