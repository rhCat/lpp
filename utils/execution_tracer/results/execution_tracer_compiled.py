"""
L++ Compiled Operator: L++ Execution Tracer
Version: 1.0.0
Description: Structured logging and tracing for L++ blueprint execution with OpenTelemetry support

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

BLUEPRINT_ID = 'lpp_execution_tracer'
BLUEPRINT_NAME = 'L++ Execution Tracer'
BLUEPRINT_VERSION = '1.0.0'
ENTRY_STATE = 'idle'
TERMINAL_STATES = set()

STATES = {
    'idle': 'idle',  # No trace active, ready to initialize
    'configured': 'configured',  # Tracer configured, ready to start trace
    'tracing': 'tracing',  # Actively recording trace events
    'paused': 'paused',  # Tracing paused, can resume
    'completed': 'completed',  # Trace completed, ready for export/analysis
    'analyzing': 'analyzing',  # Analyzing trace data
    'exporting': 'exporting',  # Exporting trace data
    'error': 'error',  # Error state
}

GATES = {
    'has_config': 'config is not None',
    'no_config': 'config is None',
    'has_trace': 'trace_id is not None',
    'no_trace': 'trace_id is None',
    'has_spans': 'spans is not None and len(spans) > 0',
    'has_active_spans': 'active_spans is not None and len(active_spans) > 0',
    'has_events': 'events is not None and len(events) > 0',
    'has_analysis': 'analysis_result is not None',
    'is_idle': "_state == 'idle'",
    'is_configured': "_state == 'configured'",
    'is_tracing': "_state == 'tracing'",
    'is_paused': "_state == 'paused'",
    'is_completed': "_state == 'completed'",
    'is_analyzing': "_state == 'analyzing'",
    'is_exporting': "_state == 'exporting'",
    'is_error': "_state == 'error'",
}

DISPLAY_RULES = [
    {'gate': 'is_error', 'template': 'ERROR: {error}'},
    {'gate': 'is_idle', 'template': '[IDLE] No tracer configured'},
    {'gate': 'is_configured', 'template': '[READY] Tracer configured, format: {output_format}'},
    {'gate': 'is_tracing', 'template': '[TRACING] {blueprint_name} - {trace_id}'},
    {'gate': 'is_paused', 'template': '[PAUSED] {blueprint_name} - {trace_id}'},
    {'gate': 'is_completed', 'template': '[DONE] {blueprint_name} - {trace_id}'},
    {'gate': 'is_analyzing', 'template': '[ANALYZING] {trace_id}'},
    {'gate': 'is_exporting', 'template': '[EXPORTING] {trace_id}'},
    {'template': 'L++ Execution Tracer'},
]

ACTIONS = {
    'init_tracer': {
        'type': 'compute',
        'compute_unit': 'tracer:init_tracer',
        'input_map': {'output_format': 'event.payload.output_format', 'include_context': 'event.payload.include_context', 'include_timing': 'event.payload.include_timing', 'max_spans': 'event.payload.max_spans'},
        'output_map': {'config': 'config', 'output_format': 'output_format', 'output': 'output'},
    },
    'start_trace': {
        'type': 'compute',
        'compute_unit': 'tracer:start_trace',
        'input_map': {'config': 'config', 'blueprint_id': 'event.payload.blueprint_id', 'blueprint_name': 'event.payload.blueprint_name', 'metadata': 'event.payload.metadata'},
        'output_map': {'trace_id': 'trace_id', 'root_span_id': 'root_span_id', 'spans': 'spans', 'active_spans': 'active_spans', 'events': 'events', 'blueprint_id': 'blueprint_id', 'blueprint_name': 'blueprint_name', 'start_time': 'start_time', 'output': 'output'},
    },
    'end_trace': {
        'type': 'compute',
        'compute_unit': 'tracer:end_trace',
        'input_map': {'trace_id': 'trace_id', 'root_span_id': 'root_span_id', 'spans': 'spans', 'active_spans': 'active_spans', 'start_time': 'start_time'},
        'output_map': {'spans': 'spans', 'active_spans': 'active_spans', 'end_time': 'end_time', 'output': 'output'},
    },
    'record_span': {
        'type': 'compute',
        'compute_unit': 'tracer:record_span',
        'input_map': {'trace_id': 'trace_id', 'spans': 'spans', 'span_type': 'event.payload.span_type', 'name': 'event.payload.name', 'parent_span_id': 'event.payload.parent_span_id', 'attributes': 'event.payload.attributes', 'start_time': 'event.payload.start_time', 'end_time': 'event.payload.end_time', 'duration_ms': 'event.payload.duration_ms'},
        'output_map': {'spans': 'spans', 'output': 'output'},
    },
    'start_span': {
        'type': 'compute',
        'compute_unit': 'tracer:start_span',
        'input_map': {'trace_id': 'trace_id', 'spans': 'spans', 'active_spans': 'active_spans', 'span_type': 'event.payload.span_type', 'name': 'event.payload.name', 'parent_span_id': 'event.payload.parent_span_id', 'attributes': 'event.payload.attributes'},
        'output_map': {'spans': 'spans', 'active_spans': 'active_spans', 'output': 'output'},
    },
    'end_span': {
        'type': 'compute',
        'compute_unit': 'tracer:end_span',
        'input_map': {'span_id': 'event.payload.span_id', 'spans': 'spans', 'active_spans': 'active_spans', 'attributes': 'event.payload.attributes', 'status': 'event.payload.status'},
        'output_map': {'spans': 'spans', 'active_spans': 'active_spans', 'output': 'output'},
    },
    'record_state_change': {
        'type': 'compute',
        'compute_unit': 'tracer:record_state_change',
        'input_map': {'trace_id': 'trace_id', 'spans': 'spans', 'events': 'events', 'active_spans': 'active_spans', 'from_state': 'event.payload.from_state', 'to_state': 'event.payload.to_state', 'transition_id': 'event.payload.transition_id', 'trigger_event': 'event.payload.trigger_event'},
        'output_map': {'spans': 'spans', 'events': 'events', 'output': 'output'},
    },
    'record_gate_eval': {
        'type': 'compute',
        'compute_unit': 'tracer:record_gate_eval',
        'input_map': {'trace_id': 'trace_id', 'spans': 'spans', 'events': 'events', 'active_spans': 'active_spans', 'gate_id': 'event.payload.gate_id', 'expression': 'event.payload.expression', 'result': 'event.payload.result', 'input_values': 'event.payload.input_values'},
        'output_map': {'spans': 'spans', 'events': 'events', 'output': 'output'},
    },
    'record_action': {
        'type': 'compute',
        'compute_unit': 'tracer:record_action',
        'input_map': {'trace_id': 'trace_id', 'spans': 'spans', 'events': 'events', 'active_spans': 'active_spans', 'action_id': 'event.payload.action_id', 'action_type': 'event.payload.action_type', 'input_map': 'event.payload.input_map', 'output_map': 'event.payload.output_map', 'duration_ms': 'event.payload.duration_ms'},
        'output_map': {'spans': 'spans', 'events': 'events', 'output': 'output'},
    },
    'record_event': {
        'type': 'compute',
        'compute_unit': 'tracer:record_event',
        'input_map': {'trace_id': 'trace_id', 'events': 'events', 'active_spans': 'active_spans', 'event_name': 'event.payload.event_name', 'event_payload': 'event.payload.event_payload'},
        'output_map': {'events': 'events', 'output': 'output'},
    },
    'record_context_change': {
        'type': 'compute',
        'compute_unit': 'tracer:record_context_change',
        'input_map': {'trace_id': 'trace_id', 'events': 'events', 'active_spans': 'active_spans', 'key': 'event.payload.key', 'old_value': 'event.payload.old_value', 'new_value': 'event.payload.new_value'},
        'output_map': {'events': 'events', 'output': 'output'},
    },
    'format_otlp': {
        'type': 'compute',
        'compute_unit': 'tracer:format_otlp',
        'input_map': {'trace_id': 'trace_id', 'spans': 'spans', 'events': 'events', 'blueprint_id': 'blueprint_id', 'blueprint_name': 'blueprint_name', 'start_time': 'start_time', 'end_time': 'end_time'},
        'output_map': {'formatted_output': 'formatted_output', 'output': 'output'},
    },
    'format_jsonl': {
        'type': 'compute',
        'compute_unit': 'tracer:format_jsonl',
        'input_map': {'trace_id': 'trace_id', 'spans': 'spans', 'events': 'events'},
        'output_map': {'formatted_output': 'formatted_output', 'output': 'output'},
    },
    'format_human': {
        'type': 'compute',
        'compute_unit': 'tracer:format_human',
        'input_map': {'trace_id': 'trace_id', 'spans': 'spans', 'events': 'events', 'blueprint_name': 'blueprint_name', 'start_time': 'start_time', 'end_time': 'end_time'},
        'output_map': {'formatted_output': 'formatted_output', 'output': 'output'},
    },
    'format_timeline': {
        'type': 'compute',
        'compute_unit': 'tracer:format_timeline',
        'input_map': {'trace_id': 'trace_id', 'spans': 'spans', 'events': 'events', 'blueprint_name': 'blueprint_name', 'start_time': 'start_time', 'end_time': 'end_time'},
        'output_map': {'formatted_output': 'formatted_output', 'output': 'output'},
    },
    'export_trace': {
        'type': 'compute',
        'compute_unit': 'tracer:export_trace',
        'input_map': {'formatted_output': 'formatted_output', 'output_format': 'output_format', 'path': 'event.payload.path', 'trace_id': 'trace_id', 'spans': 'spans', 'events': 'events', 'blueprint_id': 'blueprint_id', 'blueprint_name': 'blueprint_name', 'start_time': 'start_time', 'end_time': 'end_time'},
        'output_map': {'export_path': 'export_path', 'output': 'output'},
    },
    'analyze_trace': {
        'type': 'compute',
        'compute_unit': 'tracer:analyze_trace',
        'input_map': {'trace_id': 'trace_id', 'spans': 'spans', 'events': 'events', 'start_time': 'start_time', 'end_time': 'end_time'},
        'output_map': {'analysis_result': 'analysis_result', 'output': 'output'},
    },
    'render_status': {
        'type': 'compute',
        'compute_unit': 'tracer:render_status',
        'input_map': {'trace_id': 'trace_id', 'blueprint_name': 'blueprint_name', 'spans': 'spans', 'events': 'events', 'active_spans': 'active_spans', 'start_time': 'start_time', 'output_format': 'output_format'},
        'output_map': {'output': 'output'},
    },
    'clear_trace': {
        'type': 'compute',
        'compute_unit': 'tracer:clear_trace',
        'output_map': {'trace_id': 'trace_id', 'root_span_id': 'root_span_id', 'spans': 'spans', 'active_spans': 'active_spans', 'events': 'events', 'start_time': 'start_time', 'end_time': 'end_time', 'analysis_result': 'analysis_result', 'formatted_output': 'formatted_output', 'output': 'output'},
    },
    'set_format': {
        'type': 'set',
        'target': 'output_format',
        'value_from': 'event.payload.format',
    },
    'set_error': {
        'type': 'set',
        'target': 'error',
        'value_from': 'event.payload.message',
    },
    'clear_error': {
        'type': 'set',
        'target': 'error',
    },
}

TRANSITIONS = [
    {
        'id': 't_init',
        'from': 'idle',
        'to': 'configured',
        'on_event': 'INIT',
        'gates': [],
        'actions': ['init_tracer'],
    },
    {
        'id': 't_init_error',
        'from': 'idle',
        'to': 'error',
        'on_event': 'INIT_FAILED',
        'gates': [],
        'actions': ['set_error'],
    },
    {
        'id': 't_reconfigure',
        'from': 'configured',
        'to': 'configured',
        'on_event': 'INIT',
        'gates': [],
        'actions': ['init_tracer'],
    },
    {
        'id': 't_start_trace',
        'from': 'configured',
        'to': 'tracing',
        'on_event': 'START_TRACE',
        'gates': ['has_config'],
        'actions': ['start_trace'],
    },
    {
        'id': 't_start_trace_idle',
        'from': 'idle',
        'to': 'tracing',
        'on_event': 'START_TRACE',
        'gates': [],
        'actions': ['init_tracer', 'start_trace'],
    },
    {
        'id': 't_record_span',
        'from': 'tracing',
        'to': 'tracing',
        'on_event': 'RECORD_SPAN',
        'gates': ['has_trace'],
        'actions': ['record_span'],
    },
    {
        'id': 't_start_span',
        'from': 'tracing',
        'to': 'tracing',
        'on_event': 'START_SPAN',
        'gates': ['has_trace'],
        'actions': ['start_span'],
    },
    {
        'id': 't_end_span',
        'from': 'tracing',
        'to': 'tracing',
        'on_event': 'END_SPAN',
        'gates': ['has_trace'],
        'actions': ['end_span'],
    },
    {
        'id': 't_record_state',
        'from': 'tracing',
        'to': 'tracing',
        'on_event': 'STATE_CHANGE',
        'gates': ['has_trace'],
        'actions': ['record_state_change'],
    },
    {
        'id': 't_record_gate',
        'from': 'tracing',
        'to': 'tracing',
        'on_event': 'GATE_EVAL',
        'gates': ['has_trace'],
        'actions': ['record_gate_eval'],
    },
    {
        'id': 't_record_action',
        'from': 'tracing',
        'to': 'tracing',
        'on_event': 'ACTION',
        'gates': ['has_trace'],
        'actions': ['record_action'],
    },
    {
        'id': 't_record_event',
        'from': 'tracing',
        'to': 'tracing',
        'on_event': 'EVENT',
        'gates': ['has_trace'],
        'actions': ['record_event'],
    },
    {
        'id': 't_record_context',
        'from': 'tracing',
        'to': 'tracing',
        'on_event': 'CONTEXT_CHANGE',
        'gates': ['has_trace'],
        'actions': ['record_context_change'],
    },
    {
        'id': 't_pause_trace',
        'from': 'tracing',
        'to': 'paused',
        'on_event': 'PAUSE',
        'gates': [],
        'actions': [],
    },
    {
        'id': 't_resume_trace',
        'from': 'paused',
        'to': 'tracing',
        'on_event': 'RESUME',
        'gates': [],
        'actions': [],
    },
    {
        'id': 't_end_trace',
        'from': 'tracing',
        'to': 'completed',
        'on_event': 'END_TRACE',
        'gates': ['has_trace'],
        'actions': ['end_trace'],
    },
    {
        'id': 't_end_trace_paused',
        'from': 'paused',
        'to': 'completed',
        'on_event': 'END_TRACE',
        'gates': ['has_trace'],
        'actions': ['end_trace'],
    },
    {
        'id': 't_format_otlp',
        'from': 'completed',
        'to': 'completed',
        'on_event': 'FORMAT_OTLP',
        'gates': ['has_spans'],
        'actions': ['format_otlp'],
    },
    {
        'id': 't_format_jsonl',
        'from': 'completed',
        'to': 'completed',
        'on_event': 'FORMAT_JSONL',
        'gates': ['has_spans'],
        'actions': ['format_jsonl'],
    },
    {
        'id': 't_format_human',
        'from': 'completed',
        'to': 'completed',
        'on_event': 'FORMAT_HUMAN',
        'gates': ['has_spans'],
        'actions': ['format_human'],
    },
    {
        'id': 't_format_timeline',
        'from': 'completed',
        'to': 'completed',
        'on_event': 'FORMAT_TIMELINE',
        'gates': ['has_spans'],
        'actions': ['format_timeline'],
    },
    {
        'id': 't_export',
        'from': 'completed',
        'to': 'completed',
        'on_event': 'EXPORT',
        'gates': [],
        'actions': ['export_trace'],
    },
    {
        'id': 't_analyze',
        'from': 'completed',
        'to': 'completed',
        'on_event': 'ANALYZE',
        'gates': ['has_spans'],
        'actions': ['analyze_trace'],
    },
    {
        'id': 't_status_tracing',
        'from': 'tracing',
        'to': 'tracing',
        'on_event': 'STATUS',
        'gates': [],
        'actions': ['render_status'],
    },
    {
        'id': 't_status_paused',
        'from': 'paused',
        'to': 'paused',
        'on_event': 'STATUS',
        'gates': [],
        'actions': ['render_status'],
    },
    {
        'id': 't_status_completed',
        'from': 'completed',
        'to': 'completed',
        'on_event': 'STATUS',
        'gates': [],
        'actions': ['render_status'],
    },
    {
        'id': 't_set_format_conf',
        'from': 'configured',
        'to': 'configured',
        'on_event': 'SET_FORMAT',
        'gates': [],
        'actions': ['set_format'],
    },
    {
        'id': 't_set_format_completed',
        'from': 'completed',
        'to': 'completed',
        'on_event': 'SET_FORMAT',
        'gates': [],
        'actions': ['set_format'],
    },
    {
        'id': 't_clear_completed',
        'from': 'completed',
        'to': 'configured',
        'on_event': 'CLEAR',
        'gates': [],
        'actions': ['clear_trace'],
    },
    {
        'id': 't_new_trace',
        'from': 'completed',
        'to': 'tracing',
        'on_event': 'START_TRACE',
        'gates': ['has_config'],
        'actions': ['clear_trace', 'start_trace'],
    },
    {
        'id': 't_reset',
        'from': 'configured',
        'to': 'idle',
        'on_event': 'RESET',
        'gates': [],
        'actions': ['clear_trace'],
    },
    {
        'id': 't_reset_tracing',
        'from': 'tracing',
        'to': 'idle',
        'on_event': 'RESET',
        'gates': [],
        'actions': ['clear_trace'],
    },
    {
        'id': 't_reset_completed',
        'from': 'completed',
        'to': 'idle',
        'on_event': 'RESET',
        'gates': [],
        'actions': ['clear_trace'],
    },
    {
        'id': 't_recover',
        'from': 'error',
        'to': 'idle',
        'on_event': 'CLEAR',
        'gates': [],
        'actions': ['clear_error', 'clear_trace'],
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
    Compiled L++ Operator: L++ Execution Tracer
    """

    def __init__(self, compute_registry: dict = None):
        self.context = {'_state': ENTRY_STATE, 'config': None, 'trace_id': None, 'root_span_id': None, 'spans': None, 'active_spans': None, 'events': None, 'blueprint_id': None, 'blueprint_name': None, 'start_time': None, 'end_time': None, 'output_format': None, 'export_path': None, 'analysis_result': None, 'formatted_output': None, 'output': None, 'error': None}
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
                gate_result, _ = atom_EVALUATE(expr, scope)
                if not gate_result:
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
                self.context, _ = atom_MUTATE(self.context, target, value)
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
                    result, _ = atom_DISPATCH(
                        sys_id, op_id, inp, self.compute_registry
                    )
                    for ctx_path, res_key in action.get('output_map', {}).items():
                        if res_key in result:
                            self.context, _ = atom_MUTATE(
                                self.context, ctx_path, result[res_key]
                            )
                    scope.update(self.context)  # Sync scope for chained actions

        # TRANSITION
        (new_state, trace), _ = atom_TRANSITION(current, trans['to'])
        self.context, _ = atom_MUTATE(self.context, '_state', new_state)
        self.traces.append(trace)

        return True, new_state, None

    def get(self, path: str):
        """Get a value from context by path."""
        return _resolve_path(path, self.context)

    def set(self, path: str, value):
        """Set a value in context by path."""
        self.context, _ = atom_MUTATE(self.context, path, value)

    def display(self) -> str:
        """Evaluate display rules and return formatted string."""
        for rule in DISPLAY_RULES:
            gate = rule.get('gate')
            if gate:
                expr = GATES.get(gate, 'False')
                gate_result, _ = atom_EVALUATE(expr, self.context)
                if not gate_result:
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
        self.context = {'_state': ENTRY_STATE, 'config': None, 'trace_id': None, 'root_span_id': None, 'spans': None, 'active_spans': None, 'events': None, 'blueprint_id': None, 'blueprint_name': None, 'start_time': None, 'end_time': None, 'output_format': None, 'export_path': None, 'analysis_result': None, 'formatted_output': None, 'output': None, 'error': None}
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
                print(f'[L++ WARNING] Blueprint ID mismatch: {state_data.get("blueprint_id")}')
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
    print('L++ Compiled Operator: L++ Execution Tracer')
    print('States:', list(STATES.keys()))
    print('Entry:', ENTRY_STATE)
    print('Transitions:', len(TRANSITIONS))
