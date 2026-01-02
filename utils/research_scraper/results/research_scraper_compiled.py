"""
L++ Compiled Operator: Research Scraper
Version: 1.0.1
Description: Scrape academic papers from arXiv, Semantic Scholar, and web

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

BLUEPRINT_ID = 'research_scraper'
BLUEPRINT_NAME = 'Research Scraper'
BLUEPRINT_VERSION = '1.0.1'
ENTRY_STATE = 'idle'
TERMINAL_STATES = set()

STATES = {
    'idle': 'idle',  # Ready for search query
    'hasResults': 'hasResults',  # Results available
    'error': 'error',  # Error occurred
}

GATES = {
    'hasQuery': 'query is not None',
    'hasResults': 'results is not None',
    'hasDetail': 'detail is not None',
    'hasError': 'error is not None',
    'noError': 'error is None',
}

DISPLAY_RULES = [
    {'gate': 'hasError', 'template': 'Error: {error}'},
    {'gate': 'hasDetail', 'template': 'Viewing: {detail.title}'},
    {'gate': 'hasResults', 'template': 'Found results for: {query}'},
    {'gate': 'hasQuery', 'template': 'Searching: {query}'},
    {'template': 'Ready'},
]

ACTIONS = {
    'setQuery': {
        'type': 'set',
        'target': 'query',
        'value_from': 'event.payload.query',
    },
    'setSourceArxiv': {
        'type': 'set',
        'target': 'source',
        'value': 'arxiv',
    },
    'setSourceScholar': {
        'type': 'set',
        'target': 'source',
        'value': 'semantic_scholar',
    },
    'setSourceWeb': {
        'type': 'set',
        'target': 'source',
        'value': 'web',
    },
    'setMaxResults': {
        'type': 'set',
        'target': 'maxResults',
        'value_from': 'event.payload.maxResults',
    },
    'searchArxiv': {
        'type': 'compute',
        'compute_unit': 'scraper:arxiv',
        'input_map': {'query': 'query', 'maxResults': 'maxResults'},
        'output_map': {'results': 'results', 'error': 'error'},
    },
    'searchSemanticScholar': {
        'type': 'compute',
        'compute_unit': 'scraper:semanticScholar',
        'input_map': {'query': 'query', 'maxResults': 'maxResults'},
        'output_map': {'results': 'results', 'error': 'error'},
    },
    'searchWeb': {
        'type': 'compute',
        'compute_unit': 'scraper:web',
        'input_map': {'query': 'query', 'maxResults': 'maxResults'},
        'output_map': {'results': 'results', 'error': 'error'},
    },
    'setSelectedId': {
        'type': 'set',
        'target': 'selectedId',
        'value_from': 'event.payload.id',
    },
    'setSourceFromPayload': {
        'type': 'set',
        'target': 'source',
        'value_from': 'event.payload.source',
    },
    'fetchDetail': {
        'type': 'compute',
        'compute_unit': 'scraper:fetchDetail',
        'input_map': {'id': 'selectedId', 'source': 'source'},
        'output_map': {'detail': 'detail', 'error': 'error'},
    },
    'clearResults': {
        'type': 'set',
        'target': 'results',
    },
    'clearDetail': {
        'type': 'set',
        'target': 'detail',
    },
    'clearError': {
        'type': 'set',
        'target': 'error',
    },
}

TRANSITIONS = [
    {
        'id': 't_search_arxiv',
        'from': 'idle',
        'to': 'hasResults',
        'on_event': 'SEARCH_ARXIV',
        'gates': [],
        'actions': ['setQuery', 'setMaxResults', 'setSourceArxiv', 'searchArxiv'],
    },
    {
        'id': 't_search_scholar',
        'from': 'idle',
        'to': 'hasResults',
        'on_event': 'SEARCH_SCHOLAR',
        'gates': [],
        'actions': ['setQuery', 'setMaxResults', 'setSourceScholar', 'searchSemanticScholar'],
    },
    {
        'id': 't_search_web',
        'from': 'idle',
        'to': 'hasResults',
        'on_event': 'SEARCH_WEB',
        'gates': [],
        'actions': ['setQuery', 'setMaxResults', 'setSourceWeb', 'searchWeb'],
    },
    {
        'id': 't_select',
        'from': 'hasResults',
        'to': 'hasResults',
        'on_event': 'SELECT',
        'gates': [],
        'actions': ['setSelectedId', 'setSourceFromPayload', 'fetchDetail'],
    },
    {
        'id': 't_search_new_arxiv',
        'from': 'hasResults',
        'to': 'hasResults',
        'on_event': 'SEARCH_ARXIV',
        'gates': [],
        'actions': ['clearDetail', 'setQuery', 'setMaxResults', 'setSourceArxiv', 'searchArxiv'],
    },
    {
        'id': 't_search_new_scholar',
        'from': 'hasResults',
        'to': 'hasResults',
        'on_event': 'SEARCH_SCHOLAR',
        'gates': [],
        'actions': ['clearDetail', 'setQuery', 'setMaxResults', 'setSourceScholar', 'searchSemanticScholar'],
    },
    {
        'id': 't_search_new_web',
        'from': 'hasResults',
        'to': 'hasResults',
        'on_event': 'SEARCH_WEB',
        'gates': [],
        'actions': ['clearDetail', 'setQuery', 'setMaxResults', 'setSourceWeb', 'searchWeb'],
    },
    {
        'id': 't_clear',
        'from': 'hasResults',
        'to': 'idle',
        'on_event': 'CLEAR',
        'gates': [],
        'actions': ['clearResults', 'clearDetail'],
    },
    {
        'id': 't_retry',
        'from': 'error',
        'to': 'idle',
        'on_event': 'RETRY',
        'gates': [],
        'actions': ['clearError'],
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
    Compiled L++ Operator: Research Scraper
    """

    def __init__(self, compute_registry: dict = None):
        self.context = {'_state': ENTRY_STATE, 'query': None, 'source': None, 'maxResults': None, 'results': None, 'selectedId': None, 'detail': None, 'error': None}
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
        self.context = {'_state': ENTRY_STATE, 'query': None, 'source': None, 'maxResults': None, 'results': None, 'selectedId': None, 'detail': None, 'error': None}
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
    print('L++ Compiled Operator: Research Scraper')
    print('States:', list(STATES.keys()))
    print('Entry:', ENTRY_STATE)
    print('Transitions:', len(TRANSITIONS))
