"""
L++ Policy Library

Verified state machine templates with customizable flesh bindings.
The stage is PROVED. Your actors determine the show.
"""

import json
import os
from typing import Dict, Callable, Any, Optional
from pathlib import Path


POLICY_DIR = Path(__file__).parent


class PolicySlotError(Exception):
    """Raised when a slot binding fails contract validation."""
    pass


class Policy:
    """
    A verified state machine template with bindable slots.

    The policy defines the stage - guaranteed correct structure.
    Users bind flesh (compute functions) to slots to customize behavior.
    """

    def __init__(self, policy_data: dict):
        self.id = policy_data["id"]
        self.name = policy_data["name"]
        self.version = policy_data["version"]
        self.description = policy_data.get("description", "")

        self.states = policy_data["states"]
        self.entry_state = policy_data["entry_state"]
        self.terminal_states = policy_data["terminal_states"]
        self.gates = policy_data.get("gates", {})
        self.slots = policy_data.get("slots", {})
        self.actions = policy_data.get("actions", {})
        self.transitions = policy_data.get("transitions", [])
        self.invariants = policy_data.get("invariants", {})

        self._bindings: Dict[str, Callable] = {}
        self._context: Dict[str, Any] = {}
        self._current_state: str = self.entry_state

    def bind(self, bindings: Dict[str, Callable]) -> "Policy":
        """
        Bind flesh (compute functions) to policy slots.

        Args:
            bindings: Dict mapping slot names to callable functions

        Returns:
            Self for chaining

        Raises:
            PolicySlotError: If a required slot is not bound
        """
        for slot_name, func in bindings.items():
            if slot_name not in self.slots:
                raise PolicySlotError(
                    f"Unknown slot '{slot_name}'. "
                    f"Available slots: {list(self.slots.keys())}"
                )
            if not callable(func):
                raise PolicySlotError(
                    f"Binding for slot '{slot_name}' must be callable"
                )
            self._bindings[slot_name] = func

        return self

    def validate_bindings(self) -> Dict[str, bool]:
        """
        Check that all required slots are bound.

        Returns:
            Dict mapping slot names to bound status
        """
        status = {}
        for slot_name in self.slots:
            status[slot_name] = slot_name in self._bindings
        return status

    def get_unbound_slots(self) -> list:
        """Return list of slots that haven't been bound."""
        return [s for s in self.slots if s not in self._bindings]

    def _evaluate_gate(self, gate_expr: str) -> bool:
        """Evaluate a gate expression against current context."""
        try:
            return eval(gate_expr, {"__builtins__": {}}, self._context)
        except Exception:
            return False

    def _execute_slot(self, slot_name: str, input_map: dict,
                      output_map: dict) -> Dict[str, Any]:
        """Execute a bound slot function."""
        if slot_name not in self._bindings:
            raise PolicySlotError(f"Slot '{slot_name}' not bound")

        # Build input params from context
        params = {}
        for param_name, ctx_key in input_map.items():
            params[param_name] = self._context.get(ctx_key)

        # Call the bound function
        func = self._bindings[slot_name]
        result = func(params)

        # Map outputs back to context
        for ctx_key, result_key in output_map.items():
            if result_key in result:
                self._context[ctx_key] = result[result_key]

        return result

    def dispatch(self, event: str, payload: Optional[dict] = None) -> dict:
        """
        Dispatch an event to the policy state machine.

        Args:
            event: Event name to dispatch
            payload: Optional payload to merge into context

        Returns:
            Dict with current state and context snapshot
        """
        if payload:
            self._context.update(payload)

        # Find matching transition
        for t in self.transitions:
            if t["from"] != self._current_state:
                continue
            if t["on_event"] != event:
                continue

            # Check guard if present
            guard = t.get("guard")
            if guard:
                gate_expr = self.gates.get(guard, guard)
                if not self._evaluate_gate(gate_expr):
                    continue

            # Execute action if present
            action_name = t.get("action")
            if action_name and action_name in self.actions:
                action = self.actions[action_name]
                if action["type"] == "slot":
                    self._execute_slot(
                        action["slot"],
                        action.get("input_map", {}),
                        action.get("output_map", {})
                    )
                elif action["type"] == "mutate":
                    for ctx_key, source in action.get("mutations", {}).items():
                        self._context[ctx_key] = self._context.get(source)

            # Transition
            self._current_state = t["to"]
            break

        return {
            "state": self._current_state,
            "context": dict(self._context),
            "is_terminal": self._current_state in self.terminal_states
        }

    def run(self, initial_context: dict, events: list) -> dict:
        """
        Run the policy with a sequence of events.

        Args:
            initial_context: Starting context
            events: List of (event_name, payload) tuples

        Returns:
            Final state and context
        """
        self._context = dict(initial_context)
        self._current_state = self.entry_state

        for event_item in events:
            if isinstance(event_item, tuple):
                event, payload = event_item
            else:
                event, payload = event_item, None

            result = self.dispatch(event, payload)
            if result["is_terminal"]:
                break

        return result

    @property
    def state(self) -> str:
        """Current state."""
        return self._current_state

    @property
    def context(self) -> dict:
        """Current context."""
        return dict(self._context)

    def reset(self):
        """Reset to initial state."""
        self._current_state = self.entry_state
        self._context = {}


def load_policy(policy_name: str) -> Policy:
    """
    Load a policy from the library.

    Args:
        policy_name: Name of the policy (without .json extension)

    Returns:
        Policy instance ready for binding
    """
    policy_path = POLICY_DIR / f"{policy_name}.json"

    if not policy_path.exists():
        available = [p.stem for p in POLICY_DIR.glob("*.json")]
        raise FileNotFoundError(
            f"Policy '{policy_name}' not found. "
            f"Available policies: {available}"
        )

    with open(policy_path) as f:
        data = json.load(f)

    return Policy(data)


def list_policies() -> list:
    """List all available policies."""
    policies = []
    for p in POLICY_DIR.glob("*.json"):
        with open(p) as f:
            data = json.load(f)
        policies.append({
            "id": data.get("id", p.stem),
            "name": data.get("name", p.stem),
            "version": data.get("version", "unknown"),
            "description": data.get("description", ""),
            "slots": list(data.get("slots", {}).keys())
        })
    return policies
