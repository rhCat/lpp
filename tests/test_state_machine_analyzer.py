"""
Tests for StateMachineAnalyzer._find_ungated_transitions gate-pointer fix.

The L++ schema stores gates as transition['gates'] (transition→gate pointer),
NOT as gate['transitions'] (gate→transition pointer). This file verifies that
the analyzer correctly reads gate presence from the transition itself.
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parent.parent / "workflows" / "logic_vulnerability_pointer" / "src"))

from lvp_state_machine_analyzer import StateMachineAnalyzer


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _make_bone(transitions, gates=None):
    """Build a minimal bone.json dict for testing."""
    return {
        "states": {
            "idle": {"name": "Idle"},
            "processing": {"name": "Processing"},
            "done": {"name": "Done"},
            "error": {"name": "Error"},
        },
        "transitions": transitions,
        "gates": gates or {},
        "entry_state": "idle",
        "terminal_states": ["done", "error"],
    }


def _ungated_self_loop_ids(bone):
    analyzer = StateMachineAnalyzer(bone, "test")
    vulns = analyzer._find_ungated_transitions()
    return {v.affected_transitions[0] for v in vulns if v.vuln_type == "UNGATED_SELF_LOOP"}


# ---------------------------------------------------------------------------
# Core gate-pointer direction tests
# ---------------------------------------------------------------------------

class TestGatePointerDirection:
    """Verify that gates are read from transition['gates'], not gate['transitions']."""

    def test_gated_self_loop_not_flagged(self):
        """Self-loop with non-empty gates list must not be flagged."""
        bone = _make_bone(
            transitions=[
                {
                    "id": "t_self",
                    "from": "processing",
                    "to": "processing",
                    "on_event": "TICK",
                    "gates": ["g_iter_bound"],
                }
            ],
            gates={
                "g_iter_bound": {
                    "type": "expression",
                    "expression": "iteration_count < MAX_ITERATIONS",
                }
            },
        )
        assert "t_self" not in _ungated_self_loop_ids(bone)

    def test_ungated_self_loop_flagged(self):
        """Self-loop with empty gates list must be flagged as UNGATED_SELF_LOOP."""
        bone = _make_bone(
            transitions=[
                {
                    "id": "t_self_ungated",
                    "from": "processing",
                    "to": "processing",
                    "on_event": "TICK",
                    "gates": [],
                }
            ],
        )
        assert "t_self_ungated" in _ungated_self_loop_ids(bone)

    def test_missing_gates_field_flagged(self):
        """Self-loop with no 'gates' key at all must be flagged."""
        bone = _make_bone(
            transitions=[
                {
                    "id": "t_no_gates_key",
                    "from": "processing",
                    "to": "processing",
                    "on_event": "TICK",
                }
            ],
        )
        assert "t_no_gates_key" in _ungated_self_loop_ids(bone)

    def test_convergence_gate_self_loop_not_flagged(self):
        """Self-loop gated by a convergence-type (ITER_BOUNDED) gate must not be flagged."""
        bone = _make_bone(
            transitions=[
                {
                    "id": "t_converge",
                    "from": "processing",
                    "to": "processing",
                    "on_event": "ITER",
                    "gates": ["g_converge"],
                }
            ],
            gates={
                "g_converge": {
                    "gate_type": "convergence",
                    "bound_type": "ITER_BOUNDED",
                    "expression": "i < n",
                }
            },
        )
        assert "t_converge" not in _ungated_self_loop_ids(bone)

    def test_old_gate_transitions_pointer_ignored(self):
        """Legacy gate['transitions'] pointer must NOT grant gated status.

        Verifies the bug was in the old code: having gate['transitions'] in the
        gates dict alone (without transition['gates']) must not suppress the flag.
        """
        bone = _make_bone(
            transitions=[
                {
                    "id": "t_no_gate_ref",
                    "from": "processing",
                    "to": "processing",
                    "on_event": "TICK",
                    # No 'gates' key — only the old (wrong) direction exists
                },
            ],
            gates={
                "g_legacy": {
                    "type": "expression",
                    "expression": "x > 0",
                    "transitions": ["t_no_gate_ref"],  # old wrong-direction pointer
                }
            },
        )
        # The transition has no gates[], so it IS ungated regardless of gate['transitions']
        assert "t_no_gate_ref" in _ungated_self_loop_ids(bone)

    def test_non_self_loop_not_flagged(self):
        """Non-self-loop ungated transitions must not be flagged as UNGATED_SELF_LOOP."""
        bone = _make_bone(
            transitions=[
                {
                    "id": "t_forward",
                    "from": "idle",
                    "to": "processing",
                    "on_event": "START",
                    "gates": [],
                }
            ],
        )
        # t_forward is ungated but it's NOT a self-loop — only self-loops are flagged
        assert "t_forward" not in _ungated_self_loop_ids(bone)

    def test_mixed_transitions_only_ungated_self_loops_flagged(self):
        """Only truly ungated self-loops are flagged; gated ones are clean."""
        bone = _make_bone(
            transitions=[
                {
                    "id": "t_gated_loop",
                    "from": "processing",
                    "to": "processing",
                    "on_event": "ITER",
                    "gates": ["g_bound"],
                },
                {
                    "id": "t_ungated_loop",
                    "from": "idle",
                    "to": "idle",
                    "on_event": "NOP",
                    "gates": [],
                },
                {
                    "id": "t_forward",
                    "from": "idle",
                    "to": "processing",
                    "on_event": "START",
                },
            ],
            gates={
                "g_bound": {
                    "type": "expression",
                    "expression": "i < limit",
                }
            },
        )
        flagged = _ungated_self_loop_ids(bone)
        assert "t_ungated_loop" in flagged
        assert "t_gated_loop" not in flagged
        assert "t_forward" not in flagged

    def test_wildcard_from_never_flagged(self):
        """Transitions from '*' (any state) are exempt from ungated checks."""
        bone = _make_bone(
            transitions=[
                {
                    "id": "t_global_tick",
                    "from": "*",
                    "to": "processing",
                    "on_event": "TICK",
                    "gates": [],
                }
            ],
        )
        assert "t_global_tick" not in _ungated_self_loop_ids(bone)


# ---------------------------------------------------------------------------
# Full analyze() round-trip — count regression
# ---------------------------------------------------------------------------

class TestAnalyzeRoundTrip:
    """Verify the full analyze() path with the pointer fix."""

    def test_all_bounded_for_loops_clean(self):
        """Blueprint where every self-loop has a gate should produce zero UNGATED_SELF_LOOP."""
        transitions = [
            {
                "id": f"t_loop_{i}",
                "from": "processing",
                "to": "processing",
                "on_event": f"ITER_{i}",
                "gates": ["g_bound"],
            }
            for i in range(10)
        ]
        bone = _make_bone(
            transitions=transitions,
            gates={"g_bound": {"gate_type": "convergence", "bound_type": "ITER_BOUNDED", "expression": "i < n"}},
        )
        analyzer = StateMachineAnalyzer(bone, "test")
        vulns = analyzer.analyze()
        ungated = [v for v in vulns if v.vuln_type == "UNGATED_SELF_LOOP"]
        assert ungated == [], f"Expected no UNGATED_SELF_LOOP, got: {[v.description for v in ungated]}"

    def test_truly_ungated_while_true_flagged(self):
        """Blueprint with an ungated self-loop (loop {}/while true equivalent) must still be flagged."""
        bone = _make_bone(
            transitions=[
                {
                    "id": "t_infinite",
                    "from": "processing",
                    "to": "processing",
                    "on_event": "SPIN",
                    # no gates at all
                }
            ],
        )
        analyzer = StateMachineAnalyzer(bone, "test")
        vulns = analyzer.analyze()
        ungated = [v for v in vulns if v.vuln_type == "UNGATED_SELF_LOOP"]
        assert len(ungated) == 1
        assert ungated[0].affected_transitions == ["t_infinite"]
