---------------------------- MODULE blueprint_builder ----------------------------
\* L++ Blueprint: Blueprint Builder
\* Version: 1.0.0
\* Auto-generated TLA+ specification (universal adaptor)

EXTENDS Integers, Sequences, TLC

\* =========================================================
\* BOUNDS - Constrain state space for model checking
\* =========================================================
INT_MIN == -5
INT_MAX == 5
MAX_HISTORY == 3
BoundedInt == INT_MIN..INT_MAX

\* NULL constant for uninitialized values
CONSTANT NULL

\* States
States == {"idle", "building", "complete", "error"}

Events == {"BUILD", "DONE", "ERROR"}

TerminalStates == {"complete", "error"}

VARIABLES
    state,           \* Current state
    event_history    \* Trace of events

vars == <<state, event_history>>

\* Type invariant - structural correctness
TypeInvariant ==
    /\ state \in States

\* State constraint - limits TLC exploration depth
StateConstraint ==
    /\ Len(event_history) <= MAX_HISTORY

\* Initial state
Init ==
    /\ state = "idle"
    /\ event_history = <<>>

\* Transitions
\* t0: idle --(BUILD)--> building
t0 ==
    /\ state = "idle"
    /\ state' = "building"
    /\ event_history' = Append(event_history, "BUILD")

\* t1: building --(DONE)--> complete
t1 ==
    /\ state = "building"
    /\ state' = "complete"
    /\ event_history' = Append(event_history, "DONE")

\* t2: * --(ERROR)--> error
t2 ==
    /\ TRUE  \* from any state
    /\ state' = "error"
    /\ event_history' = Append(event_history, "ERROR")

\* Next state relation
Next ==
    \/ t0
    \/ t1
    \/ t2

\* Specification
Spec == Init /\ [][Next]_vars

\* Safety: Always in valid state
AlwaysValidState == state \in States

\* Reachability: Entry state is reachable
EntryReachable == state = "idle"

\* Terminal states are reachable
TerminalReachable == <>(state = "complete" \/ state = "error")

=============================================================================