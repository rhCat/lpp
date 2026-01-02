---------------------------- MODULE graph_visualizer ----------------------------
\* L++ Blueprint: Graph Visualizer
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
States == {"idle", "generating", "done"}

Events == {"generate", "start"}

TerminalStates == {"done"}

VARIABLES
    state,           \* Current state
    blueprint,           \* JSON representation of the L++ blueprint
    html_path,           \* Path to the generated HTML file
    has_blueprint,           \* Context variable
    has_html,           \* Context variable
    error,           \* Context variable
    event_history    \* Trace of events

vars == <<state, blueprint, html_path, has_blueprint, has_html, error, event_history>>

\* Type invariant - structural correctness
TypeInvariant ==
    /\ state \in States
    /\ TRUE  \* blueprint: any string or NULL
    /\ TRUE  \* html_path: any string or NULL
    /\ (has_blueprint \in BOOLEAN) \/ (has_blueprint = NULL)
    /\ (has_html \in BOOLEAN) \/ (has_html = NULL)
    /\ TRUE  \* error: any string or NULL

\* State constraint - limits TLC exploration depth
StateConstraint ==
    /\ Len(event_history) <= MAX_HISTORY

\* Initial state
Init ==
    /\ state = "idle"
    /\ blueprint = NULL
    /\ html_path = NULL
    /\ has_blueprint = NULL
    /\ has_html = NULL
    /\ error = NULL
    /\ event_history = <<>>

\* Transitions
\* t_start: idle --(start)--> generating
t_start ==
    /\ state = "idle"
    /\ has_blueprint = TRUE  \* gate: has_blueprint
    /\ state' = "generating"
    /\ blueprint' = blueprint
    /\ html_path' = html_path
    /\ has_blueprint' = has_blueprint
    /\ has_html' = has_html
    /\ error' = error
    /\ event_history' = Append(event_history, "start")

\* t_generate: generating --(generate)--> done
t_generate ==
    /\ state = "generating"
    /\ state' = "done"
    /\ blueprint' = blueprint
    /\ html_path' = html_path
    /\ has_blueprint' = has_blueprint
    /\ has_html' = has_html
    /\ error' = error
    /\ event_history' = Append(event_history, "generate")

\* Next state relation
Next ==
    \/ t_start
    \/ t_generate

\* Specification
Spec == Init /\ [][Next]_vars

\* Safety: Always in valid state
AlwaysValidState == state \in States

\* Reachability: Entry state is reachable
EntryReachable == state = "idle"

\* Terminal states are reachable
TerminalReachable == <>(state = "done")

=============================================================================