---------------------------- MODULE python_to_lpp ----------------------------
\* L++ Blueprint: Python to L++ Refactorer
\* Version: 1.0.0
\* Auto-generated TLA+ specification (universal adaptor)

EXTENDS Integers, Sequences, TLC

\* =========================================================
\* BOUNDS - Constrain state space for model checking
\* =========================================================
INT_MIN == -10
INT_MAX == 10
MAX_HISTORY == 5
BoundedInt == INT_MIN..INT_MAX

\* NULL constant for uninitialized values
CONSTANT NULL

\* States
States == {"idle", "scanning", "analyzing", "extracting", "generating_blueprints", "generating_compute", "generating_docs", "validating", "complete", "error"}

Events == {"DONE", "ERROR", "REFACTOR", "RESET", "START"}

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
\* t0: idle --(START)--> idle
t0 ==
    /\ state = "idle"
    /\ state' = "idle"
    /\ event_history' = Append(event_history, "START")

\* t1: idle --(REFACTOR)--> scanning
t1 ==
    /\ state = "idle"
    /\ projectPath /= NULL /\ Len(projectPath) > 0  \* gate: has_project
    /\ state' = "scanning"
    /\ event_history' = Append(event_history, "REFACTOR")

\* t2: idle --(REFACTOR)--> error
t2 ==
    /\ state = "idle"
    /\ projectPath = NULL \/ Len(projectPath) = 0  \* gate: no_project
    /\ state' = "error"
    /\ event_history' = Append(event_history, "REFACTOR")

\* t3: scanning --(DONE)--> analyzing
t3 ==
    /\ state = "scanning"
    /\ pythonFiles /= NULL /\ Len(pythonFiles) > 0  \* gate: has_python_files
    /\ error = NULL  \* gate: no_error
    /\ state' = "analyzing"
    /\ event_history' = Append(event_history, "DONE")

\* t4: scanning --(DONE)--> error
t4 ==
    /\ state = "scanning"
    /\ pythonFiles = NULL \/ Len(pythonFiles) = 0  \* gate: no_python_files
    /\ state' = "error"
    /\ event_history' = Append(event_history, "DONE")

\* t5: analyzing --(DONE)--> extracting
t5 ==
    /\ state = "analyzing"
    /\ error = NULL  \* gate: no_error
    /\ state' = "extracting"
    /\ event_history' = Append(event_history, "DONE")

\* t6: extracting --(DONE)--> generating_blueprints
t6 ==
    /\ state = "extracting"
    /\ extractedModules /= NULL /\ Len(extractedModules) > 0  \* gate: has_modules
    /\ error = NULL  \* gate: no_error
    /\ state' = "generating_blueprints"
    /\ event_history' = Append(event_history, "DONE")

\* t7: generating_blueprints --(DONE)--> generating_compute
t7 ==
    /\ state = "generating_blueprints"
    /\ blueprints /= NULL /\ Len(blueprints) > 0  \* gate: has_blueprints
    /\ error = NULL  \* gate: no_error
    /\ state' = "generating_compute"
    /\ event_history' = Append(event_history, "DONE")

\* t8: generating_compute --(DONE)--> generating_docs
t8 ==
    /\ state = "generating_compute"
    /\ options.get("generateDocs", TRUE)  \* gate: wants_docs
    /\ error = NULL  \* gate: no_error
    /\ state' = "generating_docs"
    /\ event_history' = Append(event_history, "DONE")

\* t9: generating_compute --(DONE)--> validating
t9 ==
    /\ state = "generating_compute"
    /\ error = NULL  \* gate: no_error
    /\ state' = "validating"
    /\ event_history' = Append(event_history, "DONE")

\* t10: generating_docs --(DONE)--> validating
t10 ==
    /\ state = "generating_docs"
    /\ error = NULL  \* gate: no_error
    /\ state' = "validating"
    /\ event_history' = Append(event_history, "DONE")

\* t11: validating --(DONE)--> complete
t11 ==
    /\ state = "validating"
    /\ error = NULL  \* gate: no_error
    /\ state' = "complete"
    /\ event_history' = Append(event_history, "DONE")

\* t12: * --(ERROR)--> error
t12 ==
    /\ TRUE  \* from any state
    /\ error /= NULL  \* gate: has_error
    /\ state' = "error"
    /\ event_history' = Append(event_history, "ERROR")

\* t13: error --(RESET)--> idle
t13 ==
    /\ state = "error"
    /\ state' = "idle"
    /\ event_history' = Append(event_history, "RESET")

\* t14: complete --(RESET)--> idle
t14 ==
    /\ state = "complete"
    /\ state' = "idle"
    /\ event_history' = Append(event_history, "RESET")

\* Next state relation
Next ==
    \/ t0
    \/ t1
    \/ t2
    \/ t3
    \/ t4
    \/ t5
    \/ t6
    \/ t7
    \/ t8
    \/ t9
    \/ t10
    \/ t11
    \/ t12
    \/ t13
    \/ t14

\* Specification
Spec == Init /\ [][Next]_vars

\* Safety: Always in valid state
AlwaysValidState == state \in States

\* Reachability: Entry state is reachable
EntryReachable == state = "idle"

\* Terminal states are reachable
TerminalReachable == <>(state = "complete" \/ state = "error")

=============================================================================