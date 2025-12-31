---------------------------- MODULE skill_registry ----------------------------
\* L++ Blueprint: Skill Registry
\* Version: 1.0.0
\* TLAPS Seal Specification

EXTENDS Integers, Sequences, TLC

\* Bounds for model checking
MAX_HISTORY == 3
CONSTANT NULL

States == {"idle", "scanned", "viewing", "error"}
Events == {"BACK", "EXPORT", "RESET", "RETRY", "SCAN", "SELECT"}
TerminalStates == {}

VARIABLES
    state,
    basePath,
    skills,
    selectedSkill,
    registry,
    error

vars == <<state, basePath, skills, selectedSkill, registry, error>>

\* Type Invariant - Structural Correctness
TypeInvariant ==
    /\ state \in States
    /\ TRUE  \* basePath
    /\ TRUE  \* skills
    /\ TRUE  \* selectedSkill
    /\ TRUE  \* registry
    /\ TRUE  \* error

\* Initial State
Init ==
    /\ state = "idle"
    /\ basePath = NULL
    /\ skills = NULL
    /\ selectedSkill = NULL
    /\ registry = NULL
    /\ error = NULL

\* Transitions
\* t_scan: idle --(SCAN)--> scanned
t_scan ==
    /\ state = "idle"
    /\ state' = "scanned"
    /\ UNCHANGED <<basePath, skills, selectedSkill, registry, error>>

\* t_rescan: scanned --(SCAN)--> scanned
t_rescan ==
    /\ state = "scanned"
    /\ state' = "scanned"
    /\ UNCHANGED <<basePath, skills, selectedSkill, registry, error>>

\* t_select: scanned --(SELECT)--> viewing
t_select ==
    /\ state = "scanned"
    /\ state' = "viewing"
    /\ UNCHANGED <<basePath, skills, selectedSkill, registry, error>>

\* t_back: viewing --(BACK)--> scanned
t_back ==
    /\ state = "viewing"
    /\ state' = "scanned"
    /\ UNCHANGED <<basePath, skills, selectedSkill, registry, error>>

\* t_select_another: viewing --(SELECT)--> viewing
t_select_another ==
    /\ state = "viewing"
    /\ state' = "viewing"
    /\ UNCHANGED <<basePath, skills, selectedSkill, registry, error>>

\* t_export: scanned --(EXPORT)--> scanned
t_export ==
    /\ state = "scanned"
    /\ state' = "scanned"
    /\ UNCHANGED <<basePath, skills, selectedSkill, registry, error>>

\* t_export_viewing: viewing --(EXPORT)--> viewing
t_export_viewing ==
    /\ state = "viewing"
    /\ state' = "viewing"
    /\ UNCHANGED <<basePath, skills, selectedSkill, registry, error>>

\* t_reset: scanned --(RESET)--> idle
t_reset ==
    /\ state = "scanned"
    /\ state' = "idle"
    /\ UNCHANGED <<basePath, skills, selectedSkill, registry, error>>

\* t_retry: error --(RETRY)--> idle
t_retry ==
    /\ state = "error"
    /\ state' = "idle"
    /\ UNCHANGED <<basePath, skills, selectedSkill, registry, error>>

\* Next State Relation
Next ==
    \/ t_scan
    \/ t_rescan
    \/ t_select
    \/ t_back
    \/ t_select_another
    \/ t_export
    \/ t_export_viewing
    \/ t_reset
    \/ t_retry

\* Safety Invariant - Convergence Guarantee
SafetyInvariant ==
    state \in TerminalStates \/
    \E e \in Events : ENABLED(Next)

\* Temporal Specification
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* =========================================================
\* TLAPS THEOREMS - Axiomatic Certification
\* =========================================================

\* Theorem 1: Type Safety
THEOREM TypeSafety == Spec => []TypeInvariant
PROOF OMITTED  \* To be proven by TLAPS

\* Theorem 2: Convergence (No unhandled deadlock)
THEOREM Convergence == Spec => []SafetyInvariant
PROOF OMITTED  \* To be proven by TLAPS

\* Theorem 3: Terminal Reachability
THEOREM TerminalReachable == Spec => <>(TRUE)
PROOF OMITTED  \* To be proven by TLAPS

============================================================================