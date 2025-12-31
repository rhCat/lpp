---------------------------- MODULE skill_registry ----------------------------
\* L++ Blueprint: Skill Registry
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
States == {"idle", "scanned", "viewing", "error"}

Events == {"BACK", "EXPORT", "RESET", "RETRY", "SCAN", "SELECT"}

TerminalStates == {}

VARIABLES
    state,           \* Current state
    basePath,           \* Base path to scan for skills
    skills,           \* List of discovered skill metadata
    selectedSkill,           \* Currently selected skill details
    registry,           \* Full registry export for agent context
    error,           \* Error message
    event_history    \* Trace of events

vars == <<state, basePath, skills, selectedSkill, registry, error, event_history>>

\* Type invariant - structural correctness
TypeInvariant ==
    /\ state \in States
    /\ TRUE  \* basePath: any string or NULL
    /\ TRUE  \* skills: any string or NULL
    /\ TRUE  \* selectedSkill: any string or NULL
    /\ TRUE  \* registry: any string or NULL
    /\ TRUE  \* error: any string or NULL

\* State constraint - limits TLC exploration depth
StateConstraint ==
    /\ Len(event_history) <= MAX_HISTORY

\* Initial state
Init ==
    /\ state = "idle"
    /\ basePath = NULL
    /\ skills = NULL
    /\ selectedSkill = NULL
    /\ registry = NULL
    /\ error = NULL
    /\ event_history = <<>>

\* Transitions
\* t_scan: idle --(SCAN)--> scanned
t_scan ==
    /\ state = "idle"
    /\ state' = "scanned"
    /\ basePath' = basePath
    /\ skills' = skills
    /\ selectedSkill' = selectedSkill
    /\ registry' = registry
    /\ error' = error
    /\ event_history' = Append(event_history, "SCAN")

\* t_rescan: scanned --(SCAN)--> scanned
t_rescan ==
    /\ state = "scanned"
    /\ state' = "scanned"
    /\ basePath' = basePath
    /\ skills' = skills
    /\ selectedSkill' = selectedSkill
    /\ registry' = registry
    /\ error' = error
    /\ event_history' = Append(event_history, "SCAN")

\* t_select: scanned --(SELECT)--> viewing
t_select ==
    /\ state = "scanned"
    /\ state' = "viewing"
    /\ basePath' = basePath
    /\ skills' = skills
    /\ selectedSkill' = selectedSkill
    /\ registry' = registry
    /\ error' = error
    /\ event_history' = Append(event_history, "SELECT")

\* t_back: viewing --(BACK)--> scanned
t_back ==
    /\ state = "viewing"
    /\ state' = "scanned"
    /\ basePath' = basePath
    /\ skills' = skills
    /\ selectedSkill' = selectedSkill
    /\ registry' = registry
    /\ error' = error
    /\ event_history' = Append(event_history, "BACK")

\* t_select_another: viewing --(SELECT)--> viewing
t_select_another ==
    /\ state = "viewing"
    /\ state' = "viewing"
    /\ basePath' = basePath
    /\ skills' = skills
    /\ selectedSkill' = selectedSkill
    /\ registry' = registry
    /\ error' = error
    /\ event_history' = Append(event_history, "SELECT")

\* t_export: scanned --(EXPORT)--> scanned
t_export ==
    /\ state = "scanned"
    /\ state' = "scanned"
    /\ basePath' = basePath
    /\ skills' = skills
    /\ selectedSkill' = selectedSkill
    /\ registry' = registry
    /\ error' = error
    /\ event_history' = Append(event_history, "EXPORT")

\* t_export_viewing: viewing --(EXPORT)--> viewing
t_export_viewing ==
    /\ state = "viewing"
    /\ state' = "viewing"
    /\ basePath' = basePath
    /\ skills' = skills
    /\ selectedSkill' = selectedSkill
    /\ registry' = registry
    /\ error' = error
    /\ event_history' = Append(event_history, "EXPORT")

\* t_reset: scanned --(RESET)--> idle
t_reset ==
    /\ state = "scanned"
    /\ state' = "idle"
    /\ basePath' = basePath
    /\ skills' = skills
    /\ selectedSkill' = selectedSkill
    /\ registry' = registry
    /\ error' = error
    /\ event_history' = Append(event_history, "RESET")

\* t_retry: error --(RETRY)--> idle
t_retry ==
    /\ state = "error"
    /\ state' = "idle"
    /\ basePath' = basePath
    /\ skills' = skills
    /\ selectedSkill' = selectedSkill
    /\ registry' = registry
    /\ error' = error
    /\ event_history' = Append(event_history, "RETRY")

\* Next state relation
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

\* Specification
Spec == Init /\ [][Next]_vars

\* Safety: Always in valid state
AlwaysValidState == state \in States

\* Liveness: No deadlock (always can make progress)
NoDeadlock == <>(ENABLED Next)

\* Reachability: Entry state is reachable
EntryReachable == state = "idle"

=============================================================================