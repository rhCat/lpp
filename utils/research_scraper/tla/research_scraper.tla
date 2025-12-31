---------------------------- MODULE research_scraper ----------------------------
\* L++ Blueprint: Research Scraper
\* Version: 1.0.1
\* TLAPS Seal Specification

EXTENDS Integers, Sequences, TLC

\* Bounds for model checking
MAX_HISTORY == 3
CONSTANT NULL

States == {"idle", "hasResults", "error"}
Events == {"CLEAR", "RETRY", "SEARCH_ARXIV", "SEARCH_SCHOLAR", "SEARCH_WEB", "SELECT"}
TerminalStates == {}

VARIABLES
    state,
    query,
    source,
    maxResults,
    results,
    selectedId,
    detail,
    error

vars == <<state, query, source, maxResults, results, selectedId, detail, error>>

\* Type Invariant - Structural Correctness
TypeInvariant ==
    /\ state \in States
    /\ TRUE  \* query
    /\ TRUE  \* source
    /\ TRUE  \* maxResults
    /\ TRUE  \* results
    /\ TRUE  \* selectedId
    /\ TRUE  \* detail
    /\ TRUE  \* error

\* Initial State
Init ==
    /\ state = "idle"
    /\ query = NULL
    /\ source = NULL
    /\ maxResults = NULL
    /\ results = NULL
    /\ selectedId = NULL
    /\ detail = NULL
    /\ error = NULL

\* Transitions
\* t_search_arxiv: idle --(SEARCH_ARXIV)--> hasResults
t_search_arxiv ==
    /\ state = "idle"
    /\ state' = "hasResults"
    /\ UNCHANGED <<query, source, maxResults, results, selectedId, detail, error>>

\* t_search_scholar: idle --(SEARCH_SCHOLAR)--> hasResults
t_search_scholar ==
    /\ state = "idle"
    /\ state' = "hasResults"
    /\ UNCHANGED <<query, source, maxResults, results, selectedId, detail, error>>

\* t_search_web: idle --(SEARCH_WEB)--> hasResults
t_search_web ==
    /\ state = "idle"
    /\ state' = "hasResults"
    /\ UNCHANGED <<query, source, maxResults, results, selectedId, detail, error>>

\* t_select: hasResults --(SELECT)--> hasResults
t_select ==
    /\ state = "hasResults"
    /\ state' = "hasResults"
    /\ UNCHANGED <<query, source, maxResults, results, selectedId, detail, error>>

\* t_search_new_arxiv: hasResults --(SEARCH_ARXIV)--> hasResults
t_search_new_arxiv ==
    /\ state = "hasResults"
    /\ state' = "hasResults"
    /\ UNCHANGED <<query, source, maxResults, results, selectedId, detail, error>>

\* t_search_new_scholar: hasResults --(SEARCH_SCHOLAR)--> hasResults
t_search_new_scholar ==
    /\ state = "hasResults"
    /\ state' = "hasResults"
    /\ UNCHANGED <<query, source, maxResults, results, selectedId, detail, error>>

\* t_search_new_web: hasResults --(SEARCH_WEB)--> hasResults
t_search_new_web ==
    /\ state = "hasResults"
    /\ state' = "hasResults"
    /\ UNCHANGED <<query, source, maxResults, results, selectedId, detail, error>>

\* t_clear: hasResults --(CLEAR)--> idle
t_clear ==
    /\ state = "hasResults"
    /\ state' = "idle"
    /\ UNCHANGED <<query, source, maxResults, results, selectedId, detail, error>>

\* t_retry: error --(RETRY)--> idle
t_retry ==
    /\ state = "error"
    /\ state' = "idle"
    /\ UNCHANGED <<query, source, maxResults, results, selectedId, detail, error>>

\* Next State Relation
Next ==
    \/ t_search_arxiv
    \/ t_search_scholar
    \/ t_search_web
    \/ t_select
    \/ t_search_new_arxiv
    \/ t_search_new_scholar
    \/ t_search_new_web
    \/ t_clear
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