---------------------------- MODULE research_scraper ----------------------------
\* L++ Blueprint: Research Scraper
\* Version: 1.0.1
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

\* =========================================================
\* DOMAINS - Auto-extracted from context_schema
\* =========================================================
SourceDomain == {"arxiv", "semantic_scholar", "web"}

\* States
States == {"idle", "hasResults", "error"}

Events == {"CLEAR", "RETRY", "SEARCH_ARXIV", "SEARCH_SCHOLAR", "SEARCH_WEB", "SELECT"}

TerminalStates == {}

VARIABLES
    state,           \* Current state
    query,           \* Search query
    source,           \* Context variable
    maxResults,           \* Maximum results
    results,           \* Search results
    selectedId,           \* Selected paper ID
    detail,           \* Full paper details
    error,           \* Error message
    event_history    \* Trace of events

vars == <<state, query, source, maxResults, results, selectedId, detail, error, event_history>>

\* Type invariant - structural correctness
TypeInvariant ==
    /\ state \in States
    /\ TRUE  \* query: any string or NULL
    /\ (source \in SourceDomain) \/ (source = NULL)
    /\ (maxResults \in BoundedInt) \/ (maxResults = NULL)
    /\ TRUE  \* results: any string or NULL
    /\ TRUE  \* selectedId: any string or NULL
    /\ TRUE  \* detail: any string or NULL
    /\ TRUE  \* error: any string or NULL

\* State constraint - limits TLC exploration depth
StateConstraint ==
    /\ Len(event_history) <= MAX_HISTORY
    /\ (maxResults = NULL) \/ (maxResults \in BoundedInt)

\* Initial state
Init ==
    /\ state = "idle"
    /\ query = NULL
    /\ source = NULL
    /\ maxResults = NULL
    /\ results = NULL
    /\ selectedId = NULL
    /\ detail = NULL
    /\ error = NULL
    /\ event_history = <<>>

\* Transitions
\* t_search_arxiv: idle --(SEARCH_ARXIV)--> hasResults
t_search_arxiv ==
    /\ state = "idle"
    /\ state' = "hasResults"
    /\ query' = query
    /\ source' = source
    /\ maxResults' = maxResults
    /\ results' = results
    /\ selectedId' = selectedId
    /\ detail' = detail
    /\ error' = error
    /\ event_history' = Append(event_history, "SEARCH_ARXIV")

\* t_search_scholar: idle --(SEARCH_SCHOLAR)--> hasResults
t_search_scholar ==
    /\ state = "idle"
    /\ state' = "hasResults"
    /\ query' = query
    /\ source' = source
    /\ maxResults' = maxResults
    /\ results' = results
    /\ selectedId' = selectedId
    /\ detail' = detail
    /\ error' = error
    /\ event_history' = Append(event_history, "SEARCH_SCHOLAR")

\* t_search_web: idle --(SEARCH_WEB)--> hasResults
t_search_web ==
    /\ state = "idle"
    /\ state' = "hasResults"
    /\ query' = query
    /\ source' = source
    /\ maxResults' = maxResults
    /\ results' = results
    /\ selectedId' = selectedId
    /\ detail' = detail
    /\ error' = error
    /\ event_history' = Append(event_history, "SEARCH_WEB")

\* t_select: hasResults --(SELECT)--> hasResults
t_select ==
    /\ state = "hasResults"
    /\ state' = "hasResults"
    /\ query' = query
    /\ source' = source
    /\ maxResults' = maxResults
    /\ results' = results
    /\ selectedId' = selectedId
    /\ detail' = detail
    /\ error' = error
    /\ event_history' = Append(event_history, "SELECT")

\* t_search_new_arxiv: hasResults --(SEARCH_ARXIV)--> hasResults
t_search_new_arxiv ==
    /\ state = "hasResults"
    /\ state' = "hasResults"
    /\ query' = query
    /\ source' = source
    /\ maxResults' = maxResults
    /\ results' = results
    /\ selectedId' = selectedId
    /\ detail' = detail
    /\ error' = error
    /\ event_history' = Append(event_history, "SEARCH_ARXIV")

\* t_search_new_scholar: hasResults --(SEARCH_SCHOLAR)--> hasResults
t_search_new_scholar ==
    /\ state = "hasResults"
    /\ state' = "hasResults"
    /\ query' = query
    /\ source' = source
    /\ maxResults' = maxResults
    /\ results' = results
    /\ selectedId' = selectedId
    /\ detail' = detail
    /\ error' = error
    /\ event_history' = Append(event_history, "SEARCH_SCHOLAR")

\* t_search_new_web: hasResults --(SEARCH_WEB)--> hasResults
t_search_new_web ==
    /\ state = "hasResults"
    /\ state' = "hasResults"
    /\ query' = query
    /\ source' = source
    /\ maxResults' = maxResults
    /\ results' = results
    /\ selectedId' = selectedId
    /\ detail' = detail
    /\ error' = error
    /\ event_history' = Append(event_history, "SEARCH_WEB")

\* t_clear: hasResults --(CLEAR)--> idle
t_clear ==
    /\ state = "hasResults"
    /\ state' = "idle"
    /\ query' = query
    /\ source' = source
    /\ maxResults' = maxResults
    /\ results' = results
    /\ selectedId' = selectedId
    /\ detail' = detail
    /\ error' = error
    /\ event_history' = Append(event_history, "CLEAR")

\* t_retry: error --(RETRY)--> idle
t_retry ==
    /\ state = "error"
    /\ state' = "idle"
    /\ query' = query
    /\ source' = source
    /\ maxResults' = maxResults
    /\ results' = results
    /\ selectedId' = selectedId
    /\ detail' = detail
    /\ error' = error
    /\ event_history' = Append(event_history, "RETRY")

\* Next state relation
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

\* Specification
Spec == Init /\ [][Next]_vars

\* Safety: Always in valid state
AlwaysValidState == state \in States

\* Liveness: No deadlock (always can make progress)
NoDeadlock == <>(ENABLED Next)

\* Reachability: Entry state is reachable
EntryReachable == state = "idle"

=============================================================================