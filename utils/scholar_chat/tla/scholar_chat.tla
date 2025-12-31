---------------------------- MODULE scholar_chat ----------------------------
\* L++ Blueprint: Scholar Chatbot
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
States == {"idle", "searching", "reviewing", "analyzing", "chatting", "error"}

Events == {"ASK", "BACK", "DONE", "INIT", "RESET", "RETRY", "SEARCH", "SELECT"}

TerminalStates == {}

VARIABLES
    state,           \* Current state
    apiKey,           \* LLM API key
    apiBase,           \* LLM API endpoint
    model,           \* LLM model name
    query,           \* Current research query
    sources,           \* Search sources to use [arxiv, semantic_scholar, web]
    searchResults,           \* Aggregated search results from all sources
    selectedPapers,           \* Papers selected for deep analysis
    paperDetails,           \* Fetched details for selected papers
    paperLinks,           \* URLs for selected papers [{title, url, pdfUrl}]
    conversation,           \* Chat history [{role, content}]
    synthesis,           \* LLM-generated research synthesis
    followUpQuestions,           \* Suggested follow-up questions
    error,           \* Error message
    event_history    \* Trace of events

vars == <<state, apiKey, apiBase, model, query, sources, searchResults, selectedPapers, paperDetails, paperLinks, conversation, synthesis, followUpQuestions, error, event_history>>

\* Type invariant - structural correctness
TypeInvariant ==
    /\ state \in States
    /\ TRUE  \* apiKey: any string or NULL
    /\ TRUE  \* apiBase: any string or NULL
    /\ TRUE  \* model: any string or NULL
    /\ TRUE  \* query: any string or NULL
    /\ TRUE  \* sources: any string or NULL
    /\ TRUE  \* searchResults: any string or NULL
    /\ TRUE  \* selectedPapers: any string or NULL
    /\ TRUE  \* paperDetails: any string or NULL
    /\ TRUE  \* paperLinks: any string or NULL
    /\ TRUE  \* conversation: any string or NULL
    /\ TRUE  \* synthesis: any string or NULL
    /\ TRUE  \* followUpQuestions: any string or NULL
    /\ TRUE  \* error: any string or NULL

\* State constraint - limits TLC exploration depth
StateConstraint ==
    /\ Len(event_history) <= MAX_HISTORY

\* Initial state
Init ==
    /\ state = "idle"
    /\ apiKey = NULL
    /\ apiBase = NULL
    /\ model = NULL
    /\ query = NULL
    /\ sources = NULL
    /\ searchResults = NULL
    /\ selectedPapers = NULL
    /\ paperDetails = NULL
    /\ paperLinks = NULL
    /\ conversation = NULL
    /\ synthesis = NULL
    /\ followUpQuestions = NULL
    /\ error = NULL
    /\ event_history = <<>>

\* Transitions
\* t_init: idle --(INIT)--> idle
t_init ==
    /\ state = "idle"
    /\ state' = "idle"
    /\ apiKey' = apiKey
    /\ apiBase' = apiBase
    /\ model' = model
    /\ query' = query
    /\ sources' = sources
    /\ searchResults' = searchResults
    /\ selectedPapers' = selectedPapers
    /\ paperDetails' = paperDetails
    /\ paperLinks' = paperLinks
    /\ conversation' = conversation
    /\ synthesis' = synthesis
    /\ followUpQuestions' = followUpQuestions
    /\ error' = error
    /\ event_history' = Append(event_history, "INIT")

\* t_search: idle --(SEARCH)--> searching
t_search ==
    /\ state = "idle"
    /\ state' = "searching"
    /\ apiKey' = apiKey
    /\ apiBase' = apiBase
    /\ model' = model
    /\ query' = query
    /\ sources' = sources
    /\ searchResults' = searchResults
    /\ selectedPapers' = selectedPapers
    /\ paperDetails' = paperDetails
    /\ paperLinks' = paperLinks
    /\ conversation' = conversation
    /\ synthesis' = synthesis
    /\ followUpQuestions' = followUpQuestions
    /\ error' = error
    /\ event_history' = Append(event_history, "SEARCH")

\* t_search_done: searching --(DONE)--> reviewing
t_search_done ==
    /\ state = "searching"
    /\ error = NULL  \* gate: noError
    /\ state' = "reviewing"
    /\ apiKey' = apiKey
    /\ apiBase' = apiBase
    /\ model' = model
    /\ query' = query
    /\ sources' = sources
    /\ searchResults' = searchResults
    /\ selectedPapers' = selectedPapers
    /\ paperDetails' = paperDetails
    /\ paperLinks' = paperLinks
    /\ conversation' = conversation
    /\ synthesis' = synthesis
    /\ followUpQuestions' = followUpQuestions
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_search_error: searching --(DONE)--> error
t_search_error ==
    /\ state = "searching"
    /\ error /= NULL  \* gate: hasError
    /\ state' = "error"
    /\ apiKey' = apiKey
    /\ apiBase' = apiBase
    /\ model' = model
    /\ query' = query
    /\ sources' = sources
    /\ searchResults' = searchResults
    /\ selectedPapers' = selectedPapers
    /\ paperDetails' = paperDetails
    /\ paperLinks' = paperLinks
    /\ conversation' = conversation
    /\ synthesis' = synthesis
    /\ followUpQuestions' = followUpQuestions
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_new_search: reviewing --(SEARCH)--> searching
t_new_search ==
    /\ state = "reviewing"
    /\ state' = "searching"
    /\ apiKey' = apiKey
    /\ apiBase' = apiBase
    /\ model' = model
    /\ query' = query
    /\ sources' = sources
    /\ searchResults' = searchResults
    /\ selectedPapers' = selectedPapers
    /\ paperDetails' = paperDetails
    /\ paperLinks' = paperLinks
    /\ conversation' = conversation
    /\ synthesis' = synthesis
    /\ followUpQuestions' = followUpQuestions
    /\ error' = error
    /\ event_history' = Append(event_history, "SEARCH")

\* t_select: reviewing --(SELECT)--> analyzing
t_select ==
    /\ state = "reviewing"
    /\ state' = "analyzing"
    /\ apiKey' = apiKey
    /\ apiBase' = apiBase
    /\ model' = model
    /\ query' = query
    /\ sources' = sources
    /\ searchResults' = searchResults
    /\ selectedPapers' = selectedPapers
    /\ paperDetails' = paperDetails
    /\ paperLinks' = paperLinks
    /\ conversation' = conversation
    /\ synthesis' = synthesis
    /\ followUpQuestions' = followUpQuestions
    /\ error' = error
    /\ event_history' = Append(event_history, "SELECT")

\* t_analyze_done: analyzing --(DONE)--> chatting
t_analyze_done ==
    /\ state = "analyzing"
    /\ error = NULL  \* gate: noError
    /\ state' = "chatting"
    /\ apiKey' = apiKey
    /\ apiBase' = apiBase
    /\ model' = model
    /\ query' = query
    /\ sources' = sources
    /\ searchResults' = searchResults
    /\ selectedPapers' = selectedPapers
    /\ paperDetails' = paperDetails
    /\ paperLinks' = paperLinks
    /\ conversation' = conversation
    /\ synthesis' = synthesis
    /\ followUpQuestions' = followUpQuestions
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_analyze_error: analyzing --(DONE)--> error
t_analyze_error ==
    /\ state = "analyzing"
    /\ error /= NULL  \* gate: hasError
    /\ state' = "error"
    /\ apiKey' = apiKey
    /\ apiBase' = apiBase
    /\ model' = model
    /\ query' = query
    /\ sources' = sources
    /\ searchResults' = searchResults
    /\ selectedPapers' = selectedPapers
    /\ paperDetails' = paperDetails
    /\ paperLinks' = paperLinks
    /\ conversation' = conversation
    /\ synthesis' = synthesis
    /\ followUpQuestions' = followUpQuestions
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_ask: chatting --(ASK)--> chatting
t_ask ==
    /\ state = "chatting"
    /\ state' = "chatting"
    /\ apiKey' = apiKey
    /\ apiBase' = apiBase
    /\ model' = model
    /\ query' = query
    /\ sources' = sources
    /\ searchResults' = searchResults
    /\ selectedPapers' = selectedPapers
    /\ paperDetails' = paperDetails
    /\ paperLinks' = paperLinks
    /\ conversation' = conversation
    /\ synthesis' = synthesis
    /\ followUpQuestions' = followUpQuestions
    /\ error' = error
    /\ event_history' = Append(event_history, "ASK")

\* t_new_search_chat: chatting --(SEARCH)--> searching
t_new_search_chat ==
    /\ state = "chatting"
    /\ state' = "searching"
    /\ apiKey' = apiKey
    /\ apiBase' = apiBase
    /\ model' = model
    /\ query' = query
    /\ sources' = sources
    /\ searchResults' = searchResults
    /\ selectedPapers' = selectedPapers
    /\ paperDetails' = paperDetails
    /\ paperLinks' = paperLinks
    /\ conversation' = conversation
    /\ synthesis' = synthesis
    /\ followUpQuestions' = followUpQuestions
    /\ error' = error
    /\ event_history' = Append(event_history, "SEARCH")

\* t_reselect: chatting --(BACK)--> reviewing
t_reselect ==
    /\ state = "chatting"
    /\ state' = "reviewing"
    /\ apiKey' = apiKey
    /\ apiBase' = apiBase
    /\ model' = model
    /\ query' = query
    /\ sources' = sources
    /\ searchResults' = searchResults
    /\ selectedPapers' = selectedPapers
    /\ paperDetails' = paperDetails
    /\ paperLinks' = paperLinks
    /\ conversation' = conversation
    /\ synthesis' = synthesis
    /\ followUpQuestions' = followUpQuestions
    /\ error' = error
    /\ event_history' = Append(event_history, "BACK")

\* t_reset: reviewing --(RESET)--> idle
t_reset ==
    /\ state = "reviewing"
    /\ state' = "idle"
    /\ apiKey' = apiKey
    /\ apiBase' = apiBase
    /\ model' = model
    /\ query' = query
    /\ sources' = sources
    /\ searchResults' = searchResults
    /\ selectedPapers' = selectedPapers
    /\ paperDetails' = paperDetails
    /\ paperLinks' = paperLinks
    /\ conversation' = conversation
    /\ synthesis' = synthesis
    /\ followUpQuestions' = followUpQuestions
    /\ error' = error
    /\ event_history' = Append(event_history, "RESET")

\* t_retry: error --(RETRY)--> idle
t_retry ==
    /\ state = "error"
    /\ state' = "idle"
    /\ apiKey' = apiKey
    /\ apiBase' = apiBase
    /\ model' = model
    /\ query' = query
    /\ sources' = sources
    /\ searchResults' = searchResults
    /\ selectedPapers' = selectedPapers
    /\ paperDetails' = paperDetails
    /\ paperLinks' = paperLinks
    /\ conversation' = conversation
    /\ synthesis' = synthesis
    /\ followUpQuestions' = followUpQuestions
    /\ error' = error
    /\ event_history' = Append(event_history, "RETRY")

\* Next state relation
Next ==
    \/ t_init
    \/ t_search
    \/ t_search_done
    \/ t_search_error
    \/ t_new_search
    \/ t_select
    \/ t_analyze_done
    \/ t_analyze_error
    \/ t_ask
    \/ t_new_search_chat
    \/ t_reselect
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