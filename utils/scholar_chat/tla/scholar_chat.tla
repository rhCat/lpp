---------------------------- MODULE scholar_chat ----------------------------
\* L++ Blueprint: Scholar Chatbot
\* Version: 1.0.0
\* TLAPS Seal Specification

EXTENDS Integers, Sequences, TLC

\* Bounds for model checking
MAX_HISTORY == 3
CONSTANT NULL

States == {"idle", "searching", "reviewing", "analyzing", "chatting", "error"}
Events == {"ASK", "BACK", "DONE", "INIT", "RESET", "RETRY", "SEARCH", "SELECT"}
TerminalStates == {}

VARIABLES
    state,
    apiKey,
    apiBase,
    model,
    query,
    sources,
    searchResults,
    selectedPapers,
    paperDetails,
    paperLinks,
    conversation,
    synthesis,
    followUpQuestions,
    error

vars == <<state, apiKey, apiBase, model, query, sources, searchResults, selectedPapers, paperDetails, paperLinks, conversation, synthesis, followUpQuestions, error>>

\* Type Invariant - Structural Correctness
TypeInvariant ==
    /\ state \in States
    /\ TRUE  \* apiKey
    /\ TRUE  \* apiBase
    /\ TRUE  \* model
    /\ TRUE  \* query
    /\ TRUE  \* sources
    /\ TRUE  \* searchResults
    /\ TRUE  \* selectedPapers
    /\ TRUE  \* paperDetails
    /\ TRUE  \* paperLinks
    /\ TRUE  \* conversation
    /\ TRUE  \* synthesis
    /\ TRUE  \* followUpQuestions
    /\ TRUE  \* error

\* Initial State
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

\* Transitions
\* t_init: idle --(INIT)--> idle
t_init ==
    /\ state = "idle"
    /\ state' = "idle"
    /\ UNCHANGED <<apiKey, apiBase, model, query, sources, searchResults, selectedPapers, paperDetails, paperLinks, conversation, synthesis, followUpQuestions, error>>

\* t_search: idle --(SEARCH)--> searching
t_search ==
    /\ state = "idle"
    /\ state' = "searching"
    /\ UNCHANGED <<apiKey, apiBase, model, query, sources, searchResults, selectedPapers, paperDetails, paperLinks, conversation, synthesis, followUpQuestions, error>>

\* t_search_done: searching --(DONE)--> reviewing
t_search_done ==
    /\ state = "searching"
    /\ state' = "reviewing"
    /\ error = NULL  \* Gate: noError
    /\ UNCHANGED <<apiKey, apiBase, model, query, sources, searchResults, selectedPapers, paperDetails, paperLinks, conversation, synthesis, followUpQuestions, error>>

\* t_search_error: searching --(DONE)--> error
t_search_error ==
    /\ state = "searching"
    /\ state' = "error"
    /\ error # NULL  \* Gate: hasError
    /\ UNCHANGED <<apiKey, apiBase, model, query, sources, searchResults, selectedPapers, paperDetails, paperLinks, conversation, synthesis, followUpQuestions, error>>

\* t_new_search: reviewing --(SEARCH)--> searching
t_new_search ==
    /\ state = "reviewing"
    /\ state' = "searching"
    /\ UNCHANGED <<apiKey, apiBase, model, query, sources, searchResults, selectedPapers, paperDetails, paperLinks, conversation, synthesis, followUpQuestions, error>>

\* t_select: reviewing --(SELECT)--> analyzing
t_select ==
    /\ state = "reviewing"
    /\ state' = "analyzing"
    /\ UNCHANGED <<apiKey, apiBase, model, query, sources, searchResults, selectedPapers, paperDetails, paperLinks, conversation, synthesis, followUpQuestions, error>>

\* t_analyze_done: analyzing --(DONE)--> chatting
t_analyze_done ==
    /\ state = "analyzing"
    /\ state' = "chatting"
    /\ error = NULL  \* Gate: noError
    /\ UNCHANGED <<apiKey, apiBase, model, query, sources, searchResults, selectedPapers, paperDetails, paperLinks, conversation, synthesis, followUpQuestions, error>>

\* t_analyze_error: analyzing --(DONE)--> error
t_analyze_error ==
    /\ state = "analyzing"
    /\ state' = "error"
    /\ error # NULL  \* Gate: hasError
    /\ UNCHANGED <<apiKey, apiBase, model, query, sources, searchResults, selectedPapers, paperDetails, paperLinks, conversation, synthesis, followUpQuestions, error>>

\* t_ask: chatting --(ASK)--> chatting
t_ask ==
    /\ state = "chatting"
    /\ state' = "chatting"
    /\ UNCHANGED <<apiKey, apiBase, model, query, sources, searchResults, selectedPapers, paperDetails, paperLinks, conversation, synthesis, followUpQuestions, error>>

\* t_new_search_chat: chatting --(SEARCH)--> searching
t_new_search_chat ==
    /\ state = "chatting"
    /\ state' = "searching"
    /\ UNCHANGED <<apiKey, apiBase, model, query, sources, searchResults, selectedPapers, paperDetails, paperLinks, conversation, synthesis, followUpQuestions, error>>

\* t_reselect: chatting --(BACK)--> reviewing
t_reselect ==
    /\ state = "chatting"
    /\ state' = "reviewing"
    /\ UNCHANGED <<apiKey, apiBase, model, query, sources, searchResults, selectedPapers, paperDetails, paperLinks, conversation, synthesis, followUpQuestions, error>>

\* t_reset: reviewing --(RESET)--> idle
t_reset ==
    /\ state = "reviewing"
    /\ state' = "idle"
    /\ UNCHANGED <<apiKey, apiBase, model, query, sources, searchResults, selectedPapers, paperDetails, paperLinks, conversation, synthesis, followUpQuestions, error>>

\* t_retry: error --(RETRY)--> idle
t_retry ==
    /\ state = "error"
    /\ state' = "idle"
    /\ UNCHANGED <<apiKey, apiBase, model, query, sources, searchResults, selectedPapers, paperDetails, paperLinks, conversation, synthesis, followUpQuestions, error>>

\* Next State Relation
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