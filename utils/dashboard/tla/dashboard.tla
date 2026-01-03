---------------------------- MODULE dashboard ----------------------------
\* L++ Blueprint: L++ Tools Dashboard
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
States == {"idle", "scanning", "analyzing", "categorizing", "generating", "complete", "error"}

Events == {"AUTO", "RESET", "SCAN"}

TerminalStates == {"complete"}

VARIABLES
    state,           \* Current state
    utilsPath,           \* Path to the utils directory
    tools,           \* List of discovered tool metadata
    categories,           \* Tools grouped by category
    statistics,           \* Aggregated statistics across all tools
    htmlPath,           \* Path to generated dashboard HTML
    hasTools,           \* Context variable
    hasHtml,           \* Context variable
    error,           \* Context variable
    event_history    \* Trace of events

vars == <<state, utilsPath, tools, categories, statistics, htmlPath, hasTools, hasHtml, error, event_history>>

\* Type invariant - structural correctness
TypeInvariant ==
    /\ state \in States
    /\ TRUE  \* utilsPath: any string or NULL
    /\ TRUE  \* tools: any string or NULL
    /\ TRUE  \* categories: any string or NULL
    /\ TRUE  \* statistics: any string or NULL
    /\ TRUE  \* htmlPath: any string or NULL
    /\ (hasTools \in BOOLEAN) \/ (hasTools = NULL)
    /\ (hasHtml \in BOOLEAN) \/ (hasHtml = NULL)
    /\ TRUE  \* error: any string or NULL

\* State constraint - limits TLC exploration depth
StateConstraint ==
    /\ Len(event_history) <= MAX_HISTORY

\* Initial state
Init ==
    /\ state = "idle"
    /\ utilsPath = NULL
    /\ tools = NULL
    /\ categories = NULL
    /\ statistics = NULL
    /\ htmlPath = NULL
    /\ hasTools = NULL
    /\ hasHtml = NULL
    /\ error = NULL
    /\ event_history = <<>>

\* Transitions
\* t_start_scan: idle --(SCAN)--> scanning
t_start_scan ==
    /\ state = "idle"
    /\ utilsPath /= NULL /\ Len(utilsPath) > 0  \* gate: hasUtilsPath
    /\ state' = "scanning"
    /\ utilsPath' = utilsPath
    /\ tools' = tools
    /\ categories' = categories
    /\ statistics' = statistics
    /\ htmlPath' = htmlPath
    /\ hasTools' = hasTools
    /\ hasHtml' = hasHtml
    /\ error' = error
    /\ event_history' = Append(event_history, "SCAN")

\* t_scan_error: scanning --(AUTO)--> error
t_scan_error ==
    /\ state = "scanning"
    /\ error /= NULL /\ Len(error) > 0  \* gate: hasError
    /\ state' = "error"
    /\ utilsPath' = utilsPath
    /\ tools' = tools
    /\ categories' = categories
    /\ statistics' = statistics
    /\ htmlPath' = htmlPath
    /\ hasTools' = hasTools
    /\ hasHtml' = hasHtml
    /\ error' = error
    /\ event_history' = Append(event_history, "AUTO")

\* t_scan_done: scanning --(AUTO)--> analyzing
t_scan_done ==
    /\ state = "scanning"
    /\ tools /= NULL /\ Len(tools) > 0  \* gate: hasTools
    /\ state' = "analyzing"
    /\ utilsPath' = utilsPath
    /\ tools' = tools
    /\ categories' = categories
    /\ statistics' = statistics
    /\ htmlPath' = htmlPath
    /\ hasTools' = hasTools
    /\ hasHtml' = hasHtml
    /\ error' = error
    /\ event_history' = Append(event_history, "AUTO")

\* t_analyze_error: analyzing --(AUTO)--> error
t_analyze_error ==
    /\ state = "analyzing"
    /\ error /= NULL /\ Len(error) > 0  \* gate: hasError
    /\ state' = "error"
    /\ utilsPath' = utilsPath
    /\ tools' = tools
    /\ categories' = categories
    /\ statistics' = statistics
    /\ htmlPath' = htmlPath
    /\ hasTools' = hasTools
    /\ hasHtml' = hasHtml
    /\ error' = error
    /\ event_history' = Append(event_history, "AUTO")

\* t_analyze_done: analyzing --(AUTO)--> categorizing
t_analyze_done ==
    /\ state = "analyzing"
    /\ statistics /= NULL  \* gate: hasStatistics
    /\ state' = "categorizing"
    /\ utilsPath' = utilsPath
    /\ tools' = tools
    /\ categories' = categories
    /\ statistics' = statistics
    /\ htmlPath' = htmlPath
    /\ hasTools' = hasTools
    /\ hasHtml' = hasHtml
    /\ error' = error
    /\ event_history' = Append(event_history, "AUTO")

\* t_categorize_error: categorizing --(AUTO)--> error
t_categorize_error ==
    /\ state = "categorizing"
    /\ error /= NULL /\ Len(error) > 0  \* gate: hasError
    /\ state' = "error"
    /\ utilsPath' = utilsPath
    /\ tools' = tools
    /\ categories' = categories
    /\ statistics' = statistics
    /\ htmlPath' = htmlPath
    /\ hasTools' = hasTools
    /\ hasHtml' = hasHtml
    /\ error' = error
    /\ event_history' = Append(event_history, "AUTO")

\* t_categorize_done: categorizing --(AUTO)--> generating
t_categorize_done ==
    /\ state = "categorizing"
    /\ categories /= NULL  \* gate: hasCategories
    /\ state' = "generating"
    /\ utilsPath' = utilsPath
    /\ tools' = tools
    /\ categories' = categories
    /\ statistics' = statistics
    /\ htmlPath' = htmlPath
    /\ hasTools' = hasTools
    /\ hasHtml' = hasHtml
    /\ error' = error
    /\ event_history' = Append(event_history, "AUTO")

\* t_generate_error: generating --(AUTO)--> error
t_generate_error ==
    /\ state = "generating"
    /\ error /= NULL /\ Len(error) > 0  \* gate: hasError
    /\ state' = "error"
    /\ utilsPath' = utilsPath
    /\ tools' = tools
    /\ categories' = categories
    /\ statistics' = statistics
    /\ htmlPath' = htmlPath
    /\ hasTools' = hasTools
    /\ hasHtml' = hasHtml
    /\ error' = error
    /\ event_history' = Append(event_history, "AUTO")

\* t_generate_done: generating --(AUTO)--> complete
t_generate_done ==
    /\ state = "generating"
    /\ state' = "complete"
    /\ utilsPath' = utilsPath
    /\ tools' = tools
    /\ categories' = categories
    /\ statistics' = statistics
    /\ htmlPath' = htmlPath
    /\ hasTools' = hasTools
    /\ hasHtml' = hasHtml
    /\ error' = error
    /\ event_history' = Append(event_history, "AUTO")

\* t_reset: * --(RESET)--> idle
t_reset ==
    /\ TRUE  \* from any state
    /\ state' = "idle"
    /\ utilsPath' = utilsPath
    /\ tools' = tools
    /\ categories' = categories
    /\ statistics' = statistics
    /\ htmlPath' = htmlPath
    /\ hasTools' = hasTools
    /\ hasHtml' = hasHtml
    /\ error' = error
    /\ event_history' = Append(event_history, "RESET")

\* Next state relation
Next ==
    \/ t_start_scan
    \/ t_scan_error
    \/ t_scan_done
    \/ t_analyze_error
    \/ t_analyze_done
    \/ t_categorize_error
    \/ t_categorize_done
    \/ t_generate_error
    \/ t_generate_done
    \/ t_reset

\* Specification
Spec == Init /\ [][Next]_vars

\* Safety: Always in valid state
AlwaysValidState == state \in States

\* Reachability: Entry state is reachable
EntryReachable == state = "idle"

\* Terminal states are reachable
TerminalReachable == <>(state = "complete")

=============================================================================