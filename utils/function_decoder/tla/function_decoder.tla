---------------------------- MODULE function_decoder ----------------------------
\* L++ Blueprint: Python Function Decoder
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
States == {"idle", "parsing", "extracting", "tracing", "computing", "complete", "error"}

Events == {"AUTO", "DECODE", "RESET"}

TerminalStates == {}

VARIABLES
    state,           \* Current state
    filePath,           \* Context variable
    sourceCode,           \* Context variable
    ast,           \* Context variable
    exports,           \* Public functions/classes (inbound interface)
    imports,           \* Import statements with usage tracking
    internalCalls,           \* Function-to-function call edges within script
    externalCalls,           \* Calls to imported modules
    localCalls,           \* Calls to other local scripts
    coupling,           \* Coupling metrics (fan-in, fan-out, etc.)
    moduleGraph,           \* Final linkable module graph
    error,           \* Context variable
    event_history    \* Trace of events

vars == <<state, filePath, sourceCode, ast, exports, imports, internalCalls, externalCalls, localCalls, coupling, moduleGraph, error, event_history>>

\* Type invariant - structural correctness
TypeInvariant ==
    /\ state \in States
    /\ TRUE  \* filePath: any string or NULL
    /\ TRUE  \* sourceCode: any string or NULL
    /\ TRUE  \* ast: any string or NULL
    /\ TRUE  \* exports: any string or NULL
    /\ TRUE  \* imports: any string or NULL
    /\ TRUE  \* internalCalls: any string or NULL
    /\ TRUE  \* externalCalls: any string or NULL
    /\ TRUE  \* localCalls: any string or NULL
    /\ TRUE  \* coupling: any string or NULL
    /\ TRUE  \* moduleGraph: any string or NULL
    /\ TRUE  \* error: any string or NULL

\* State constraint - limits TLC exploration depth
StateConstraint ==
    /\ Len(event_history) <= MAX_HISTORY

\* Initial state
Init ==
    /\ state = "idle"
    /\ filePath = NULL
    /\ sourceCode = NULL
    /\ ast = NULL
    /\ exports = NULL
    /\ imports = NULL
    /\ internalCalls = NULL
    /\ externalCalls = NULL
    /\ localCalls = NULL
    /\ coupling = NULL
    /\ moduleGraph = NULL
    /\ error = NULL
    /\ event_history = <<>>

\* Transitions
\* t_start_decode: idle --(DECODE)--> parsing
t_start_decode ==
    /\ state = "idle"
    /\ filePath /= NULL /\ Len(filePath) > 0  \* gate: hasFilePath
    /\ state' = "parsing"
    /\ filePath' = filePath
    /\ sourceCode' = sourceCode
    /\ ast' = ast
    /\ exports' = exports
    /\ imports' = imports
    /\ internalCalls' = internalCalls
    /\ externalCalls' = externalCalls
    /\ localCalls' = localCalls
    /\ coupling' = coupling
    /\ moduleGraph' = moduleGraph
    /\ error' = error
    /\ event_history' = Append(event_history, "DECODE")

\* t_parse_error: parsing --(AUTO)--> error
t_parse_error ==
    /\ state = "parsing"
    /\ error /= NULL /\ Len(error) > 0  \* gate: hasError
    /\ state' = "error"
    /\ filePath' = filePath
    /\ sourceCode' = sourceCode
    /\ ast' = ast
    /\ exports' = exports
    /\ imports' = imports
    /\ internalCalls' = internalCalls
    /\ externalCalls' = externalCalls
    /\ localCalls' = localCalls
    /\ coupling' = coupling
    /\ moduleGraph' = moduleGraph
    /\ error' = error
    /\ event_history' = Append(event_history, "AUTO")

\* t_parse_done: parsing --(AUTO)--> extracting
t_parse_done ==
    /\ state = "parsing"
    /\ ast /= NULL  \* gate: hasAst
    /\ state' = "extracting"
    /\ filePath' = filePath
    /\ sourceCode' = sourceCode
    /\ ast' = ast
    /\ exports' = exports
    /\ imports' = imports
    /\ internalCalls' = internalCalls
    /\ externalCalls' = externalCalls
    /\ localCalls' = localCalls
    /\ coupling' = coupling
    /\ moduleGraph' = moduleGraph
    /\ error' = error
    /\ event_history' = Append(event_history, "AUTO")

\* t_extract_error: extracting --(AUTO)--> error
t_extract_error ==
    /\ state = "extracting"
    /\ error /= NULL /\ Len(error) > 0  \* gate: hasError
    /\ state' = "error"
    /\ filePath' = filePath
    /\ sourceCode' = sourceCode
    /\ ast' = ast
    /\ exports' = exports
    /\ imports' = imports
    /\ internalCalls' = internalCalls
    /\ externalCalls' = externalCalls
    /\ localCalls' = localCalls
    /\ coupling' = coupling
    /\ moduleGraph' = moduleGraph
    /\ error' = error
    /\ event_history' = Append(event_history, "AUTO")

\* t_extract_done: extracting --(AUTO)--> tracing
t_extract_done ==
    /\ state = "extracting"
    /\ exports /= NULL /\ imports /= NULL  \* gate: hasExtracts
    /\ state' = "tracing"
    /\ filePath' = filePath
    /\ sourceCode' = sourceCode
    /\ ast' = ast
    /\ exports' = exports
    /\ imports' = imports
    /\ internalCalls' = internalCalls
    /\ externalCalls' = externalCalls
    /\ localCalls' = localCalls
    /\ coupling' = coupling
    /\ moduleGraph' = moduleGraph
    /\ error' = error
    /\ event_history' = Append(event_history, "AUTO")

\* t_trace_error: tracing --(AUTO)--> error
t_trace_error ==
    /\ state = "tracing"
    /\ error /= NULL /\ Len(error) > 0  \* gate: hasError
    /\ state' = "error"
    /\ filePath' = filePath
    /\ sourceCode' = sourceCode
    /\ ast' = ast
    /\ exports' = exports
    /\ imports' = imports
    /\ internalCalls' = internalCalls
    /\ externalCalls' = externalCalls
    /\ localCalls' = localCalls
    /\ coupling' = coupling
    /\ moduleGraph' = moduleGraph
    /\ error' = error
    /\ event_history' = Append(event_history, "AUTO")

\* t_trace_done: tracing --(AUTO)--> computing
t_trace_done ==
    /\ state = "tracing"
    /\ internalCalls /= NULL  \* gate: hasCalls
    /\ state' = "computing"
    /\ filePath' = filePath
    /\ sourceCode' = sourceCode
    /\ ast' = ast
    /\ exports' = exports
    /\ imports' = imports
    /\ internalCalls' = internalCalls
    /\ externalCalls' = externalCalls
    /\ localCalls' = localCalls
    /\ coupling' = coupling
    /\ moduleGraph' = moduleGraph
    /\ error' = error
    /\ event_history' = Append(event_history, "AUTO")

\* t_compute_error: computing --(AUTO)--> error
t_compute_error ==
    /\ state = "computing"
    /\ error /= NULL /\ Len(error) > 0  \* gate: hasError
    /\ state' = "error"
    /\ filePath' = filePath
    /\ sourceCode' = sourceCode
    /\ ast' = ast
    /\ exports' = exports
    /\ imports' = imports
    /\ internalCalls' = internalCalls
    /\ externalCalls' = externalCalls
    /\ localCalls' = localCalls
    /\ coupling' = coupling
    /\ moduleGraph' = moduleGraph
    /\ error' = error
    /\ event_history' = Append(event_history, "AUTO")

\* t_compute_done: computing --(AUTO)--> complete
t_compute_done ==
    /\ state = "computing"
    /\ state' = "complete"
    /\ filePath' = filePath
    /\ sourceCode' = sourceCode
    /\ ast' = ast
    /\ exports' = exports
    /\ imports' = imports
    /\ internalCalls' = internalCalls
    /\ externalCalls' = externalCalls
    /\ localCalls' = localCalls
    /\ coupling' = coupling
    /\ moduleGraph' = moduleGraph
    /\ error' = error
    /\ event_history' = Append(event_history, "AUTO")

\* t_reset: * --(RESET)--> idle
t_reset ==
    /\ TRUE  \* from any state
    /\ state' = "idle"
    /\ filePath' = filePath
    /\ sourceCode' = sourceCode
    /\ ast' = ast
    /\ exports' = exports
    /\ imports' = imports
    /\ internalCalls' = internalCalls
    /\ externalCalls' = externalCalls
    /\ localCalls' = localCalls
    /\ coupling' = coupling
    /\ moduleGraph' = moduleGraph
    /\ error' = error
    /\ event_history' = Append(event_history, "RESET")

\* Next state relation
Next ==
    \/ t_start_decode
    \/ t_parse_error
    \/ t_parse_done
    \/ t_extract_error
    \/ t_extract_done
    \/ t_trace_error
    \/ t_trace_done
    \/ t_compute_error
    \/ t_compute_done
    \/ t_reset

\* Specification
Spec == Init /\ [][Next]_vars

\* Safety: Always in valid state
AlwaysValidState == state \in States

\* Liveness: No deadlock (always can make progress)
NoDeadlock == <>(ENABLED Next)

\* Reachability: Entry state is reachable
EntryReachable == state = "idle"

=============================================================================