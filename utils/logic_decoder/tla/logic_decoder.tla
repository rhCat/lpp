---------------------------- MODULE logic_decoder ----------------------------
\* L++ Blueprint: Python Logic Decoder
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
States == {"idle", "parsing", "analyzing", "inferring", "generating", "complete", "error"}

Events == {"AUTO", "DECODE", "ERROR", "RESET"}

TerminalStates == {}

VARIABLES
    state,           \* Current state
    filePath,           \* Context variable
    sourceCode,           \* Context variable
    ast,           \* Context variable
    imports,           \* Context variable
    functions,           \* Context variable
    classes,           \* Context variable
    controlFlow,           \* Context variable
    inferredStates,           \* Context variable
    inferredTransitions,           \* Context variable
    inferredActions,           \* Context variable
    inferredGates,           \* Context variable
    blueprint,           \* Context variable
    blueprintJson,           \* Context variable
    analysisReport,           \* Context variable
    error,           \* Context variable
    event_history    \* Trace of events

vars == <<state, filePath, sourceCode, ast, imports, functions, classes, controlFlow, inferredStates, inferredTransitions, inferredActions, inferredGates, blueprint, blueprintJson, analysisReport, error, event_history>>

\* Type invariant - structural correctness
TypeInvariant ==
    /\ state \in States
    /\ TRUE  \* filePath: any string or NULL
    /\ TRUE  \* sourceCode: any string or NULL
    /\ TRUE  \* ast: any string or NULL
    /\ TRUE  \* imports: any string or NULL
    /\ TRUE  \* functions: any string or NULL
    /\ TRUE  \* classes: any string or NULL
    /\ TRUE  \* controlFlow: any string or NULL
    /\ TRUE  \* inferredStates: any string or NULL
    /\ TRUE  \* inferredTransitions: any string or NULL
    /\ TRUE  \* inferredActions: any string or NULL
    /\ TRUE  \* inferredGates: any string or NULL
    /\ TRUE  \* blueprint: any string or NULL
    /\ TRUE  \* blueprintJson: any string or NULL
    /\ TRUE  \* analysisReport: any string or NULL
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
    /\ imports = NULL
    /\ functions = NULL
    /\ classes = NULL
    /\ controlFlow = NULL
    /\ inferredStates = NULL
    /\ inferredTransitions = NULL
    /\ inferredActions = NULL
    /\ inferredGates = NULL
    /\ blueprint = NULL
    /\ blueprintJson = NULL
    /\ analysisReport = NULL
    /\ error = NULL
    /\ event_history = <<>>

\* Transitions
\* t1_load: idle --(DECODE)--> parsing
t1_load ==
    /\ state = "idle"
    /\ state' = "parsing"
    /\ filePath' = filePath
    /\ sourceCode' = sourceCode
    /\ ast' = ast
    /\ imports' = imports
    /\ functions' = functions
    /\ classes' = classes
    /\ controlFlow' = controlFlow
    /\ inferredStates' = inferredStates
    /\ inferredTransitions' = inferredTransitions
    /\ inferredActions' = inferredActions
    /\ inferredGates' = inferredGates
    /\ blueprint' = blueprint
    /\ blueprintJson' = blueprintJson
    /\ analysisReport' = analysisReport
    /\ error' = error
    /\ event_history' = Append(event_history, "DECODE")

\* t2_parse: parsing --(AUTO)--> analyzing
t2_parse ==
    /\ state = "parsing"
    /\ state' = "analyzing"
    /\ filePath' = filePath
    /\ sourceCode' = sourceCode
    /\ ast' = ast
    /\ imports' = imports
    /\ functions' = functions
    /\ classes' = classes
    /\ controlFlow' = controlFlow
    /\ inferredStates' = inferredStates
    /\ inferredTransitions' = inferredTransitions
    /\ inferredActions' = inferredActions
    /\ inferredGates' = inferredGates
    /\ blueprint' = blueprint
    /\ blueprintJson' = blueprintJson
    /\ analysisReport' = analysisReport
    /\ error' = error
    /\ event_history' = Append(event_history, "AUTO")

\* t3_analyze: analyzing --(AUTO)--> inferring
t3_analyze ==
    /\ state = "analyzing"
    /\ state' = "inferring"
    /\ filePath' = filePath
    /\ sourceCode' = sourceCode
    /\ ast' = ast
    /\ imports' = imports
    /\ functions' = functions
    /\ classes' = classes
    /\ controlFlow' = controlFlow
    /\ inferredStates' = inferredStates
    /\ inferredTransitions' = inferredTransitions
    /\ inferredActions' = inferredActions
    /\ inferredGates' = inferredGates
    /\ blueprint' = blueprint
    /\ blueprintJson' = blueprintJson
    /\ analysisReport' = analysisReport
    /\ error' = error
    /\ event_history' = Append(event_history, "AUTO")

\* t4_infer: inferring --(AUTO)--> generating
t4_infer ==
    /\ state = "inferring"
    /\ state' = "generating"
    /\ filePath' = filePath
    /\ sourceCode' = sourceCode
    /\ ast' = ast
    /\ imports' = imports
    /\ functions' = functions
    /\ classes' = classes
    /\ controlFlow' = controlFlow
    /\ inferredStates' = inferredStates
    /\ inferredTransitions' = inferredTransitions
    /\ inferredActions' = inferredActions
    /\ inferredGates' = inferredGates
    /\ blueprint' = blueprint
    /\ blueprintJson' = blueprintJson
    /\ analysisReport' = analysisReport
    /\ error' = error
    /\ event_history' = Append(event_history, "AUTO")

\* t5_generate: generating --(AUTO)--> complete
t5_generate ==
    /\ state = "generating"
    /\ state' = "complete"
    /\ filePath' = filePath
    /\ sourceCode' = sourceCode
    /\ ast' = ast
    /\ imports' = imports
    /\ functions' = functions
    /\ classes' = classes
    /\ controlFlow' = controlFlow
    /\ inferredStates' = inferredStates
    /\ inferredTransitions' = inferredTransitions
    /\ inferredActions' = inferredActions
    /\ inferredGates' = inferredGates
    /\ blueprint' = blueprint
    /\ blueprintJson' = blueprintJson
    /\ analysisReport' = analysisReport
    /\ error' = error
    /\ event_history' = Append(event_history, "AUTO")

\* t6_error_parse: parsing --(ERROR)--> error
t6_error_parse ==
    /\ state = "parsing"
    /\ state' = "error"
    /\ filePath' = filePath
    /\ sourceCode' = sourceCode
    /\ ast' = ast
    /\ imports' = imports
    /\ functions' = functions
    /\ classes' = classes
    /\ controlFlow' = controlFlow
    /\ inferredStates' = inferredStates
    /\ inferredTransitions' = inferredTransitions
    /\ inferredActions' = inferredActions
    /\ inferredGates' = inferredGates
    /\ blueprint' = blueprint
    /\ blueprintJson' = blueprintJson
    /\ analysisReport' = analysisReport
    /\ error' = error
    /\ event_history' = Append(event_history, "ERROR")

\* t7_error_analyze: analyzing --(ERROR)--> error
t7_error_analyze ==
    /\ state = "analyzing"
    /\ state' = "error"
    /\ filePath' = filePath
    /\ sourceCode' = sourceCode
    /\ ast' = ast
    /\ imports' = imports
    /\ functions' = functions
    /\ classes' = classes
    /\ controlFlow' = controlFlow
    /\ inferredStates' = inferredStates
    /\ inferredTransitions' = inferredTransitions
    /\ inferredActions' = inferredActions
    /\ inferredGates' = inferredGates
    /\ blueprint' = blueprint
    /\ blueprintJson' = blueprintJson
    /\ analysisReport' = analysisReport
    /\ error' = error
    /\ event_history' = Append(event_history, "ERROR")

\* t8_error_infer: inferring --(ERROR)--> error
t8_error_infer ==
    /\ state = "inferring"
    /\ state' = "error"
    /\ filePath' = filePath
    /\ sourceCode' = sourceCode
    /\ ast' = ast
    /\ imports' = imports
    /\ functions' = functions
    /\ classes' = classes
    /\ controlFlow' = controlFlow
    /\ inferredStates' = inferredStates
    /\ inferredTransitions' = inferredTransitions
    /\ inferredActions' = inferredActions
    /\ inferredGates' = inferredGates
    /\ blueprint' = blueprint
    /\ blueprintJson' = blueprintJson
    /\ analysisReport' = analysisReport
    /\ error' = error
    /\ event_history' = Append(event_history, "ERROR")

\* t9_reset: complete --(RESET)--> idle
t9_reset ==
    /\ state = "complete"
    /\ state' = "idle"
    /\ filePath' = filePath
    /\ sourceCode' = sourceCode
    /\ ast' = ast
    /\ imports' = imports
    /\ functions' = functions
    /\ classes' = classes
    /\ controlFlow' = controlFlow
    /\ inferredStates' = inferredStates
    /\ inferredTransitions' = inferredTransitions
    /\ inferredActions' = inferredActions
    /\ inferredGates' = inferredGates
    /\ blueprint' = blueprint
    /\ blueprintJson' = blueprintJson
    /\ analysisReport' = analysisReport
    /\ error' = error
    /\ event_history' = Append(event_history, "RESET")

\* t10_error_reset: error --(RESET)--> idle
t10_error_reset ==
    /\ state = "error"
    /\ state' = "idle"
    /\ filePath' = filePath
    /\ sourceCode' = sourceCode
    /\ ast' = ast
    /\ imports' = imports
    /\ functions' = functions
    /\ classes' = classes
    /\ controlFlow' = controlFlow
    /\ inferredStates' = inferredStates
    /\ inferredTransitions' = inferredTransitions
    /\ inferredActions' = inferredActions
    /\ inferredGates' = inferredGates
    /\ blueprint' = blueprint
    /\ blueprintJson' = blueprintJson
    /\ analysisReport' = analysisReport
    /\ error' = error
    /\ event_history' = Append(event_history, "RESET")

\* Next state relation
Next ==
    \/ t1_load
    \/ t2_parse
    \/ t3_analyze
    \/ t4_infer
    \/ t5_generate
    \/ t6_error_parse
    \/ t7_error_analyze
    \/ t8_error_infer
    \/ t9_reset
    \/ t10_error_reset

\* Specification
Spec == Init /\ [][Next]_vars

\* Safety: Always in valid state
AlwaysValidState == state \in States

\* Liveness: No deadlock (always can make progress)
NoDeadlock == <>(ENABLED Next)

\* Reachability: Entry state is reachable
EntryReachable == state = "idle"

=============================================================================