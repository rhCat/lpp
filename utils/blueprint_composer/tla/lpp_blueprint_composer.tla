---------------------------- MODULE lpp_blueprint_composer ----------------------------
\* L++ Blueprint: L++ Blueprint Composer
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
States == {"idle", "parent_loaded", "child_loaded", "defining_embedding", "embedding_ready", "composed", "validated", "error"}

Events == {"ADD_MORE", "BACK", "CANCEL", "CLEAR", "COMPOSE", "DEFINE", "DONE", "EXPORT", "FLATTEN", "LOAD_CHILD", "LOAD_FAILED", "LOAD_MANIFEST", "LOAD_PARENT", "QUICK_COMPOSE", "RESET", "SAVE_MANIFEST", "SET_EVENTS", "SET_INPUT", "SET_OUTPUT", "VALIDATE"}

TerminalStates == {}

VARIABLES
    state,           \* Current state
    parent_blueprint,           \* The loaded parent blueprint
    parent_path,           \* Path to the parent blueprint file
    child_blueprint,           \* The loaded child blueprint to embed
    child_path,           \* Path to the child blueprint file
    embeddings,           \* List of embedding definitions
    current_embedding,           \* Current embedding being defined
    composed_blueprint,           \* Result of composition operation
    validation_result,           \* Validation results with errors and warnings
    manifest,           \* Full composition manifest
    export_path,           \* Path where composed blueprint was exported
    error,           \* Error message if any
    namespace_prefix,           \* Prefix for child element namespacing
    event_history    \* Trace of events

vars == <<state, parent_blueprint, parent_path, child_blueprint, child_path, embeddings, current_embedding, composed_blueprint, validation_result, manifest, export_path, error, namespace_prefix, event_history>>

\* Type invariant - structural correctness
TypeInvariant ==
    /\ state \in States
    /\ TRUE  \* parent_blueprint: any string or NULL
    /\ TRUE  \* parent_path: any string or NULL
    /\ TRUE  \* child_blueprint: any string or NULL
    /\ TRUE  \* child_path: any string or NULL
    /\ TRUE  \* embeddings: any string or NULL
    /\ TRUE  \* current_embedding: any string or NULL
    /\ TRUE  \* composed_blueprint: any string or NULL
    /\ TRUE  \* validation_result: any string or NULL
    /\ TRUE  \* manifest: any string or NULL
    /\ TRUE  \* export_path: any string or NULL
    /\ TRUE  \* error: any string or NULL
    /\ TRUE  \* namespace_prefix: any string or NULL

\* State constraint - limits TLC exploration depth
StateConstraint ==
    /\ Len(event_history) <= MAX_HISTORY

\* Initial state
Init ==
    /\ state = "idle"
    /\ parent_blueprint = NULL
    /\ parent_path = NULL
    /\ child_blueprint = NULL
    /\ child_path = NULL
    /\ embeddings = NULL
    /\ current_embedding = NULL
    /\ composed_blueprint = NULL
    /\ validation_result = NULL
    /\ manifest = NULL
    /\ export_path = NULL
    /\ error = NULL
    /\ namespace_prefix = NULL
    /\ event_history = <<>>

\* Transitions
\* t_load_parent_from_idle: idle --(LOAD_PARENT)--> parent_loaded
t_load_parent_from_idle ==
    /\ state = "idle"
    /\ state' = "parent_loaded"
    /\ parent_blueprint' = parent_blueprint
    /\ parent_path' = parent_path
    /\ child_blueprint' = child_blueprint
    /\ child_path' = child_path
    /\ embeddings' = embeddings
    /\ current_embedding' = current_embedding
    /\ composed_blueprint' = composed_blueprint
    /\ validation_result' = validation_result
    /\ manifest' = manifest
    /\ export_path' = export_path
    /\ error' = error
    /\ namespace_prefix' = namespace_prefix
    /\ event_history' = Append(event_history, "LOAD_PARENT")

\* t_load_manifest: idle --(LOAD_MANIFEST)--> composed
t_load_manifest ==
    /\ state = "idle"
    /\ state' = "composed"
    /\ parent_blueprint' = parent_blueprint
    /\ parent_path' = parent_path
    /\ child_blueprint' = child_blueprint
    /\ child_path' = child_path
    /\ embeddings' = embeddings
    /\ current_embedding' = current_embedding
    /\ composed_blueprint' = composed_blueprint
    /\ validation_result' = validation_result
    /\ manifest' = manifest
    /\ export_path' = export_path
    /\ error' = error
    /\ namespace_prefix' = namespace_prefix
    /\ event_history' = Append(event_history, "LOAD_MANIFEST")

\* t_load_child: parent_loaded --(LOAD_CHILD)--> child_loaded
t_load_child ==
    /\ state = "parent_loaded"
    /\ parent_blueprint /= NULL  \* gate: has_parent
    /\ state' = "child_loaded"
    /\ parent_blueprint' = parent_blueprint
    /\ parent_path' = parent_path
    /\ child_blueprint' = child_blueprint
    /\ child_path' = child_path
    /\ embeddings' = embeddings
    /\ current_embedding' = current_embedding
    /\ composed_blueprint' = composed_blueprint
    /\ validation_result' = validation_result
    /\ manifest' = manifest
    /\ export_path' = export_path
    /\ error' = error
    /\ namespace_prefix' = namespace_prefix
    /\ event_history' = Append(event_history, "LOAD_CHILD")

\* t_reload_parent: parent_loaded --(LOAD_PARENT)--> parent_loaded
t_reload_parent ==
    /\ state = "parent_loaded"
    /\ state' = "parent_loaded"
    /\ parent_blueprint' = parent_blueprint
    /\ parent_path' = parent_path
    /\ child_blueprint' = child_blueprint
    /\ child_path' = child_path
    /\ embeddings' = embeddings
    /\ current_embedding' = current_embedding
    /\ composed_blueprint' = composed_blueprint
    /\ validation_result' = validation_result
    /\ manifest' = manifest
    /\ export_path' = export_path
    /\ error' = error
    /\ namespace_prefix' = namespace_prefix
    /\ event_history' = Append(event_history, "LOAD_PARENT")

\* t_reload_child: child_loaded --(LOAD_CHILD)--> child_loaded
t_reload_child ==
    /\ state = "child_loaded"
    /\ state' = "child_loaded"
    /\ parent_blueprint' = parent_blueprint
    /\ parent_path' = parent_path
    /\ child_blueprint' = child_blueprint
    /\ child_path' = child_path
    /\ embeddings' = embeddings
    /\ current_embedding' = current_embedding
    /\ composed_blueprint' = composed_blueprint
    /\ validation_result' = validation_result
    /\ manifest' = manifest
    /\ export_path' = export_path
    /\ error' = error
    /\ namespace_prefix' = namespace_prefix
    /\ event_history' = Append(event_history, "LOAD_CHILD")

\* t_define_embedding: child_loaded --(DEFINE)--> defining_embedding
t_define_embedding ==
    /\ state = "child_loaded"
    /\ parent_blueprint /= NULL /\ child_blueprint /= NULL  \* gate: has_both
    /\ state' = "defining_embedding"
    /\ parent_blueprint' = parent_blueprint
    /\ parent_path' = parent_path
    /\ child_blueprint' = child_blueprint
    /\ child_path' = child_path
    /\ embeddings' = embeddings
    /\ current_embedding' = current_embedding
    /\ composed_blueprint' = composed_blueprint
    /\ validation_result' = validation_result
    /\ manifest' = manifest
    /\ export_path' = export_path
    /\ error' = error
    /\ namespace_prefix' = namespace_prefix
    /\ event_history' = Append(event_history, "DEFINE")

\* t_set_input: defining_embedding --(SET_INPUT)--> defining_embedding
t_set_input ==
    /\ state = "defining_embedding"
    /\ current_embedding /= NULL  \* gate: has_embedding
    /\ state' = "defining_embedding"
    /\ parent_blueprint' = parent_blueprint
    /\ parent_path' = parent_path
    /\ child_blueprint' = child_blueprint
    /\ child_path' = child_path
    /\ embeddings' = embeddings
    /\ current_embedding' = current_embedding
    /\ composed_blueprint' = composed_blueprint
    /\ validation_result' = validation_result
    /\ manifest' = manifest
    /\ export_path' = export_path
    /\ error' = error
    /\ namespace_prefix' = namespace_prefix
    /\ event_history' = Append(event_history, "SET_INPUT")

\* t_set_output: defining_embedding --(SET_OUTPUT)--> defining_embedding
t_set_output ==
    /\ state = "defining_embedding"
    /\ current_embedding /= NULL  \* gate: has_embedding
    /\ state' = "defining_embedding"
    /\ parent_blueprint' = parent_blueprint
    /\ parent_path' = parent_path
    /\ child_blueprint' = child_blueprint
    /\ child_path' = child_path
    /\ embeddings' = embeddings
    /\ current_embedding' = current_embedding
    /\ composed_blueprint' = composed_blueprint
    /\ validation_result' = validation_result
    /\ manifest' = manifest
    /\ export_path' = export_path
    /\ error' = error
    /\ namespace_prefix' = namespace_prefix
    /\ event_history' = Append(event_history, "SET_OUTPUT")

\* t_set_events: defining_embedding --(SET_EVENTS)--> defining_embedding
t_set_events ==
    /\ state = "defining_embedding"
    /\ current_embedding /= NULL  \* gate: has_embedding
    /\ state' = "defining_embedding"
    /\ parent_blueprint' = parent_blueprint
    /\ parent_path' = parent_path
    /\ child_blueprint' = child_blueprint
    /\ child_path' = child_path
    /\ embeddings' = embeddings
    /\ current_embedding' = current_embedding
    /\ composed_blueprint' = composed_blueprint
    /\ validation_result' = validation_result
    /\ manifest' = manifest
    /\ export_path' = export_path
    /\ error' = error
    /\ namespace_prefix' = namespace_prefix
    /\ event_history' = Append(event_history, "SET_EVENTS")

\* t_done_defining: defining_embedding --(DONE)--> embedding_ready
t_done_defining ==
    /\ state = "defining_embedding"
    /\ current_embedding /= NULL  \* gate: has_embedding
    /\ state' = "embedding_ready"
    /\ parent_blueprint' = parent_blueprint
    /\ parent_path' = parent_path
    /\ child_blueprint' = child_blueprint
    /\ child_path' = child_path
    /\ embeddings' = embeddings
    /\ current_embedding' = current_embedding
    /\ composed_blueprint' = composed_blueprint
    /\ validation_result' = validation_result
    /\ manifest' = manifest
    /\ export_path' = export_path
    /\ error' = error
    /\ namespace_prefix' = namespace_prefix
    /\ event_history' = Append(event_history, "DONE")

\* t_add_more: embedding_ready --(ADD_MORE)--> child_loaded
t_add_more ==
    /\ state = "embedding_ready"
    /\ state' = "child_loaded"
    /\ parent_blueprint' = parent_blueprint
    /\ parent_path' = parent_path
    /\ child_blueprint' = child_blueprint
    /\ child_path' = child_path
    /\ embeddings' = embeddings
    /\ current_embedding' = current_embedding
    /\ composed_blueprint' = composed_blueprint
    /\ validation_result' = validation_result
    /\ manifest' = manifest
    /\ export_path' = export_path
    /\ error' = error
    /\ namespace_prefix' = namespace_prefix
    /\ event_history' = Append(event_history, "ADD_MORE")

\* t_compose: embedding_ready --(COMPOSE)--> composed
t_compose ==
    /\ state = "embedding_ready"
    /\ embeddings /= NULL /\ Len(embeddings) > 0  \* gate: has_embeddings
    /\ state' = "composed"
    /\ parent_blueprint' = parent_blueprint
    /\ parent_path' = parent_path
    /\ child_blueprint' = child_blueprint
    /\ child_path' = child_path
    /\ embeddings' = embeddings
    /\ current_embedding' = current_embedding
    /\ composed_blueprint' = composed_blueprint
    /\ validation_result' = validation_result
    /\ manifest' = manifest
    /\ export_path' = export_path
    /\ error' = error
    /\ namespace_prefix' = namespace_prefix
    /\ event_history' = Append(event_history, "COMPOSE")

\* t_quick_compose: child_loaded --(QUICK_COMPOSE)--> composed
t_quick_compose ==
    /\ state = "child_loaded"
    /\ parent_blueprint /= NULL /\ child_blueprint /= NULL  \* gate: has_both
    /\ state' = "composed"
    /\ parent_blueprint' = parent_blueprint
    /\ parent_path' = parent_path
    /\ child_blueprint' = child_blueprint
    /\ child_path' = child_path
    /\ embeddings' = embeddings
    /\ current_embedding' = current_embedding
    /\ composed_blueprint' = composed_blueprint
    /\ validation_result' = validation_result
    /\ manifest' = manifest
    /\ export_path' = export_path
    /\ error' = error
    /\ namespace_prefix' = namespace_prefix
    /\ event_history' = Append(event_history, "QUICK_COMPOSE")

\* t_validate: composed --(VALIDATE)--> validated
t_validate ==
    /\ state = "composed"
    /\ composed_blueprint /= NULL  \* gate: has_composed
    /\ state' = "validated"
    /\ parent_blueprint' = parent_blueprint
    /\ parent_path' = parent_path
    /\ child_blueprint' = child_blueprint
    /\ child_path' = child_path
    /\ embeddings' = embeddings
    /\ current_embedding' = current_embedding
    /\ composed_blueprint' = composed_blueprint
    /\ validation_result' = validation_result
    /\ manifest' = manifest
    /\ export_path' = export_path
    /\ error' = error
    /\ namespace_prefix' = namespace_prefix
    /\ event_history' = Append(event_history, "VALIDATE")

\* t_flatten: composed --(FLATTEN)--> composed
t_flatten ==
    /\ state = "composed"
    /\ composed_blueprint /= NULL  \* gate: has_composed
    /\ state' = "composed"
    /\ parent_blueprint' = parent_blueprint
    /\ parent_path' = parent_path
    /\ child_blueprint' = child_blueprint
    /\ child_path' = child_path
    /\ embeddings' = embeddings
    /\ current_embedding' = current_embedding
    /\ composed_blueprint' = composed_blueprint
    /\ validation_result' = validation_result
    /\ manifest' = manifest
    /\ export_path' = export_path
    /\ error' = error
    /\ namespace_prefix' = namespace_prefix
    /\ event_history' = Append(event_history, "FLATTEN")

\* t_export: composed --(EXPORT)--> composed
t_export ==
    /\ state = "composed"
    /\ composed_blueprint /= NULL  \* gate: has_composed
    /\ state' = "composed"
    /\ parent_blueprint' = parent_blueprint
    /\ parent_path' = parent_path
    /\ child_blueprint' = child_blueprint
    /\ child_path' = child_path
    /\ embeddings' = embeddings
    /\ current_embedding' = current_embedding
    /\ composed_blueprint' = composed_blueprint
    /\ validation_result' = validation_result
    /\ manifest' = manifest
    /\ export_path' = export_path
    /\ error' = error
    /\ namespace_prefix' = namespace_prefix
    /\ event_history' = Append(event_history, "EXPORT")

\* t_export_after_validate: validated --(EXPORT)--> validated
t_export_after_validate ==
    /\ state = "validated"
    /\ composed_blueprint /= NULL  \* gate: has_composed
    /\ state' = "validated"
    /\ parent_blueprint' = parent_blueprint
    /\ parent_path' = parent_path
    /\ child_blueprint' = child_blueprint
    /\ child_path' = child_path
    /\ embeddings' = embeddings
    /\ current_embedding' = current_embedding
    /\ composed_blueprint' = composed_blueprint
    /\ validation_result' = validation_result
    /\ manifest' = manifest
    /\ export_path' = export_path
    /\ error' = error
    /\ namespace_prefix' = namespace_prefix
    /\ event_history' = Append(event_history, "EXPORT")

\* t_save_manifest: embedding_ready --(SAVE_MANIFEST)--> embedding_ready
t_save_manifest ==
    /\ state = "embedding_ready"
    /\ embeddings /= NULL /\ Len(embeddings) > 0  \* gate: has_embeddings
    /\ state' = "embedding_ready"
    /\ parent_blueprint' = parent_blueprint
    /\ parent_path' = parent_path
    /\ child_blueprint' = child_blueprint
    /\ child_path' = child_path
    /\ embeddings' = embeddings
    /\ current_embedding' = current_embedding
    /\ composed_blueprint' = composed_blueprint
    /\ validation_result' = validation_result
    /\ manifest' = manifest
    /\ export_path' = export_path
    /\ error' = error
    /\ namespace_prefix' = namespace_prefix
    /\ event_history' = Append(event_history, "SAVE_MANIFEST")

\* t_revalidate: validated --(VALIDATE)--> validated
t_revalidate ==
    /\ state = "validated"
    /\ composed_blueprint /= NULL  \* gate: has_composed
    /\ state' = "validated"
    /\ parent_blueprint' = parent_blueprint
    /\ parent_path' = parent_path
    /\ child_blueprint' = child_blueprint
    /\ child_path' = child_path
    /\ embeddings' = embeddings
    /\ current_embedding' = current_embedding
    /\ composed_blueprint' = composed_blueprint
    /\ validation_result' = validation_result
    /\ manifest' = manifest
    /\ export_path' = export_path
    /\ error' = error
    /\ namespace_prefix' = namespace_prefix
    /\ event_history' = Append(event_history, "VALIDATE")

\* t_back_to_composed: validated --(BACK)--> composed
t_back_to_composed ==
    /\ state = "validated"
    /\ state' = "composed"
    /\ parent_blueprint' = parent_blueprint
    /\ parent_path' = parent_path
    /\ child_blueprint' = child_blueprint
    /\ child_path' = child_path
    /\ embeddings' = embeddings
    /\ current_embedding' = current_embedding
    /\ composed_blueprint' = composed_blueprint
    /\ validation_result' = validation_result
    /\ manifest' = manifest
    /\ export_path' = export_path
    /\ error' = error
    /\ namespace_prefix' = namespace_prefix
    /\ event_history' = Append(event_history, "BACK")

\* t_back_to_embedding: composed --(BACK)--> embedding_ready
t_back_to_embedding ==
    /\ state = "composed"
    /\ state' = "embedding_ready"
    /\ parent_blueprint' = parent_blueprint
    /\ parent_path' = parent_path
    /\ child_blueprint' = child_blueprint
    /\ child_path' = child_path
    /\ embeddings' = embeddings
    /\ current_embedding' = current_embedding
    /\ composed_blueprint' = composed_blueprint
    /\ validation_result' = validation_result
    /\ manifest' = manifest
    /\ export_path' = export_path
    /\ error' = error
    /\ namespace_prefix' = namespace_prefix
    /\ event_history' = Append(event_history, "BACK")

\* t_back_from_defining: defining_embedding --(CANCEL)--> child_loaded
t_back_from_defining ==
    /\ state = "defining_embedding"
    /\ state' = "child_loaded"
    /\ parent_blueprint' = parent_blueprint
    /\ parent_path' = parent_path
    /\ child_blueprint' = child_blueprint
    /\ child_path' = child_path
    /\ embeddings' = embeddings
    /\ current_embedding' = current_embedding
    /\ composed_blueprint' = composed_blueprint
    /\ validation_result' = validation_result
    /\ manifest' = manifest
    /\ export_path' = export_path
    /\ error' = error
    /\ namespace_prefix' = namespace_prefix
    /\ event_history' = Append(event_history, "CANCEL")

\* t_reset: composed --(RESET)--> idle
t_reset ==
    /\ state = "composed"
    /\ state' = "idle"
    /\ parent_blueprint' = parent_blueprint
    /\ parent_path' = parent_path
    /\ child_blueprint' = child_blueprint
    /\ child_path' = child_path
    /\ embeddings' = embeddings
    /\ current_embedding' = current_embedding
    /\ composed_blueprint' = composed_blueprint
    /\ validation_result' = validation_result
    /\ manifest' = manifest
    /\ export_path' = export_path
    /\ error' = error
    /\ namespace_prefix' = namespace_prefix
    /\ event_history' = Append(event_history, "RESET")

\* t_reset_from_validated: validated --(RESET)--> idle
t_reset_from_validated ==
    /\ state = "validated"
    /\ state' = "idle"
    /\ parent_blueprint' = parent_blueprint
    /\ parent_path' = parent_path
    /\ child_blueprint' = child_blueprint
    /\ child_path' = child_path
    /\ embeddings' = embeddings
    /\ current_embedding' = current_embedding
    /\ composed_blueprint' = composed_blueprint
    /\ validation_result' = validation_result
    /\ manifest' = manifest
    /\ export_path' = export_path
    /\ error' = error
    /\ namespace_prefix' = namespace_prefix
    /\ event_history' = Append(event_history, "RESET")

\* t_clear_from_parent: parent_loaded --(CLEAR)--> idle
t_clear_from_parent ==
    /\ state = "parent_loaded"
    /\ state' = "idle"
    /\ parent_blueprint' = parent_blueprint
    /\ parent_path' = parent_path
    /\ child_blueprint' = child_blueprint
    /\ child_path' = child_path
    /\ embeddings' = embeddings
    /\ current_embedding' = current_embedding
    /\ composed_blueprint' = composed_blueprint
    /\ validation_result' = validation_result
    /\ manifest' = manifest
    /\ export_path' = export_path
    /\ error' = error
    /\ namespace_prefix' = namespace_prefix
    /\ event_history' = Append(event_history, "CLEAR")

\* t_clear_from_child: child_loaded --(CLEAR)--> idle
t_clear_from_child ==
    /\ state = "child_loaded"
    /\ state' = "idle"
    /\ parent_blueprint' = parent_blueprint
    /\ parent_path' = parent_path
    /\ child_blueprint' = child_blueprint
    /\ child_path' = child_path
    /\ embeddings' = embeddings
    /\ current_embedding' = current_embedding
    /\ composed_blueprint' = composed_blueprint
    /\ validation_result' = validation_result
    /\ manifest' = manifest
    /\ export_path' = export_path
    /\ error' = error
    /\ namespace_prefix' = namespace_prefix
    /\ event_history' = Append(event_history, "CLEAR")

\* t_error_recover: error --(CLEAR)--> idle
t_error_recover ==
    /\ state = "error"
    /\ state' = "idle"
    /\ parent_blueprint' = parent_blueprint
    /\ parent_path' = parent_path
    /\ child_blueprint' = child_blueprint
    /\ child_path' = child_path
    /\ embeddings' = embeddings
    /\ current_embedding' = current_embedding
    /\ composed_blueprint' = composed_blueprint
    /\ validation_result' = validation_result
    /\ manifest' = manifest
    /\ export_path' = export_path
    /\ error' = error
    /\ namespace_prefix' = namespace_prefix
    /\ event_history' = Append(event_history, "CLEAR")

\* t_load_error: * --(LOAD_FAILED)--> error
t_load_error ==
    /\ TRUE  \* from any state
    /\ state' = "error"
    /\ parent_blueprint' = parent_blueprint
    /\ parent_path' = parent_path
    /\ child_blueprint' = child_blueprint
    /\ child_path' = child_path
    /\ embeddings' = embeddings
    /\ current_embedding' = current_embedding
    /\ composed_blueprint' = composed_blueprint
    /\ validation_result' = validation_result
    /\ manifest' = manifest
    /\ export_path' = export_path
    /\ error' = error
    /\ namespace_prefix' = namespace_prefix
    /\ event_history' = Append(event_history, "LOAD_FAILED")

\* Next state relation
Next ==
    \/ t_load_parent_from_idle
    \/ t_load_manifest
    \/ t_load_child
    \/ t_reload_parent
    \/ t_reload_child
    \/ t_define_embedding
    \/ t_set_input
    \/ t_set_output
    \/ t_set_events
    \/ t_done_defining
    \/ t_add_more
    \/ t_compose
    \/ t_quick_compose
    \/ t_validate
    \/ t_flatten
    \/ t_export
    \/ t_export_after_validate
    \/ t_save_manifest
    \/ t_revalidate
    \/ t_back_to_composed
    \/ t_back_to_embedding
    \/ t_back_from_defining
    \/ t_reset
    \/ t_reset_from_validated
    \/ t_clear_from_parent
    \/ t_clear_from_child
    \/ t_error_recover
    \/ t_load_error

\* Specification
Spec == Init /\ [][Next]_vars

\* Safety: Always in valid state
AlwaysValidState == state \in States

\* Liveness: No deadlock (always can make progress)
NoDeadlock == <>(ENABLED Next)

\* Reachability: Entry state is reachable
EntryReachable == state = "idle"

=============================================================================