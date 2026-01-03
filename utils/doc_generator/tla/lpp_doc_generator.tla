---------------------------- MODULE lpp_doc_generator ----------------------------
\* L++ Blueprint: L++ Documentation Generator
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
States == {"idle", "loaded", "generating", "assembling", "exporting", "done", "error"}

Events == {"ASSEMBLE", "BACK", "CLEAR", "DONE", "EXPORT", "FORMAT_HTML", "FORMAT_JSON", "FORMAT_MARKDOWN", "GENERATE", "GENERATE_FULL", "LOAD", "LOAD_FAILED", "TOGGLE_CONTEXT", "TOGGLE_MERMAID", "TOGGLE_QUICKSTART", "TOGGLE_TABLES", "UNLOAD"}

TerminalStates == {}

VARIABLES
    state,           \* Current state
    blueprint,           \* The loaded Blueprint object
    blueprint_path,           \* Path to the loaded blueprint
    blueprint_name,           \* Blueprint name
    blueprint_id,           \* Blueprint ID
    output_format,           \* Output format: markdown | html | json
    output_path,           \* Path where docs were exported
    metadata,           \* Extracted metadata (name, version, desc)
    overview_section,           \* Generated overview section
    mermaid_section,           \* Generated mermaid diagram
    states_section,           \* Generated states documentation
    transitions_section,           \* Generated transitions table
    gates_section,           \* Generated gates documentation
    actions_section,           \* Generated actions documentation
    context_section,           \* Generated context schema docs
    events_section,           \* Generated events documentation
    quickstart_section,           \* Generated quick-start guide
    assembled_doc,           \* Fully assembled documentation
    include_mermaid,           \* Include mermaid diagram
    include_tables,           \* Include detailed tables
    include_quickstart,           \* Include quick-start guide
    include_context,           \* Include context schema docs
    error,           \* Error message if any
    event_history    \* Trace of events

vars == <<state, blueprint, blueprint_path, blueprint_name, blueprint_id, output_format, output_path, metadata, overview_section, mermaid_section, states_section, transitions_section, gates_section, actions_section, context_section, events_section, quickstart_section, assembled_doc, include_mermaid, include_tables, include_quickstart, include_context, error, event_history>>

\* Type invariant - structural correctness
TypeInvariant ==
    /\ state \in States
    /\ TRUE  \* blueprint: any string or NULL
    /\ TRUE  \* blueprint_path: any string or NULL
    /\ TRUE  \* blueprint_name: any string or NULL
    /\ TRUE  \* blueprint_id: any string or NULL
    /\ TRUE  \* output_format: any string or NULL
    /\ TRUE  \* output_path: any string or NULL
    /\ TRUE  \* metadata: any string or NULL
    /\ TRUE  \* overview_section: any string or NULL
    /\ TRUE  \* mermaid_section: any string or NULL
    /\ TRUE  \* states_section: any string or NULL
    /\ TRUE  \* transitions_section: any string or NULL
    /\ TRUE  \* gates_section: any string or NULL
    /\ TRUE  \* actions_section: any string or NULL
    /\ TRUE  \* context_section: any string or NULL
    /\ TRUE  \* events_section: any string or NULL
    /\ TRUE  \* quickstart_section: any string or NULL
    /\ TRUE  \* assembled_doc: any string or NULL
    /\ (include_mermaid \in BOOLEAN) \/ (include_mermaid = NULL)
    /\ (include_tables \in BOOLEAN) \/ (include_tables = NULL)
    /\ (include_quickstart \in BOOLEAN) \/ (include_quickstart = NULL)
    /\ (include_context \in BOOLEAN) \/ (include_context = NULL)
    /\ TRUE  \* error: any string or NULL

\* State constraint - limits TLC exploration depth
StateConstraint ==
    /\ Len(event_history) <= MAX_HISTORY

\* Initial state
Init ==
    /\ state = "idle"
    /\ blueprint = NULL
    /\ blueprint_path = NULL
    /\ blueprint_name = NULL
    /\ blueprint_id = NULL
    /\ output_format = NULL
    /\ output_path = NULL
    /\ metadata = NULL
    /\ overview_section = NULL
    /\ mermaid_section = NULL
    /\ states_section = NULL
    /\ transitions_section = NULL
    /\ gates_section = NULL
    /\ actions_section = NULL
    /\ context_section = NULL
    /\ events_section = NULL
    /\ quickstart_section = NULL
    /\ assembled_doc = NULL
    /\ include_mermaid = NULL
    /\ include_tables = NULL
    /\ include_quickstart = NULL
    /\ include_context = NULL
    /\ error = NULL
    /\ event_history = <<>>

\* Transitions
\* t_load: idle --(LOAD)--> loaded
t_load ==
    /\ state = "idle"
    /\ blueprint = NULL  \* gate: no_blueprint
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ metadata' = metadata
    /\ overview_section' = overview_section
    /\ mermaid_section' = mermaid_section
    /\ states_section' = states_section
    /\ transitions_section' = transitions_section
    /\ gates_section' = gates_section
    /\ actions_section' = actions_section
    /\ context_section' = context_section
    /\ events_section' = events_section
    /\ quickstart_section' = quickstart_section
    /\ assembled_doc' = assembled_doc
    /\ include_mermaid' = include_mermaid
    /\ include_tables' = include_tables
    /\ include_quickstart' = include_quickstart
    /\ include_context' = include_context
    /\ error' = error
    /\ event_history' = Append(event_history, "LOAD")

\* t_load_error: idle --(LOAD_FAILED)--> error
t_load_error ==
    /\ state = "idle"
    /\ state' = "error"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ metadata' = metadata
    /\ overview_section' = overview_section
    /\ mermaid_section' = mermaid_section
    /\ states_section' = states_section
    /\ transitions_section' = transitions_section
    /\ gates_section' = gates_section
    /\ actions_section' = actions_section
    /\ context_section' = context_section
    /\ events_section' = events_section
    /\ quickstart_section' = quickstart_section
    /\ assembled_doc' = assembled_doc
    /\ include_mermaid' = include_mermaid
    /\ include_tables' = include_tables
    /\ include_quickstart' = include_quickstart
    /\ include_context' = include_context
    /\ error' = error
    /\ event_history' = Append(event_history, "LOAD_FAILED")

\* t_reload: loaded --(LOAD)--> loaded
t_reload ==
    /\ state = "loaded"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ metadata' = metadata
    /\ overview_section' = overview_section
    /\ mermaid_section' = mermaid_section
    /\ states_section' = states_section
    /\ transitions_section' = transitions_section
    /\ gates_section' = gates_section
    /\ actions_section' = actions_section
    /\ context_section' = context_section
    /\ events_section' = events_section
    /\ quickstart_section' = quickstart_section
    /\ assembled_doc' = assembled_doc
    /\ include_mermaid' = include_mermaid
    /\ include_tables' = include_tables
    /\ include_quickstart' = include_quickstart
    /\ include_context' = include_context
    /\ error' = error
    /\ event_history' = Append(event_history, "LOAD")

\* t_reload_from_done: done --(LOAD)--> loaded
t_reload_from_done ==
    /\ state = "done"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ metadata' = metadata
    /\ overview_section' = overview_section
    /\ mermaid_section' = mermaid_section
    /\ states_section' = states_section
    /\ transitions_section' = transitions_section
    /\ gates_section' = gates_section
    /\ actions_section' = actions_section
    /\ context_section' = context_section
    /\ events_section' = events_section
    /\ quickstart_section' = quickstart_section
    /\ assembled_doc' = assembled_doc
    /\ include_mermaid' = include_mermaid
    /\ include_tables' = include_tables
    /\ include_quickstart' = include_quickstart
    /\ include_context' = include_context
    /\ error' = error
    /\ event_history' = Append(event_history, "LOAD")

\* t_set_markdown: loaded --(FORMAT_MARKDOWN)--> loaded
t_set_markdown ==
    /\ state = "loaded"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ metadata' = metadata
    /\ overview_section' = overview_section
    /\ mermaid_section' = mermaid_section
    /\ states_section' = states_section
    /\ transitions_section' = transitions_section
    /\ gates_section' = gates_section
    /\ actions_section' = actions_section
    /\ context_section' = context_section
    /\ events_section' = events_section
    /\ quickstart_section' = quickstart_section
    /\ assembled_doc' = assembled_doc
    /\ include_mermaid' = include_mermaid
    /\ include_tables' = include_tables
    /\ include_quickstart' = include_quickstart
    /\ include_context' = include_context
    /\ error' = error
    /\ event_history' = Append(event_history, "FORMAT_MARKDOWN")

\* t_set_html: loaded --(FORMAT_HTML)--> loaded
t_set_html ==
    /\ state = "loaded"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ metadata' = metadata
    /\ overview_section' = overview_section
    /\ mermaid_section' = mermaid_section
    /\ states_section' = states_section
    /\ transitions_section' = transitions_section
    /\ gates_section' = gates_section
    /\ actions_section' = actions_section
    /\ context_section' = context_section
    /\ events_section' = events_section
    /\ quickstart_section' = quickstart_section
    /\ assembled_doc' = assembled_doc
    /\ include_mermaid' = include_mermaid
    /\ include_tables' = include_tables
    /\ include_quickstart' = include_quickstart
    /\ include_context' = include_context
    /\ error' = error
    /\ event_history' = Append(event_history, "FORMAT_HTML")

\* t_set_json: loaded --(FORMAT_JSON)--> loaded
t_set_json ==
    /\ state = "loaded"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ metadata' = metadata
    /\ overview_section' = overview_section
    /\ mermaid_section' = mermaid_section
    /\ states_section' = states_section
    /\ transitions_section' = transitions_section
    /\ gates_section' = gates_section
    /\ actions_section' = actions_section
    /\ context_section' = context_section
    /\ events_section' = events_section
    /\ quickstart_section' = quickstart_section
    /\ assembled_doc' = assembled_doc
    /\ include_mermaid' = include_mermaid
    /\ include_tables' = include_tables
    /\ include_quickstart' = include_quickstart
    /\ include_context' = include_context
    /\ error' = error
    /\ event_history' = Append(event_history, "FORMAT_JSON")

\* t_toggle_mermaid: loaded --(TOGGLE_MERMAID)--> loaded
t_toggle_mermaid ==
    /\ state = "loaded"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ metadata' = metadata
    /\ overview_section' = overview_section
    /\ mermaid_section' = mermaid_section
    /\ states_section' = states_section
    /\ transitions_section' = transitions_section
    /\ gates_section' = gates_section
    /\ actions_section' = actions_section
    /\ context_section' = context_section
    /\ events_section' = events_section
    /\ quickstart_section' = quickstart_section
    /\ assembled_doc' = assembled_doc
    /\ include_mermaid' = include_mermaid
    /\ include_tables' = include_tables
    /\ include_quickstart' = include_quickstart
    /\ include_context' = include_context
    /\ error' = error
    /\ event_history' = Append(event_history, "TOGGLE_MERMAID")

\* t_toggle_tables: loaded --(TOGGLE_TABLES)--> loaded
t_toggle_tables ==
    /\ state = "loaded"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ metadata' = metadata
    /\ overview_section' = overview_section
    /\ mermaid_section' = mermaid_section
    /\ states_section' = states_section
    /\ transitions_section' = transitions_section
    /\ gates_section' = gates_section
    /\ actions_section' = actions_section
    /\ context_section' = context_section
    /\ events_section' = events_section
    /\ quickstart_section' = quickstart_section
    /\ assembled_doc' = assembled_doc
    /\ include_mermaid' = include_mermaid
    /\ include_tables' = include_tables
    /\ include_quickstart' = include_quickstart
    /\ include_context' = include_context
    /\ error' = error
    /\ event_history' = Append(event_history, "TOGGLE_TABLES")

\* t_toggle_quickstart: loaded --(TOGGLE_QUICKSTART)--> loaded
t_toggle_quickstart ==
    /\ state = "loaded"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ metadata' = metadata
    /\ overview_section' = overview_section
    /\ mermaid_section' = mermaid_section
    /\ states_section' = states_section
    /\ transitions_section' = transitions_section
    /\ gates_section' = gates_section
    /\ actions_section' = actions_section
    /\ context_section' = context_section
    /\ events_section' = events_section
    /\ quickstart_section' = quickstart_section
    /\ assembled_doc' = assembled_doc
    /\ include_mermaid' = include_mermaid
    /\ include_tables' = include_tables
    /\ include_quickstart' = include_quickstart
    /\ include_context' = include_context
    /\ error' = error
    /\ event_history' = Append(event_history, "TOGGLE_QUICKSTART")

\* t_toggle_context: loaded --(TOGGLE_CONTEXT)--> loaded
t_toggle_context ==
    /\ state = "loaded"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ metadata' = metadata
    /\ overview_section' = overview_section
    /\ mermaid_section' = mermaid_section
    /\ states_section' = states_section
    /\ transitions_section' = transitions_section
    /\ gates_section' = gates_section
    /\ actions_section' = actions_section
    /\ context_section' = context_section
    /\ events_section' = events_section
    /\ quickstart_section' = quickstart_section
    /\ assembled_doc' = assembled_doc
    /\ include_mermaid' = include_mermaid
    /\ include_tables' = include_tables
    /\ include_quickstart' = include_quickstart
    /\ include_context' = include_context
    /\ error' = error
    /\ event_history' = Append(event_history, "TOGGLE_CONTEXT")

\* t_start_generate: loaded --(GENERATE)--> generating
t_start_generate ==
    /\ state = "loaded"
    /\ blueprint /= NULL  \* gate: has_blueprint
    /\ state' = "generating"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ metadata' = metadata
    /\ overview_section' = overview_section
    /\ mermaid_section' = mermaid_section
    /\ states_section' = states_section
    /\ transitions_section' = transitions_section
    /\ gates_section' = gates_section
    /\ actions_section' = actions_section
    /\ context_section' = context_section
    /\ events_section' = events_section
    /\ quickstart_section' = quickstart_section
    /\ assembled_doc' = assembled_doc
    /\ include_mermaid' = include_mermaid
    /\ include_tables' = include_tables
    /\ include_quickstart' = include_quickstart
    /\ include_context' = include_context
    /\ error' = error
    /\ event_history' = Append(event_history, "GENERATE")

\* t_assemble_markdown: generating --(ASSEMBLE)--> assembling
t_assemble_markdown ==
    /\ state = "generating"
    /\ output_format = "markdown"  \* gate: format_is_markdown
    /\ state' = "assembling"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ metadata' = metadata
    /\ overview_section' = overview_section
    /\ mermaid_section' = mermaid_section
    /\ states_section' = states_section
    /\ transitions_section' = transitions_section
    /\ gates_section' = gates_section
    /\ actions_section' = actions_section
    /\ context_section' = context_section
    /\ events_section' = events_section
    /\ quickstart_section' = quickstart_section
    /\ assembled_doc' = assembled_doc
    /\ include_mermaid' = include_mermaid
    /\ include_tables' = include_tables
    /\ include_quickstart' = include_quickstart
    /\ include_context' = include_context
    /\ error' = error
    /\ event_history' = Append(event_history, "ASSEMBLE")

\* t_assemble_html: generating --(ASSEMBLE)--> assembling
t_assemble_html ==
    /\ state = "generating"
    /\ output_format = "html"  \* gate: format_is_html
    /\ state' = "assembling"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ metadata' = metadata
    /\ overview_section' = overview_section
    /\ mermaid_section' = mermaid_section
    /\ states_section' = states_section
    /\ transitions_section' = transitions_section
    /\ gates_section' = gates_section
    /\ actions_section' = actions_section
    /\ context_section' = context_section
    /\ events_section' = events_section
    /\ quickstart_section' = quickstart_section
    /\ assembled_doc' = assembled_doc
    /\ include_mermaid' = include_mermaid
    /\ include_tables' = include_tables
    /\ include_quickstart' = include_quickstart
    /\ include_context' = include_context
    /\ error' = error
    /\ event_history' = Append(event_history, "ASSEMBLE")

\* t_assemble_json: generating --(ASSEMBLE)--> assembling
t_assemble_json ==
    /\ state = "generating"
    /\ output_format = "json"  \* gate: format_is_json
    /\ state' = "assembling"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ metadata' = metadata
    /\ overview_section' = overview_section
    /\ mermaid_section' = mermaid_section
    /\ states_section' = states_section
    /\ transitions_section' = transitions_section
    /\ gates_section' = gates_section
    /\ actions_section' = actions_section
    /\ context_section' = context_section
    /\ events_section' = events_section
    /\ quickstart_section' = quickstart_section
    /\ assembled_doc' = assembled_doc
    /\ include_mermaid' = include_mermaid
    /\ include_tables' = include_tables
    /\ include_quickstart' = include_quickstart
    /\ include_context' = include_context
    /\ error' = error
    /\ event_history' = Append(event_history, "ASSEMBLE")

\* t_export: assembling --(EXPORT)--> exporting
t_export ==
    /\ state = "assembling"
    /\ assembled_doc /= NULL  \* gate: has_assembled_doc
    /\ state' = "exporting"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ metadata' = metadata
    /\ overview_section' = overview_section
    /\ mermaid_section' = mermaid_section
    /\ states_section' = states_section
    /\ transitions_section' = transitions_section
    /\ gates_section' = gates_section
    /\ actions_section' = actions_section
    /\ context_section' = context_section
    /\ events_section' = events_section
    /\ quickstart_section' = quickstart_section
    /\ assembled_doc' = assembled_doc
    /\ include_mermaid' = include_mermaid
    /\ include_tables' = include_tables
    /\ include_quickstart' = include_quickstart
    /\ include_context' = include_context
    /\ error' = error
    /\ event_history' = Append(event_history, "EXPORT")

\* t_finish: exporting --(DONE)--> done
t_finish ==
    /\ state = "exporting"
    /\ state' = "done"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ metadata' = metadata
    /\ overview_section' = overview_section
    /\ mermaid_section' = mermaid_section
    /\ states_section' = states_section
    /\ transitions_section' = transitions_section
    /\ gates_section' = gates_section
    /\ actions_section' = actions_section
    /\ context_section' = context_section
    /\ events_section' = events_section
    /\ quickstart_section' = quickstart_section
    /\ assembled_doc' = assembled_doc
    /\ include_mermaid' = include_mermaid
    /\ include_tables' = include_tables
    /\ include_quickstart' = include_quickstart
    /\ include_context' = include_context
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_generate_full: loaded --(GENERATE_FULL)--> done
t_generate_full ==
    /\ state = "loaded"
    /\ blueprint /= NULL  \* gate: has_blueprint
    /\ state' = "done"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ metadata' = metadata
    /\ overview_section' = overview_section
    /\ mermaid_section' = mermaid_section
    /\ states_section' = states_section
    /\ transitions_section' = transitions_section
    /\ gates_section' = gates_section
    /\ actions_section' = actions_section
    /\ context_section' = context_section
    /\ events_section' = events_section
    /\ quickstart_section' = quickstart_section
    /\ assembled_doc' = assembled_doc
    /\ include_mermaid' = include_mermaid
    /\ include_tables' = include_tables
    /\ include_quickstart' = include_quickstart
    /\ include_context' = include_context
    /\ error' = error
    /\ event_history' = Append(event_history, "GENERATE_FULL")

\* t_back_to_loaded: generating --(BACK)--> loaded
t_back_to_loaded ==
    /\ state = "generating"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ metadata' = metadata
    /\ overview_section' = overview_section
    /\ mermaid_section' = mermaid_section
    /\ states_section' = states_section
    /\ transitions_section' = transitions_section
    /\ gates_section' = gates_section
    /\ actions_section' = actions_section
    /\ context_section' = context_section
    /\ events_section' = events_section
    /\ quickstart_section' = quickstart_section
    /\ assembled_doc' = assembled_doc
    /\ include_mermaid' = include_mermaid
    /\ include_tables' = include_tables
    /\ include_quickstart' = include_quickstart
    /\ include_context' = include_context
    /\ error' = error
    /\ event_history' = Append(event_history, "BACK")

\* t_back_from_assembling: assembling --(BACK)--> loaded
t_back_from_assembling ==
    /\ state = "assembling"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ metadata' = metadata
    /\ overview_section' = overview_section
    /\ mermaid_section' = mermaid_section
    /\ states_section' = states_section
    /\ transitions_section' = transitions_section
    /\ gates_section' = gates_section
    /\ actions_section' = actions_section
    /\ context_section' = context_section
    /\ events_section' = events_section
    /\ quickstart_section' = quickstart_section
    /\ assembled_doc' = assembled_doc
    /\ include_mermaid' = include_mermaid
    /\ include_tables' = include_tables
    /\ include_quickstart' = include_quickstart
    /\ include_context' = include_context
    /\ error' = error
    /\ event_history' = Append(event_history, "BACK")

\* t_back_from_done: done --(BACK)--> loaded
t_back_from_done ==
    /\ state = "done"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ metadata' = metadata
    /\ overview_section' = overview_section
    /\ mermaid_section' = mermaid_section
    /\ states_section' = states_section
    /\ transitions_section' = transitions_section
    /\ gates_section' = gates_section
    /\ actions_section' = actions_section
    /\ context_section' = context_section
    /\ events_section' = events_section
    /\ quickstart_section' = quickstart_section
    /\ assembled_doc' = assembled_doc
    /\ include_mermaid' = include_mermaid
    /\ include_tables' = include_tables
    /\ include_quickstart' = include_quickstart
    /\ include_context' = include_context
    /\ error' = error
    /\ event_history' = Append(event_history, "BACK")

\* t_unload: loaded --(UNLOAD)--> idle
t_unload ==
    /\ state = "loaded"
    /\ state' = "idle"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ metadata' = metadata
    /\ overview_section' = overview_section
    /\ mermaid_section' = mermaid_section
    /\ states_section' = states_section
    /\ transitions_section' = transitions_section
    /\ gates_section' = gates_section
    /\ actions_section' = actions_section
    /\ context_section' = context_section
    /\ events_section' = events_section
    /\ quickstart_section' = quickstart_section
    /\ assembled_doc' = assembled_doc
    /\ include_mermaid' = include_mermaid
    /\ include_tables' = include_tables
    /\ include_quickstart' = include_quickstart
    /\ include_context' = include_context
    /\ error' = error
    /\ event_history' = Append(event_history, "UNLOAD")

\* t_unload_from_done: done --(UNLOAD)--> idle
t_unload_from_done ==
    /\ state = "done"
    /\ state' = "idle"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ metadata' = metadata
    /\ overview_section' = overview_section
    /\ mermaid_section' = mermaid_section
    /\ states_section' = states_section
    /\ transitions_section' = transitions_section
    /\ gates_section' = gates_section
    /\ actions_section' = actions_section
    /\ context_section' = context_section
    /\ events_section' = events_section
    /\ quickstart_section' = quickstart_section
    /\ assembled_doc' = assembled_doc
    /\ include_mermaid' = include_mermaid
    /\ include_tables' = include_tables
    /\ include_quickstart' = include_quickstart
    /\ include_context' = include_context
    /\ error' = error
    /\ event_history' = Append(event_history, "UNLOAD")

\* t_recover: error --(CLEAR)--> idle
t_recover ==
    /\ state = "error"
    /\ state' = "idle"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ metadata' = metadata
    /\ overview_section' = overview_section
    /\ mermaid_section' = mermaid_section
    /\ states_section' = states_section
    /\ transitions_section' = transitions_section
    /\ gates_section' = gates_section
    /\ actions_section' = actions_section
    /\ context_section' = context_section
    /\ events_section' = events_section
    /\ quickstart_section' = quickstart_section
    /\ assembled_doc' = assembled_doc
    /\ include_mermaid' = include_mermaid
    /\ include_tables' = include_tables
    /\ include_quickstart' = include_quickstart
    /\ include_context' = include_context
    /\ error' = error
    /\ event_history' = Append(event_history, "CLEAR")

\* Next state relation
Next ==
    \/ t_load
    \/ t_load_error
    \/ t_reload
    \/ t_reload_from_done
    \/ t_set_markdown
    \/ t_set_html
    \/ t_set_json
    \/ t_toggle_mermaid
    \/ t_toggle_tables
    \/ t_toggle_quickstart
    \/ t_toggle_context
    \/ t_start_generate
    \/ t_assemble_markdown
    \/ t_assemble_html
    \/ t_assemble_json
    \/ t_export
    \/ t_finish
    \/ t_generate_full
    \/ t_back_to_loaded
    \/ t_back_from_assembling
    \/ t_back_from_done
    \/ t_unload
    \/ t_unload_from_done
    \/ t_recover

\* Specification
Spec == Init /\ [][Next]_vars

\* Safety: Always in valid state
AlwaysValidState == state \in States

\* Liveness: No deadlock (always can make progress)
NoDeadlock == <>(ENABLED Next)

\* Reachability: Entry state is reachable
EntryReachable == state = "idle"

=============================================================================