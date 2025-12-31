---------------------------- MODULE llm_schema_assistant ----------------------------
\* L++ Blueprint: L++ LLM Schema Assistant
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
States == {"init", "ready", "querying", "error"}

Events == {"CLEAR", "CONFIGURE", "DONE", "EXPLAIN", "LOAD", "QUERY", "RETRY", "SET_KEY", "START", "SUGGEST", "VALIDATE"}

TerminalStates == {}

VARIABLES
    state,           \* Current state
    api_key,           \* OpenAI-compatible API key
    api_base,           \* API base URL (OpenAI v1 compatible)
    model,           \* Model identifier (e.g., gpt-4o-mini)
    schema_content,           \* Loaded L++ schema specification
    blueprint,           \* Currently loaded blueprint
    blueprint_path,           \* Path to loaded blueprint
    conversation,           \* Conversation history [{role, content}]
    last_query,           \* Last user query
    last_response,           \* Last LLM response
    temperature,           \* LLM temperature (0.0-2.0)
    max_tokens,           \* Max response tokens
    error,           \* Error message if any
    event_history    \* Trace of events

vars == <<state, api_key, api_base, model, schema_content, blueprint, blueprint_path, conversation, last_query, last_response, temperature, max_tokens, error, event_history>>

\* Type invariant - structural correctness
TypeInvariant ==
    /\ state \in States
    /\ TRUE  \* api_key: any string or NULL
    /\ TRUE  \* api_base: any string or NULL
    /\ TRUE  \* model: any string or NULL
    /\ TRUE  \* schema_content: any string or NULL
    /\ TRUE  \* blueprint: any string or NULL
    /\ TRUE  \* blueprint_path: any string or NULL
    /\ TRUE  \* conversation: any string or NULL
    /\ TRUE  \* last_query: any string or NULL
    /\ TRUE  \* last_response: any string or NULL
    /\ (temperature \in BoundedInt) \/ (temperature = NULL)
    /\ (max_tokens \in BoundedInt) \/ (max_tokens = NULL)
    /\ TRUE  \* error: any string or NULL

\* State constraint - limits TLC exploration depth
StateConstraint ==
    /\ Len(event_history) <= MAX_HISTORY
    /\ (temperature = NULL) \/ (temperature \in BoundedInt)
    /\ (max_tokens = NULL) \/ (max_tokens \in BoundedInt)

\* Initial state
Init ==
    /\ state = "init"
    /\ api_key = NULL
    /\ api_base = NULL
    /\ model = NULL
    /\ schema_content = NULL
    /\ blueprint = NULL
    /\ blueprint_path = NULL
    /\ conversation = NULL
    /\ last_query = NULL
    /\ last_response = NULL
    /\ temperature = NULL
    /\ max_tokens = NULL
    /\ error = NULL
    /\ event_history = <<>>

\* Transitions
\* t_init_start: init --(START)--> ready
t_init_start ==
    /\ state = "init"
    /\ api_key /= NULL  \* gate: has_api_key
    /\ state' = "ready"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ schema_content' = schema_content
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ conversation' = conversation
    /\ last_query' = last_query
    /\ last_response' = last_response
    /\ temperature' = temperature
    /\ max_tokens' = max_tokens
    /\ error' = error
    /\ event_history' = Append(event_history, "START")

\* t_init_no_key: init --(START)--> error
t_init_no_key ==
    /\ state = "init"
    /\ api_key = NULL  \* gate: no_api_key
    /\ state' = "error"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ schema_content' = schema_content
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ conversation' = conversation
    /\ last_query' = last_query
    /\ last_response' = last_response
    /\ temperature' = temperature
    /\ max_tokens' = max_tokens
    /\ error' = error
    /\ event_history' = Append(event_history, "START")

\* t_configure: * --(CONFIGURE)--> init
t_configure ==
    /\ TRUE  \* from any state
    /\ state' = "init"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ schema_content' = schema_content
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ conversation' = conversation
    /\ last_query' = last_query
    /\ last_response' = last_response
    /\ temperature' = temperature
    /\ max_tokens' = max_tokens
    /\ error' = error
    /\ event_history' = Append(event_history, "CONFIGURE")

\* t_set_key: error --(SET_KEY)--> init
t_set_key ==
    /\ state = "error"
    /\ state' = "init"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ schema_content' = schema_content
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ conversation' = conversation
    /\ last_query' = last_query
    /\ last_response' = last_response
    /\ temperature' = temperature
    /\ max_tokens' = max_tokens
    /\ error' = error
    /\ event_history' = Append(event_history, "SET_KEY")

\* t_load_blueprint: ready --(LOAD)--> ready
t_load_blueprint ==
    /\ state = "ready"
    /\ state' = "ready"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ schema_content' = schema_content
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ conversation' = conversation
    /\ last_query' = last_query
    /\ last_response' = last_response
    /\ temperature' = temperature
    /\ max_tokens' = max_tokens
    /\ error' = error
    /\ event_history' = Append(event_history, "LOAD")

\* t_query: ready --(QUERY)--> querying
t_query ==
    /\ state = "ready"
    /\ state' = "querying"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ schema_content' = schema_content
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ conversation' = conversation
    /\ last_query' = last_query
    /\ last_response' = last_response
    /\ temperature' = temperature
    /\ max_tokens' = max_tokens
    /\ error' = error
    /\ event_history' = Append(event_history, "QUERY")

\* t_explain: ready --(EXPLAIN)--> querying
t_explain ==
    /\ state = "ready"
    /\ blueprint /= NULL  \* gate: has_blueprint
    /\ state' = "querying"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ schema_content' = schema_content
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ conversation' = conversation
    /\ last_query' = last_query
    /\ last_response' = last_response
    /\ temperature' = temperature
    /\ max_tokens' = max_tokens
    /\ error' = error
    /\ event_history' = Append(event_history, "EXPLAIN")

\* t_validate: ready --(VALIDATE)--> querying
t_validate ==
    /\ state = "ready"
    /\ blueprint /= NULL  \* gate: has_blueprint
    /\ state' = "querying"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ schema_content' = schema_content
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ conversation' = conversation
    /\ last_query' = last_query
    /\ last_response' = last_response
    /\ temperature' = temperature
    /\ max_tokens' = max_tokens
    /\ error' = error
    /\ event_history' = Append(event_history, "VALIDATE")

\* t_suggest: ready --(SUGGEST)--> querying
t_suggest ==
    /\ state = "ready"
    /\ blueprint /= NULL  \* gate: has_blueprint
    /\ state' = "querying"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ schema_content' = schema_content
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ conversation' = conversation
    /\ last_query' = last_query
    /\ last_response' = last_response
    /\ temperature' = temperature
    /\ max_tokens' = max_tokens
    /\ error' = error
    /\ event_history' = Append(event_history, "SUGGEST")

\* t_query_done: querying --(DONE)--> ready
t_query_done ==
    /\ state = "querying"
    /\ error = NULL  \* gate: no_error
    /\ state' = "ready"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ schema_content' = schema_content
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ conversation' = conversation
    /\ last_query' = last_query
    /\ last_response' = last_response
    /\ temperature' = temperature
    /\ max_tokens' = max_tokens
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_query_error: querying --(DONE)--> error
t_query_error ==
    /\ state = "querying"
    /\ error /= NULL  \* gate: has_error
    /\ state' = "error"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ schema_content' = schema_content
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ conversation' = conversation
    /\ last_query' = last_query
    /\ last_response' = last_response
    /\ temperature' = temperature
    /\ max_tokens' = max_tokens
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_clear: ready --(CLEAR)--> ready
t_clear ==
    /\ state = "ready"
    /\ state' = "ready"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ schema_content' = schema_content
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ conversation' = conversation
    /\ last_query' = last_query
    /\ last_response' = last_response
    /\ temperature' = temperature
    /\ max_tokens' = max_tokens
    /\ error' = error
    /\ event_history' = Append(event_history, "CLEAR")

\* t_recover: error --(RETRY)--> ready
t_recover ==
    /\ state = "error"
    /\ api_key /= NULL  \* gate: has_api_key
    /\ state' = "ready"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ schema_content' = schema_content
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ conversation' = conversation
    /\ last_query' = last_query
    /\ last_response' = last_response
    /\ temperature' = temperature
    /\ max_tokens' = max_tokens
    /\ error' = error
    /\ event_history' = Append(event_history, "RETRY")

\* Next state relation
Next ==
    \/ t_init_start
    \/ t_init_no_key
    \/ t_configure
    \/ t_set_key
    \/ t_load_blueprint
    \/ t_query
    \/ t_explain
    \/ t_validate
    \/ t_suggest
    \/ t_query_done
    \/ t_query_error
    \/ t_clear
    \/ t_recover

\* Specification
Spec == Init /\ [][Next]_vars

\* Safety: Always in valid state
AlwaysValidState == state \in States

\* Liveness: No deadlock (always can make progress)
NoDeadlock == <>(ENABLED Next)

\* Reachability: Entry state is reachable
EntryReachable == state = "init"

=============================================================================