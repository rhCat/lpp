---------------------------- MODULE compliance_checker ----------------------------
\* L++ Blueprint: L++ Compliance Checker
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
States == {"idle", "blueprint_loaded", "ready", "checking", "report_ready", "error"}

Events == {"AUTO", "BACK", "CHECK", "CHECK_POLICY", "CLEAR", "ERROR", "EXPORT", "GENERATE_REPORT", "LOAD_BLUEPRINT", "LOAD_FAILED", "LOAD_POLICIES", "LOAD_POLICY", "UNLOAD"}

TerminalStates == {}

VARIABLES
    state,           \* Current state
    blueprint,           \* The loaded blueprint to check
    blueprint_path,           \* Path to the loaded blueprint
    blueprint_name,           \* Name of the loaded blueprint
    policies,           \* List of loaded compliance policies
    policies_dir,           \* Directory containing policy files
    current_policy,           \* Currently selected policy for inspection
    findings,           \* List of compliance findings
    report,           \* Generated compliance report
    score,           \* Compliance score (0-100)
    summary,           \* Summary of pass/fail counts by severity
    export_path,           \* Path where report was exported
    error,           \* Error message if any
    event_history    \* Trace of events

vars == <<state, blueprint, blueprint_path, blueprint_name, policies, policies_dir, current_policy, findings, report, score, summary, export_path, error, event_history>>

\* Type invariant - structural correctness
TypeInvariant ==
    /\ state \in States
    /\ TRUE  \* blueprint: any string or NULL
    /\ TRUE  \* blueprint_path: any string or NULL
    /\ TRUE  \* blueprint_name: any string or NULL
    /\ TRUE  \* policies: any string or NULL
    /\ TRUE  \* policies_dir: any string or NULL
    /\ TRUE  \* current_policy: any string or NULL
    /\ TRUE  \* findings: any string or NULL
    /\ TRUE  \* report: any string or NULL
    /\ (score \in BoundedInt) \/ (score = NULL)
    /\ TRUE  \* summary: any string or NULL
    /\ TRUE  \* export_path: any string or NULL
    /\ TRUE  \* error: any string or NULL

\* State constraint - limits TLC exploration depth
StateConstraint ==
    /\ Len(event_history) <= MAX_HISTORY
    /\ (score = NULL) \/ (score \in BoundedInt)

\* Initial state
Init ==
    /\ state = "idle"
    /\ blueprint = NULL
    /\ blueprint_path = NULL
    /\ blueprint_name = NULL
    /\ policies = NULL
    /\ policies_dir = NULL
    /\ current_policy = NULL
    /\ findings = NULL
    /\ report = NULL
    /\ score = NULL
    /\ summary = NULL
    /\ export_path = NULL
    /\ error = NULL
    /\ event_history = <<>>

\* Transitions
\* t_load_blueprint: idle --(LOAD_BLUEPRINT)--> blueprint_loaded
t_load_blueprint ==
    /\ state = "idle"
    /\ blueprint = NULL  \* gate: no_blueprint
    /\ state' = "blueprint_loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ policies' = policies
    /\ policies_dir' = policies_dir
    /\ current_policy' = current_policy
    /\ findings' = findings
    /\ report' = report
    /\ score' = score
    /\ summary' = summary
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "LOAD_BLUEPRINT")

\* t_load_blueprint_error: idle --(LOAD_FAILED)--> error
t_load_blueprint_error ==
    /\ state = "idle"
    /\ state' = "error"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ policies' = policies
    /\ policies_dir' = policies_dir
    /\ current_policy' = current_policy
    /\ findings' = findings
    /\ report' = report
    /\ score' = score
    /\ summary' = summary
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "LOAD_FAILED")

\* t_reload_blueprint: blueprint_loaded --(LOAD_BLUEPRINT)--> blueprint_loaded
t_reload_blueprint ==
    /\ state = "blueprint_loaded"
    /\ state' = "blueprint_loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ policies' = policies
    /\ policies_dir' = policies_dir
    /\ current_policy' = current_policy
    /\ findings' = findings
    /\ report' = report
    /\ score' = score
    /\ summary' = summary
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "LOAD_BLUEPRINT")

\* t_reload_blueprint_ready: ready --(LOAD_BLUEPRINT)--> ready
t_reload_blueprint_ready ==
    /\ state = "ready"
    /\ state' = "ready"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ policies' = policies
    /\ policies_dir' = policies_dir
    /\ current_policy' = current_policy
    /\ findings' = findings
    /\ report' = report
    /\ score' = score
    /\ summary' = summary
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "LOAD_BLUEPRINT")

\* t_reload_blueprint_report: report_ready --(LOAD_BLUEPRINT)--> ready
t_reload_blueprint_report ==
    /\ state = "report_ready"
    /\ state' = "ready"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ policies' = policies
    /\ policies_dir' = policies_dir
    /\ current_policy' = current_policy
    /\ findings' = findings
    /\ report' = report
    /\ score' = score
    /\ summary' = summary
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "LOAD_BLUEPRINT")

\* t_load_policies: blueprint_loaded --(LOAD_POLICIES)--> ready
t_load_policies ==
    /\ state = "blueprint_loaded"
    /\ blueprint /= NULL  \* gate: has_blueprint
    /\ state' = "ready"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ policies' = policies
    /\ policies_dir' = policies_dir
    /\ current_policy' = current_policy
    /\ findings' = findings
    /\ report' = report
    /\ score' = score
    /\ summary' = summary
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "LOAD_POLICIES")

\* t_load_single_policy: blueprint_loaded --(LOAD_POLICY)--> ready
t_load_single_policy ==
    /\ state = "blueprint_loaded"
    /\ blueprint /= NULL  \* gate: has_blueprint
    /\ state' = "ready"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ policies' = policies
    /\ policies_dir' = policies_dir
    /\ current_policy' = current_policy
    /\ findings' = findings
    /\ report' = report
    /\ score' = score
    /\ summary' = summary
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "LOAD_POLICY")

\* t_reload_policies: ready --(LOAD_POLICIES)--> ready
t_reload_policies ==
    /\ state = "ready"
    /\ state' = "ready"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ policies' = policies
    /\ policies_dir' = policies_dir
    /\ current_policy' = current_policy
    /\ findings' = findings
    /\ report' = report
    /\ score' = score
    /\ summary' = summary
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "LOAD_POLICIES")

\* t_reload_policies_report: report_ready --(LOAD_POLICIES)--> ready
t_reload_policies_report ==
    /\ state = "report_ready"
    /\ state' = "ready"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ policies' = policies
    /\ policies_dir' = policies_dir
    /\ current_policy' = current_policy
    /\ findings' = findings
    /\ report' = report
    /\ score' = score
    /\ summary' = summary
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "LOAD_POLICIES")

\* t_add_policy: ready --(LOAD_POLICY)--> ready
t_add_policy ==
    /\ state = "ready"
    /\ state' = "ready"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ policies' = policies
    /\ policies_dir' = policies_dir
    /\ current_policy' = current_policy
    /\ findings' = findings
    /\ report' = report
    /\ score' = score
    /\ summary' = summary
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "LOAD_POLICY")

\* t_check_all: ready --(CHECK)--> checking
t_check_all ==
    /\ state = "ready"
    /\ blueprint /= NULL  \* gate: has_blueprint
    /\ policies /= NULL /\ Len(policies) > 0  \* gate: has_policies
    /\ state' = "checking"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ policies' = policies
    /\ policies_dir' = policies_dir
    /\ current_policy' = current_policy
    /\ findings' = findings
    /\ report' = report
    /\ score' = score
    /\ summary' = summary
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "CHECK")

\* t_check_single: ready --(CHECK_POLICY)--> checking
t_check_single ==
    /\ state = "ready"
    /\ blueprint /= NULL  \* gate: has_blueprint
    /\ state' = "checking"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ policies' = policies
    /\ policies_dir' = policies_dir
    /\ current_policy' = current_policy
    /\ findings' = findings
    /\ report' = report
    /\ score' = score
    /\ summary' = summary
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "CHECK_POLICY")

\* t_generate_report: checking --(GENERATE_REPORT)--> report_ready
t_generate_report ==
    /\ state = "checking"
    /\ findings /= NULL /\ Len(findings) > 0  \* gate: has_findings
    /\ state' = "report_ready"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ policies' = policies
    /\ policies_dir' = policies_dir
    /\ current_policy' = current_policy
    /\ findings' = findings
    /\ report' = report
    /\ score' = score
    /\ summary' = summary
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "GENERATE_REPORT")

\* t_auto_report: checking --(AUTO)--> report_ready
t_auto_report ==
    /\ state = "checking"
    /\ state' = "report_ready"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ policies' = policies
    /\ policies_dir' = policies_dir
    /\ current_policy' = current_policy
    /\ findings' = findings
    /\ report' = report
    /\ score' = score
    /\ summary' = summary
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "AUTO")

\* t_export_report: report_ready --(EXPORT)--> report_ready
t_export_report ==
    /\ state = "report_ready"
    /\ report /= NULL  \* gate: has_report
    /\ state' = "report_ready"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ policies' = policies
    /\ policies_dir' = policies_dir
    /\ current_policy' = current_policy
    /\ findings' = findings
    /\ report' = report
    /\ score' = score
    /\ summary' = summary
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "EXPORT")

\* t_recheck: report_ready --(CHECK)--> checking
t_recheck ==
    /\ state = "report_ready"
    /\ blueprint /= NULL  \* gate: has_blueprint
    /\ policies /= NULL /\ Len(policies) > 0  \* gate: has_policies
    /\ state' = "checking"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ policies' = policies
    /\ policies_dir' = policies_dir
    /\ current_policy' = current_policy
    /\ findings' = findings
    /\ report' = report
    /\ score' = score
    /\ summary' = summary
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "CHECK")

\* t_back_to_ready: report_ready --(BACK)--> ready
t_back_to_ready ==
    /\ state = "report_ready"
    /\ state' = "ready"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ policies' = policies
    /\ policies_dir' = policies_dir
    /\ current_policy' = current_policy
    /\ findings' = findings
    /\ report' = report
    /\ score' = score
    /\ summary' = summary
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "BACK")

\* t_back_to_loaded: ready --(BACK)--> blueprint_loaded
t_back_to_loaded ==
    /\ state = "ready"
    /\ state' = "blueprint_loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ policies' = policies
    /\ policies_dir' = policies_dir
    /\ current_policy' = current_policy
    /\ findings' = findings
    /\ report' = report
    /\ score' = score
    /\ summary' = summary
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "BACK")

\* t_unload: blueprint_loaded --(UNLOAD)--> idle
t_unload ==
    /\ state = "blueprint_loaded"
    /\ state' = "idle"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ policies' = policies
    /\ policies_dir' = policies_dir
    /\ current_policy' = current_policy
    /\ findings' = findings
    /\ report' = report
    /\ score' = score
    /\ summary' = summary
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "UNLOAD")

\* t_unload_ready: ready --(UNLOAD)--> idle
t_unload_ready ==
    /\ state = "ready"
    /\ state' = "idle"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ policies' = policies
    /\ policies_dir' = policies_dir
    /\ current_policy' = current_policy
    /\ findings' = findings
    /\ report' = report
    /\ score' = score
    /\ summary' = summary
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "UNLOAD")

\* t_unload_report: report_ready --(UNLOAD)--> idle
t_unload_report ==
    /\ state = "report_ready"
    /\ state' = "idle"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ policies' = policies
    /\ policies_dir' = policies_dir
    /\ current_policy' = current_policy
    /\ findings' = findings
    /\ report' = report
    /\ score' = score
    /\ summary' = summary
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "UNLOAD")

\* t_recover: error --(CLEAR)--> idle
t_recover ==
    /\ state = "error"
    /\ state' = "idle"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ policies' = policies
    /\ policies_dir' = policies_dir
    /\ current_policy' = current_policy
    /\ findings' = findings
    /\ report' = report
    /\ score' = score
    /\ summary' = summary
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "CLEAR")

\* t_global_error: * --(ERROR)--> error
t_global_error ==
    /\ TRUE  \* from any state
    /\ state' = "error"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_name' = blueprint_name
    /\ policies' = policies
    /\ policies_dir' = policies_dir
    /\ current_policy' = current_policy
    /\ findings' = findings
    /\ report' = report
    /\ score' = score
    /\ summary' = summary
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "ERROR")

\* Next state relation
Next ==
    \/ t_load_blueprint
    \/ t_load_blueprint_error
    \/ t_reload_blueprint
    \/ t_reload_blueprint_ready
    \/ t_reload_blueprint_report
    \/ t_load_policies
    \/ t_load_single_policy
    \/ t_reload_policies
    \/ t_reload_policies_report
    \/ t_add_policy
    \/ t_check_all
    \/ t_check_single
    \/ t_generate_report
    \/ t_auto_report
    \/ t_export_report
    \/ t_recheck
    \/ t_back_to_ready
    \/ t_back_to_loaded
    \/ t_unload
    \/ t_unload_ready
    \/ t_unload_report
    \/ t_recover
    \/ t_global_error

\* Specification
Spec == Init /\ [][Next]_vars

\* Safety: Always in valid state
AlwaysValidState == state \in States

\* Liveness: No deadlock (always can make progress)
NoDeadlock == <>(ENABLED Next)

\* Reachability: Entry state is reachable
EntryReachable == state = "idle"

=============================================================================