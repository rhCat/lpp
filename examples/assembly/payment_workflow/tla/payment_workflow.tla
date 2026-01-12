--------------------------- MODULE payment_workflow ---------------------------

EXTENDS Integers, Sequences, TLC

VARIABLES
    meta_state,           \* Current assembly state
    ctx_workflow_id,
    ctx_username,
    ctx_password,
    ctx_amount,
    ctx_auth_token,
    ctx_user_id,
    ctx_payment_id,
    ctx_transaction_ref,
    ctx_audit_id,
    ctx_error_source,
    ctx_error_code,
    ctx_audit_event_type,
    ctx_audit_details,
    auth_terminal,
    payment_terminal,
    audit_terminal

(* Component terminal sets *)
authTerminals == {"auth_failed", "authenticated", "PENDING"}
paymentTerminals == {"payment_failed", "payment_complete", "PENDING"}
auditTerminals == {"logged", "PENDING"}

AssemblyStates == {"idle", "authenticating", "processing_payment", "logging_success", "logging_failure", "complete", "failed"}

NULL == "__NULL__"

TypeInvariant ==
    /\ meta_state \in AssemblyStates
    /\ auth_terminal \in authTerminals
    /\ payment_terminal \in paymentTerminals
    /\ audit_terminal \in auditTerminals

Init ==
    /\ meta_state = "idle"
    /\ ctx_workflow_id = NULL
    /\ ctx_username = NULL
    /\ ctx_password = NULL
    /\ ctx_amount = NULL
    /\ ctx_auth_token = NULL
    /\ ctx_user_id = NULL
    /\ ctx_payment_id = NULL
    /\ ctx_transaction_ref = NULL
    /\ ctx_audit_id = NULL
    /\ ctx_error_source = NULL
    /\ ctx_error_code = NULL
    /\ ctx_audit_event_type = NULL
    /\ ctx_audit_details = NULL
    /\ auth_terminal = "PENDING"
    /\ payment_terminal = "PENDING"
    /\ audit_terminal = "PENDING"

(* Transition: t_start *)
t_start ==
    /\ meta_state = "idle"
    /\ meta_state' = "authenticating"
    /\ auth_terminal' \in {"auth_failed", "authenticated"}
    /\ UNCHANGED <<ctx_workflow_id, ctx_username, ctx_password, ctx_amount, ctx_auth_token, ctx_user_id, ctx_payment_id, ctx_transaction_ref, ctx_audit_id, ctx_error_source, ctx_error_code, ctx_audit_event_type, ctx_audit_details, payment_terminal, audit_terminal>>

(* Transition: t_auth_success *)
t_auth_success ==
    /\ meta_state = "authenticating"
    /\ auth_terminal /= "PENDING"
    /\ auth_terminal = 'authenticated'
    /\ meta_state' = "processing_payment"
    /\ payment_terminal' \in {"payment_failed", "payment_complete"}
    /\ UNCHANGED <<ctx_workflow_id, ctx_username, ctx_password, ctx_amount, ctx_auth_token, ctx_user_id, ctx_payment_id, ctx_transaction_ref, ctx_audit_id, ctx_error_source, ctx_error_code, ctx_audit_event_type, ctx_audit_details, auth_terminal, audit_terminal>>

(* Transition: t_auth_failed *)
t_auth_failed ==
    /\ meta_state = "authenticating"
    /\ auth_terminal /= "PENDING"
    /\ auth_terminal = 'auth_failed'
    /\ meta_state' = "logging_failure"
    /\ audit_terminal' \in {"logged"}
    /\ UNCHANGED <<ctx_workflow_id, ctx_username, ctx_password, ctx_amount, ctx_auth_token, ctx_user_id, ctx_payment_id, ctx_transaction_ref, ctx_audit_id, ctx_error_source, ctx_error_code, ctx_audit_event_type, ctx_audit_details, auth_terminal, payment_terminal>>

(* Transition: t_payment_success *)
t_payment_success ==
    /\ meta_state = "processing_payment"
    /\ payment_terminal /= "PENDING"
    /\ payment_terminal = 'payment_complete'
    /\ meta_state' = "logging_success"
    /\ audit_terminal' \in {"logged"}
    /\ UNCHANGED <<ctx_workflow_id, ctx_username, ctx_password, ctx_amount, ctx_auth_token, ctx_user_id, ctx_payment_id, ctx_transaction_ref, ctx_audit_id, ctx_error_source, ctx_error_code, ctx_audit_event_type, ctx_audit_details, auth_terminal, payment_terminal>>

(* Transition: t_payment_failed *)
t_payment_failed ==
    /\ meta_state = "processing_payment"
    /\ payment_terminal /= "PENDING"
    /\ payment_terminal = 'payment_failed'
    /\ meta_state' = "logging_failure"
    /\ audit_terminal' \in {"logged"}
    /\ UNCHANGED <<ctx_workflow_id, ctx_username, ctx_password, ctx_amount, ctx_auth_token, ctx_user_id, ctx_payment_id, ctx_transaction_ref, ctx_audit_id, ctx_error_source, ctx_error_code, ctx_audit_event_type, ctx_audit_details, auth_terminal, payment_terminal>>

(* Transition: t_logged_success *)
t_logged_success ==
    /\ meta_state = "logging_success"
    /\ audit_terminal /= "PENDING"
    /\ audit_terminal = 'logged'
    /\ meta_state' = "complete"
    /\ UNCHANGED <<ctx_workflow_id, ctx_username, ctx_password, ctx_amount, ctx_auth_token, ctx_user_id, ctx_payment_id, ctx_transaction_ref, ctx_audit_id, ctx_error_source, ctx_error_code, ctx_audit_event_type, ctx_audit_details, auth_terminal, payment_terminal, audit_terminal>>

(* Transition: t_logged_failure *)
t_logged_failure ==
    /\ meta_state = "logging_failure"
    /\ audit_terminal /= "PENDING"
    /\ audit_terminal = 'logged'
    /\ meta_state' = "failed"
    /\ UNCHANGED <<ctx_workflow_id, ctx_username, ctx_password, ctx_amount, ctx_auth_token, ctx_user_id, ctx_payment_id, ctx_transaction_ref, ctx_audit_id, ctx_error_source, ctx_error_code, ctx_audit_event_type, ctx_audit_details, auth_terminal, payment_terminal, audit_terminal>>

Next ==
    \/ t_start
    \/ t_auth_success
    \/ t_auth_failed
    \/ t_payment_success
    \/ t_payment_failed
    \/ t_logged_success
    \/ t_logged_failure

Spec == Init /\ [][Next]_<<meta_state, ctx_workflow_id, ctx_username, ctx_password, ctx_amount, ctx_auth_token, ctx_user_id, ctx_payment_id, ctx_transaction_ref, ctx_audit_id, ctx_error_source, ctx_error_code, ctx_audit_event_type, ctx_audit_details, auth_terminal, payment_terminal, audit_terminal>>

(* Payment requires authentication *)
AI_001 == meta_state = 'processing_payment' => auth_token /= NULL

(* Auth before payment *)
AI_002 == payment_terminal /= NULL => auth_terminal = 'authenticated'

(* All paths audited *)
AI_003 == (meta_state = 'complete' \/ meta_state = 'failed') => audit_terminal = 'logged'

=============================================================================