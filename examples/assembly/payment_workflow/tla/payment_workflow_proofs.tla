--------------------------- MODULE payment_workflow_proofs ---------------------------
(*
 * L++ Assembly Blueprint: Payment Workflow
 * TLAPS-ready specification with formal proofs
 *
 * This module proves the three assembly invariants:
 *   AI_001: Payment requires authentication
 *   AI_002: Auth before payment
 *   AI_003: All paths audited
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    NULL,
    \* Assembly states
    STATE_idle, STATE_authenticating, STATE_processing_payment,
    STATE_logging_success, STATE_logging_failure, STATE_complete, STATE_failed,
    \* Auth terminals
    AUTH_pending, AUTH_authenticated, AUTH_failed,
    \* Payment terminals
    PAY_pending, PAY_complete, PAY_failed,
    \* Audit terminals
    AUDIT_pending, AUDIT_logged

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_authenticating /\ STATE_idle /= STATE_processing_payment
    /\ STATE_idle /= STATE_logging_success /\ STATE_idle /= STATE_logging_failure
    /\ STATE_idle /= STATE_complete /\ STATE_idle /= STATE_failed
    /\ STATE_authenticating /= STATE_processing_payment
    /\ STATE_authenticating /= STATE_logging_success /\ STATE_authenticating /= STATE_logging_failure
    /\ STATE_authenticating /= STATE_complete /\ STATE_authenticating /= STATE_failed
    /\ STATE_processing_payment /= STATE_logging_success
    /\ STATE_processing_payment /= STATE_logging_failure
    /\ STATE_processing_payment /= STATE_complete /\ STATE_processing_payment /= STATE_failed
    /\ STATE_logging_success /= STATE_logging_failure
    /\ STATE_logging_success /= STATE_complete /\ STATE_logging_success /= STATE_failed
    /\ STATE_logging_failure /= STATE_complete /\ STATE_logging_failure /= STATE_failed
    /\ STATE_complete /= STATE_failed
    /\ AUTH_pending /= AUTH_authenticated /\ AUTH_pending /= AUTH_failed
    /\ AUTH_authenticated /= AUTH_failed
    /\ PAY_pending /= PAY_complete /\ PAY_pending /= PAY_failed
    /\ PAY_complete /= PAY_failed
    /\ AUDIT_pending /= AUDIT_logged

VARIABLES
    meta_state,
    auth_terminal,
    payment_terminal,
    audit_terminal

vars == <<meta_state, auth_terminal, payment_terminal, audit_terminal>>

-----------------------------------------------------------------------------
(* Type definitions *)

AssemblyStates == {STATE_idle, STATE_authenticating, STATE_processing_payment,
                   STATE_logging_success, STATE_logging_failure, STATE_complete, STATE_failed}

AuthTerminals == {AUTH_pending, AUTH_authenticated, AUTH_failed}

PaymentTerminals == {PAY_pending, PAY_complete, PAY_failed}

AuditTerminals == {AUDIT_pending, AUDIT_logged}

TypeInvariant ==
    /\ meta_state \in AssemblyStates
    /\ auth_terminal \in AuthTerminals
    /\ payment_terminal \in PaymentTerminals
    /\ audit_terminal \in AuditTerminals

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ meta_state = STATE_idle
    /\ auth_terminal = AUTH_pending
    /\ payment_terminal = PAY_pending
    /\ audit_terminal = AUDIT_pending

-----------------------------------------------------------------------------
(* Transitions *)

t_start ==
    /\ meta_state = STATE_idle
    /\ meta_state' = STATE_authenticating
    /\ auth_terminal' \in {AUTH_authenticated, AUTH_failed}
    /\ UNCHANGED <<payment_terminal, audit_terminal>>

t_auth_success ==
    /\ meta_state = STATE_authenticating
    /\ auth_terminal = AUTH_authenticated
    /\ meta_state' = STATE_processing_payment
    /\ payment_terminal' \in {PAY_complete, PAY_failed}
    /\ UNCHANGED <<auth_terminal, audit_terminal>>

t_auth_failed ==
    /\ meta_state = STATE_authenticating
    /\ auth_terminal = AUTH_failed
    /\ meta_state' = STATE_logging_failure
    /\ audit_terminal' = AUDIT_logged
    /\ UNCHANGED <<auth_terminal, payment_terminal>>

t_payment_success ==
    /\ meta_state = STATE_processing_payment
    /\ payment_terminal = PAY_complete
    /\ meta_state' = STATE_logging_success
    /\ audit_terminal' = AUDIT_logged
    /\ UNCHANGED <<auth_terminal, payment_terminal>>

t_payment_failed ==
    /\ meta_state = STATE_processing_payment
    /\ payment_terminal = PAY_failed
    /\ meta_state' = STATE_logging_failure
    /\ audit_terminal' = AUDIT_logged
    /\ UNCHANGED <<auth_terminal, payment_terminal>>

t_logged_success ==
    /\ meta_state = STATE_logging_success
    /\ audit_terminal = AUDIT_logged
    /\ meta_state' = STATE_complete
    /\ UNCHANGED <<auth_terminal, payment_terminal, audit_terminal>>

t_logged_failure ==
    /\ meta_state = STATE_logging_failure
    /\ audit_terminal = AUDIT_logged
    /\ meta_state' = STATE_failed
    /\ UNCHANGED <<auth_terminal, payment_terminal, audit_terminal>>

Next ==
    \/ t_start
    \/ t_auth_success
    \/ t_auth_failed
    \/ t_payment_success
    \/ t_payment_failed
    \/ t_logged_success
    \/ t_logged_failure

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Assembly Invariants *)

(* AI_001: Payment requires authentication *)
AI_001 ==
    meta_state = STATE_processing_payment => auth_terminal = AUTH_authenticated

(* AI_002: Auth before payment *)
AI_002 ==
    payment_terminal /= PAY_pending => auth_terminal = AUTH_authenticated

(* AI_003: All paths audited *)
AI_003 ==
    (meta_state = STATE_complete \/ meta_state = STATE_failed) => audit_terminal = AUDIT_logged

(* Strengthening invariant: payment_terminal only becomes non-pending after we leave authenticating *)
AI_004_PaymentOnlyAfterAuth ==
    (meta_state = STATE_idle \/ meta_state = STATE_authenticating) => payment_terminal = PAY_pending

(* Combined inductive invariant *)
Inv ==
    /\ TypeInvariant
    /\ AI_001
    /\ AI_002
    /\ AI_003
    /\ AI_004_PaymentOnlyAfterAuth

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

(* Lemma: Init establishes invariant *)
LEMMA InitEstablishesInv == Init => Inv
<1>1. Init => TypeInvariant
  BY DEF Init, TypeInvariant, AssemblyStates, AuthTerminals, PaymentTerminals, AuditTerminals
<1>2. Init => AI_001
  BY ConstantsDistinct DEF Init, AI_001
<1>3. Init => AI_002
  BY ConstantsDistinct DEF Init, AI_002
<1>4. Init => AI_003
  BY ConstantsDistinct DEF Init, AI_003
<1>5. Init => AI_004_PaymentOnlyAfterAuth
  BY DEF Init, AI_004_PaymentOnlyAfterAuth
<1>6. QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Inv

(* Lemma: t_start preserves invariant *)
LEMMA StartPreservesInv == Inv /\ t_start => Inv'
<1>1. Inv /\ t_start => TypeInvariant'
  BY ConstantsDistinct DEF Inv, t_start, TypeInvariant, AssemblyStates, AuthTerminals, PaymentTerminals, AuditTerminals
<1>2. Inv /\ t_start => AI_001'
  BY ConstantsDistinct DEF Inv, t_start, AI_001
<1>3. Inv /\ t_start => AI_002'
  \* From AI_004: in STATE_idle, payment_terminal = PAY_pending
  \* After t_start: payment_terminal' = PAY_pending (UNCHANGED), so AI_002' vacuously true
  BY ConstantsDistinct DEF Inv, t_start, AI_002, AI_004_PaymentOnlyAfterAuth
<1>4. Inv /\ t_start => AI_003'
  BY ConstantsDistinct DEF Inv, t_start, AI_003
<1>5. Inv /\ t_start => AI_004_PaymentOnlyAfterAuth'
  \* After t_start: meta_state' = STATE_authenticating, payment_terminal' = PAY_pending
  BY ConstantsDistinct DEF Inv, t_start, AI_004_PaymentOnlyAfterAuth
<1>6. QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Inv

(* Lemma: t_auth_success preserves invariant *)
LEMMA AuthSuccessPreservesInv == Inv /\ t_auth_success => Inv'
<1>1. Inv /\ t_auth_success => TypeInvariant'
  BY ConstantsDistinct DEF Inv, t_auth_success, TypeInvariant, AssemblyStates, AuthTerminals, PaymentTerminals, AuditTerminals
<1>2. Inv /\ t_auth_success => AI_001'
  BY ConstantsDistinct DEF Inv, t_auth_success, AI_001
<1>3. Inv /\ t_auth_success => AI_002'
  \* auth_terminal = AUTH_authenticated, so AI_002' holds regardless of payment_terminal'
  BY ConstantsDistinct DEF Inv, t_auth_success, AI_002
<1>4. Inv /\ t_auth_success => AI_003'
  BY ConstantsDistinct DEF Inv, t_auth_success, AI_003
<1>5. Inv /\ t_auth_success => AI_004_PaymentOnlyAfterAuth'
  \* meta_state' = STATE_processing_payment, so antecedent of AI_004' is false
  BY ConstantsDistinct DEF Inv, t_auth_success, AI_004_PaymentOnlyAfterAuth
<1>6. QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Inv

(* Lemma: t_auth_failed preserves invariant *)
LEMMA AuthFailedPreservesInv == Inv /\ t_auth_failed => Inv'
<1>1. Inv /\ t_auth_failed => TypeInvariant'
  BY ConstantsDistinct DEF Inv, t_auth_failed, TypeInvariant, AssemblyStates, AuthTerminals, PaymentTerminals, AuditTerminals
<1>2. Inv /\ t_auth_failed => AI_001'
  BY ConstantsDistinct DEF Inv, t_auth_failed, AI_001
<1>3. Inv /\ t_auth_failed => AI_002'
  \* payment_terminal unchanged, stays PAY_pending from AI_004
  BY ConstantsDistinct DEF Inv, t_auth_failed, AI_002, AI_004_PaymentOnlyAfterAuth
<1>4. Inv /\ t_auth_failed => AI_003'
  BY ConstantsDistinct DEF Inv, t_auth_failed, AI_003
<1>5. Inv /\ t_auth_failed => AI_004_PaymentOnlyAfterAuth'
  \* meta_state' = STATE_logging_failure, so antecedent of AI_004' is false
  BY ConstantsDistinct DEF Inv, t_auth_failed, AI_004_PaymentOnlyAfterAuth
<1>6. QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Inv

(* Lemma: t_payment_success preserves invariant *)
LEMMA PaymentSuccessPreservesInv == Inv /\ t_payment_success => Inv'
<1>1. Inv /\ t_payment_success => TypeInvariant'
  BY ConstantsDistinct DEF Inv, t_payment_success, TypeInvariant, AssemblyStates, AuthTerminals, PaymentTerminals, AuditTerminals
<1>2. Inv /\ t_payment_success => AI_001'
  BY ConstantsDistinct DEF Inv, t_payment_success, AI_001
<1>3. Inv /\ t_payment_success => AI_002'
  \* From AI_001: in STATE_processing_payment, auth_terminal = AUTH_authenticated
  BY ConstantsDistinct DEF Inv, t_payment_success, AI_001, AI_002
<1>4. Inv /\ t_payment_success => AI_003'
  BY ConstantsDistinct DEF Inv, t_payment_success, AI_003
<1>5. Inv /\ t_payment_success => AI_004_PaymentOnlyAfterAuth'
  \* meta_state' = STATE_logging_success, so antecedent of AI_004' is false
  BY ConstantsDistinct DEF Inv, t_payment_success, AI_004_PaymentOnlyAfterAuth
<1>6. QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Inv

(* Lemma: t_payment_failed preserves invariant *)
LEMMA PaymentFailedPreservesInv == Inv /\ t_payment_failed => Inv'
<1>1. Inv /\ t_payment_failed => TypeInvariant'
  BY ConstantsDistinct DEF Inv, t_payment_failed, TypeInvariant, AssemblyStates, AuthTerminals, PaymentTerminals, AuditTerminals
<1>2. Inv /\ t_payment_failed => AI_001'
  BY ConstantsDistinct DEF Inv, t_payment_failed, AI_001
<1>3. Inv /\ t_payment_failed => AI_002'
  \* From AI_001: in STATE_processing_payment, auth_terminal = AUTH_authenticated
  BY ConstantsDistinct DEF Inv, t_payment_failed, AI_001, AI_002
<1>4. Inv /\ t_payment_failed => AI_003'
  BY ConstantsDistinct DEF Inv, t_payment_failed, AI_003
<1>5. Inv /\ t_payment_failed => AI_004_PaymentOnlyAfterAuth'
  \* meta_state' = STATE_logging_failure, so antecedent of AI_004' is false
  BY ConstantsDistinct DEF Inv, t_payment_failed, AI_004_PaymentOnlyAfterAuth
<1>6. QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Inv

(* Lemma: t_logged_success preserves invariant *)
LEMMA LoggedSuccessPreservesInv == Inv /\ t_logged_success => Inv'
<1>1. Inv /\ t_logged_success => TypeInvariant'
  BY ConstantsDistinct DEF Inv, t_logged_success, TypeInvariant, AssemblyStates, AuthTerminals, PaymentTerminals, AuditTerminals
<1>2. Inv /\ t_logged_success => AI_001'
  BY ConstantsDistinct DEF Inv, t_logged_success, AI_001
<1>3. Inv /\ t_logged_success => AI_002'
  BY ConstantsDistinct DEF Inv, t_logged_success, AI_002
<1>4. Inv /\ t_logged_success => AI_003'
  BY ConstantsDistinct DEF Inv, t_logged_success, AI_003
<1>5. Inv /\ t_logged_success => AI_004_PaymentOnlyAfterAuth'
  \* meta_state' = STATE_complete, so antecedent of AI_004' is false
  BY ConstantsDistinct DEF Inv, t_logged_success, AI_004_PaymentOnlyAfterAuth
<1>6. QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Inv

(* Lemma: t_logged_failure preserves invariant *)
LEMMA LoggedFailurePreservesInv == Inv /\ t_logged_failure => Inv'
<1>1. Inv /\ t_logged_failure => TypeInvariant'
  BY ConstantsDistinct DEF Inv, t_logged_failure, TypeInvariant, AssemblyStates, AuthTerminals, PaymentTerminals, AuditTerminals
<1>2. Inv /\ t_logged_failure => AI_001'
  BY ConstantsDistinct DEF Inv, t_logged_failure, AI_001
<1>3. Inv /\ t_logged_failure => AI_002'
  BY ConstantsDistinct DEF Inv, t_logged_failure, AI_002
<1>4. Inv /\ t_logged_failure => AI_003'
  BY ConstantsDistinct DEF Inv, t_logged_failure, AI_003
<1>5. Inv /\ t_logged_failure => AI_004_PaymentOnlyAfterAuth'
  \* meta_state' = STATE_failed, so antecedent of AI_004' is false
  BY ConstantsDistinct DEF Inv, t_logged_failure, AI_004_PaymentOnlyAfterAuth
<1>6. QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Inv

(* Lemma: Stuttering preserves invariant *)
LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant, AI_001, AI_002, AI_003, AI_004_PaymentOnlyAfterAuth

(* Lemma: Next preserves invariant *)
LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY StartPreservesInv, AuthSuccessPreservesInv, AuthFailedPreservesInv,
   PaymentSuccessPreservesInv, PaymentFailedPreservesInv,
   LoggedSuccessPreservesInv, LoggedFailurePreservesInv
   DEF Next

(* Main inductive invariant theorem *)
THEOREM InductiveInvariant == Inv /\ [Next]_vars => Inv'
BY NextPreservesInv, StutterPreservesInv DEF vars

(* Main safety theorem *)
THEOREM SafetyTheorem == Spec => []Inv
<1>1. Init => Inv
  BY InitEstablishesInv
<1>2. Inv /\ [Next]_vars => Inv'
  BY InductiveInvariant
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

=============================================================================
