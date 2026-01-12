--------------------------- MODULE tlaps_seal_proofs ---------------------------
(*
 * L++ Blueprint: TLAPS Seal Certifier
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_loading, STATE_auditing, STATE_generating_tla, STATE_tlc_verifying, STATE_tlc_verified, STATE_tlaps_proving, STATE_certified, STATE_rejected, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_loading
    /\ STATE_idle /= STATE_auditing
    /\ STATE_idle /= STATE_generating_tla
    /\ STATE_idle /= STATE_tlc_verifying
    /\ STATE_idle /= STATE_tlc_verified
    /\ STATE_idle /= STATE_tlaps_proving
    /\ STATE_idle /= STATE_certified
    /\ STATE_idle /= STATE_rejected
    /\ STATE_idle /= STATE_error
    /\ STATE_loading /= STATE_auditing
    /\ STATE_loading /= STATE_generating_tla
    /\ STATE_loading /= STATE_tlc_verifying
    /\ STATE_loading /= STATE_tlc_verified
    /\ STATE_loading /= STATE_tlaps_proving
    /\ STATE_loading /= STATE_certified
    /\ STATE_loading /= STATE_rejected
    /\ STATE_loading /= STATE_error
    /\ STATE_auditing /= STATE_generating_tla
    /\ STATE_auditing /= STATE_tlc_verifying
    /\ STATE_auditing /= STATE_tlc_verified
    /\ STATE_auditing /= STATE_tlaps_proving
    /\ STATE_auditing /= STATE_certified
    /\ STATE_auditing /= STATE_rejected
    /\ STATE_auditing /= STATE_error
    /\ STATE_generating_tla /= STATE_tlc_verifying
    /\ STATE_generating_tla /= STATE_tlc_verified
    /\ STATE_generating_tla /= STATE_tlaps_proving
    /\ STATE_generating_tla /= STATE_certified
    /\ STATE_generating_tla /= STATE_rejected
    /\ STATE_generating_tla /= STATE_error
    /\ STATE_tlc_verifying /= STATE_tlc_verified
    /\ STATE_tlc_verifying /= STATE_tlaps_proving
    /\ STATE_tlc_verifying /= STATE_certified
    /\ STATE_tlc_verifying /= STATE_rejected
    /\ STATE_tlc_verifying /= STATE_error
    /\ STATE_tlc_verified /= STATE_tlaps_proving
    /\ STATE_tlc_verified /= STATE_certified
    /\ STATE_tlc_verified /= STATE_rejected
    /\ STATE_tlc_verified /= STATE_error
    /\ STATE_tlaps_proving /= STATE_certified
    /\ STATE_tlaps_proving /= STATE_rejected
    /\ STATE_tlaps_proving /= STATE_error
    /\ STATE_certified /= STATE_rejected
    /\ STATE_certified /= STATE_error
    /\ STATE_rejected /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_loading, STATE_auditing, STATE_generating_tla, STATE_tlc_verifying, STATE_tlc_verified, STATE_tlaps_proving, STATE_certified, STATE_rejected, STATE_error}
TerminalStates == {STATE_certified, STATE_rejected}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t1_certify *)
t_t1_certify ==
    /\ state = STATE_idle
    /\ state' = STATE_loading

(* Transition: t2_load *)
t_t2_load ==
    /\ state = STATE_loading
    /\ state' = STATE_auditing

(* Transition: t3_audit *)
t_t3_audit ==
    /\ state = STATE_auditing
    /\ state' = STATE_generating_tla

(* Transition: t4_generate *)
t_t4_generate ==
    /\ state = STATE_generating_tla
    /\ state' = STATE_tlc_verifying

(* Transition: t5_tlc *)
t_t5_tlc ==
    /\ state = STATE_tlc_verifying
    /\ state' = STATE_tlc_verified

(* Transition: t6_tlaps_start *)
t_t6_tlaps_start ==
    /\ state = STATE_tlc_verified
    /\ state' = STATE_tlaps_proving

(* Transition: t7_tlaps_complete *)
t_t7_tlaps_complete ==
    /\ state = STATE_tlaps_proving
    /\ state' = STATE_certified

(* Transition: t8_quick_seal *)
t_t8_quick_seal ==
    /\ state = STATE_tlc_verified
    /\ state' = STATE_certified

(* Transition: t9_audit_fail *)
t_t9_audit_fail ==
    /\ state = STATE_auditing
    /\ state' = STATE_rejected

(* Transition: t10_tlc_fail *)
t_t10_tlc_fail ==
    /\ state = STATE_tlc_verifying
    /\ state' = STATE_rejected

(* Transition: t11_tlaps_fail *)
t_t11_tlaps_fail ==
    /\ state = STATE_tlaps_proving
    /\ state' = STATE_rejected

(* Transition: t12_error_any *)
t_t12_error_any ==
    /\ TRUE  \* Global transition
    /\ state' = STATE_error

(* Transition: t13_reset *)
t_t13_reset ==
    /\ TRUE  \* Global transition
    /\ state' = STATE_idle

(* Transition: t14_view_cert *)
t_t14_view_cert ==
    /\ state = STATE_certified
    /\ state' = STATE_certified

Next ==
    \/ t_t1_certify
    \/ t_t2_load
    \/ t_t3_audit
    \/ t_t4_generate
    \/ t_t5_tlc
    \/ t_t6_tlaps_start
    \/ t_t7_tlaps_complete
    \/ t_t8_quick_seal
    \/ t_t9_audit_fail
    \/ t_t10_tlc_fail
    \/ t_t11_tlaps_fail
    \/ t_t12_error_any
    \/ t_t13_reset
    \/ t_t14_view_cert

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA T1CertifyPreservesInv == Inv /\ t_t1_certify => Inv'
BY ConstantsDistinct DEF Inv, t_t1_certify, TypeInvariant, States

LEMMA T2LoadPreservesInv == Inv /\ t_t2_load => Inv'
BY ConstantsDistinct DEF Inv, t_t2_load, TypeInvariant, States

LEMMA T3AuditPreservesInv == Inv /\ t_t3_audit => Inv'
BY ConstantsDistinct DEF Inv, t_t3_audit, TypeInvariant, States

LEMMA T4GeneratePreservesInv == Inv /\ t_t4_generate => Inv'
BY ConstantsDistinct DEF Inv, t_t4_generate, TypeInvariant, States

LEMMA T5TlcPreservesInv == Inv /\ t_t5_tlc => Inv'
BY ConstantsDistinct DEF Inv, t_t5_tlc, TypeInvariant, States

LEMMA T6TlapsStartPreservesInv == Inv /\ t_t6_tlaps_start => Inv'
BY ConstantsDistinct DEF Inv, t_t6_tlaps_start, TypeInvariant, States

LEMMA T7TlapsCompletePreservesInv == Inv /\ t_t7_tlaps_complete => Inv'
BY ConstantsDistinct DEF Inv, t_t7_tlaps_complete, TypeInvariant, States

LEMMA T8QuickSealPreservesInv == Inv /\ t_t8_quick_seal => Inv'
BY ConstantsDistinct DEF Inv, t_t8_quick_seal, TypeInvariant, States

LEMMA T9AudifailPreservesInv == Inv /\ t_t9_audit_fail => Inv'
BY ConstantsDistinct DEF Inv, t_t9_audit_fail, TypeInvariant, States

LEMMA T10TlcFailPreservesInv == Inv /\ t_t10_tlc_fail => Inv'
BY ConstantsDistinct DEF Inv, t_t10_tlc_fail, TypeInvariant, States

LEMMA T11TlapsFailPreservesInv == Inv /\ t_t11_tlaps_fail => Inv'
BY ConstantsDistinct DEF Inv, t_t11_tlaps_fail, TypeInvariant, States

LEMMA T12ErrorAnyPreservesInv == Inv /\ t_t12_error_any => Inv'
BY ConstantsDistinct DEF Inv, t_t12_error_any, TypeInvariant, States

LEMMA T13ResetPreservesInv == Inv /\ t_t13_reset => Inv'
BY ConstantsDistinct DEF Inv, t_t13_reset, TypeInvariant, States

LEMMA T14ViewCertPreservesInv == Inv /\ t_t14_view_cert => Inv'
BY ConstantsDistinct DEF Inv, t_t14_view_cert, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY T1CertifyPreservesInv, T2LoadPreservesInv, T3AuditPreservesInv, T4GeneratePreservesInv, T5TlcPreservesInv, T6TlapsStartPreservesInv, T7TlapsCompletePreservesInv, T8QuickSealPreservesInv, T9AudifailPreservesInv, T10TlcFailPreservesInv, T11TlapsFailPreservesInv, T12ErrorAnyPreservesInv, T13ResetPreservesInv, T14ViewCertPreservesInv DEF Next

THEOREM InductiveInvariant == Inv /\ [Next]_vars => Inv'
BY NextPreservesInv, StutterPreservesInv DEF vars

THEOREM TypeSafety == Spec => []Inv
<1>1. Init => Inv
  BY InitEstablishesInv
<1>2. Inv /\ [Next]_vars => Inv'
  BY InductiveInvariant
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

=============================================================================