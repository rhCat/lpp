--------------------------- MODULE lpp_tla_validator_proofs ---------------------------
(*
 * L++ Blueprint: L++ TLA+ Validator
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_extracting, STATE_generating, STATE_validating, STATE_saving, STATE_complete, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_extracting
    /\ STATE_idle /= STATE_generating
    /\ STATE_idle /= STATE_validating
    /\ STATE_idle /= STATE_saving
    /\ STATE_idle /= STATE_complete
    /\ STATE_idle /= STATE_error
    /\ STATE_extracting /= STATE_generating
    /\ STATE_extracting /= STATE_validating
    /\ STATE_extracting /= STATE_saving
    /\ STATE_extracting /= STATE_complete
    /\ STATE_extracting /= STATE_error
    /\ STATE_generating /= STATE_validating
    /\ STATE_generating /= STATE_saving
    /\ STATE_generating /= STATE_complete
    /\ STATE_generating /= STATE_error
    /\ STATE_validating /= STATE_saving
    /\ STATE_validating /= STATE_complete
    /\ STATE_validating /= STATE_error
    /\ STATE_saving /= STATE_complete
    /\ STATE_saving /= STATE_error
    /\ STATE_complete /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_extracting, STATE_generating, STATE_validating, STATE_saving, STATE_complete, STATE_error}
TerminalStates == {STATE_complete, STATE_error}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_generate *)
t_t_generate ==
    /\ state = STATE_idle
    /\ state' = STATE_extracting

(* Transition: t_extracted *)
t_t_extracted ==
    /\ state = STATE_extracting
    /\ state' = STATE_generating

(* Transition: t_generated *)
t_t_generated ==
    /\ state = STATE_generating
    /\ state' = STATE_validating

(* Transition: t_skip_validate *)
t_t_skip_validate ==
    /\ state = STATE_generating
    /\ state' = STATE_saving

(* Transition: t_validated *)
t_t_validated ==
    /\ state = STATE_validating
    /\ state' = STATE_saving

(* Transition: t_saved *)
t_t_saved ==
    /\ state = STATE_saving
    /\ state' = STATE_complete

(* Transition: t_extract_err *)
t_t_extract_err ==
    /\ state = STATE_extracting
    /\ state' = STATE_error

(* Transition: t_gen_err *)
t_t_gen_err ==
    /\ state = STATE_generating
    /\ state' = STATE_error

(* Transition: t_validate_err *)
t_t_validate_err ==
    /\ state = STATE_validating
    /\ state' = STATE_error

(* Transition: t_save_err *)
t_t_save_err ==
    /\ state = STATE_saving
    /\ state' = STATE_error

(* Transition: t_reset *)
t_t_reset ==
    /\ TRUE  \* Global transition
    /\ state' = STATE_idle

Next ==
    \/ t_t_generate
    \/ t_t_extracted
    \/ t_t_generated
    \/ t_t_skip_validate
    \/ t_t_validated
    \/ t_t_saved
    \/ t_t_extract_err
    \/ t_t_gen_err
    \/ t_t_validate_err
    \/ t_t_save_err
    \/ t_t_reset

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA GeneratePreservesInv == Inv /\ t_t_generate => Inv'
BY ConstantsDistinct DEF Inv, t_t_generate, TypeInvariant, States

LEMMA ExtractedPreservesInv == Inv /\ t_t_extracted => Inv'
BY ConstantsDistinct DEF Inv, t_t_extracted, TypeInvariant, States

LEMMA GeneratedPreservesInv == Inv /\ t_t_generated => Inv'
BY ConstantsDistinct DEF Inv, t_t_generated, TypeInvariant, States

LEMMA SkipValidatePreservesInv == Inv /\ t_t_skip_validate => Inv'
BY ConstantsDistinct DEF Inv, t_t_skip_validate, TypeInvariant, States

LEMMA ValidatedPreservesInv == Inv /\ t_t_validated => Inv'
BY ConstantsDistinct DEF Inv, t_t_validated, TypeInvariant, States

LEMMA SavedPreservesInv == Inv /\ t_t_saved => Inv'
BY ConstantsDistinct DEF Inv, t_t_saved, TypeInvariant, States

LEMMA ExtracerrPreservesInv == Inv /\ t_t_extract_err => Inv'
BY ConstantsDistinct DEF Inv, t_t_extract_err, TypeInvariant, States

LEMMA GenErrPreservesInv == Inv /\ t_t_gen_err => Inv'
BY ConstantsDistinct DEF Inv, t_t_gen_err, TypeInvariant, States

LEMMA ValidateErrPreservesInv == Inv /\ t_t_validate_err => Inv'
BY ConstantsDistinct DEF Inv, t_t_validate_err, TypeInvariant, States

LEMMA SaveErrPreservesInv == Inv /\ t_t_save_err => Inv'
BY ConstantsDistinct DEF Inv, t_t_save_err, TypeInvariant, States

LEMMA ResetPreservesInv == Inv /\ t_t_reset => Inv'
BY ConstantsDistinct DEF Inv, t_t_reset, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY GeneratePreservesInv, ExtractedPreservesInv, GeneratedPreservesInv, SkipValidatePreservesInv, ValidatedPreservesInv, SavedPreservesInv, ExtracerrPreservesInv, GenErrPreservesInv, ValidateErrPreservesInv, SaveErrPreservesInv, ResetPreservesInv DEF Next

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