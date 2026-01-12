--------------------------- MODULE lpp_compiler_proofs ---------------------------
(*
 * L++ Blueprint: L++ Blueprint Compiler
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_loading, STATE_validating, STATE_generating, STATE_writing, STATE_generating_tla, STATE_complete, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_loading
    /\ STATE_idle /= STATE_validating
    /\ STATE_idle /= STATE_generating
    /\ STATE_idle /= STATE_writing
    /\ STATE_idle /= STATE_generating_tla
    /\ STATE_idle /= STATE_complete
    /\ STATE_idle /= STATE_error
    /\ STATE_loading /= STATE_validating
    /\ STATE_loading /= STATE_generating
    /\ STATE_loading /= STATE_writing
    /\ STATE_loading /= STATE_generating_tla
    /\ STATE_loading /= STATE_complete
    /\ STATE_loading /= STATE_error
    /\ STATE_validating /= STATE_generating
    /\ STATE_validating /= STATE_writing
    /\ STATE_validating /= STATE_generating_tla
    /\ STATE_validating /= STATE_complete
    /\ STATE_validating /= STATE_error
    /\ STATE_generating /= STATE_writing
    /\ STATE_generating /= STATE_generating_tla
    /\ STATE_generating /= STATE_complete
    /\ STATE_generating /= STATE_error
    /\ STATE_writing /= STATE_generating_tla
    /\ STATE_writing /= STATE_complete
    /\ STATE_writing /= STATE_error
    /\ STATE_generating_tla /= STATE_complete
    /\ STATE_generating_tla /= STATE_error
    /\ STATE_complete /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_loading, STATE_validating, STATE_generating, STATE_writing, STATE_generating_tla, STATE_complete, STATE_error}
TerminalStates == {STATE_complete, STATE_error}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_compile *)
t_t_compile ==
    /\ state = STATE_idle
    /\ state' = STATE_loading

(* Transition: t_loaded *)
t_t_loaded ==
    /\ state = STATE_loading
    /\ state' = STATE_validating

(* Transition: t_validated *)
t_t_validated ==
    /\ state = STATE_validating
    /\ state' = STATE_generating

(* Transition: t_generated *)
t_t_generated ==
    /\ state = STATE_generating
    /\ state' = STATE_writing

(* Transition: t_skip_write *)
t_t_skip_write ==
    /\ state = STATE_generating
    /\ state' = STATE_generating_tla

(* Transition: t_skip_all *)
t_t_skip_all ==
    /\ state = STATE_generating
    /\ state' = STATE_complete

(* Transition: t_written *)
t_t_written ==
    /\ state = STATE_writing
    /\ state' = STATE_generating_tla

(* Transition: t_skip_tla *)
t_t_skip_tla ==
    /\ state = STATE_writing
    /\ state' = STATE_complete

(* Transition: t_tla_done *)
t_t_tla_done ==
    /\ state = STATE_generating_tla
    /\ state' = STATE_complete

(* Transition: t_load_err *)
t_t_load_err ==
    /\ state = STATE_loading
    /\ state' = STATE_error

(* Transition: t_validate_err *)
t_t_validate_err ==
    /\ state = STATE_validating
    /\ state' = STATE_error

(* Transition: t_gen_err *)
t_t_gen_err ==
    /\ state = STATE_generating
    /\ state' = STATE_error

(* Transition: t_write_err *)
t_t_write_err ==
    /\ state = STATE_writing
    /\ state' = STATE_error

(* Transition: t_tla_err *)
t_t_tla_err ==
    /\ state = STATE_generating_tla
    /\ state' = STATE_error

(* Transition: t_reset *)
t_t_reset ==
    /\ TRUE  \* Global transition
    /\ state' = STATE_idle

Next ==
    \/ t_t_compile
    \/ t_t_loaded
    \/ t_t_validated
    \/ t_t_generated
    \/ t_t_skip_write
    \/ t_t_skip_all
    \/ t_t_written
    \/ t_t_skip_tla
    \/ t_t_tla_done
    \/ t_t_load_err
    \/ t_t_validate_err
    \/ t_t_gen_err
    \/ t_t_write_err
    \/ t_t_tla_err
    \/ t_t_reset

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA CompilePreservesInv == Inv /\ t_t_compile => Inv'
BY ConstantsDistinct DEF Inv, t_t_compile, TypeInvariant, States

LEMMA LoadedPreservesInv == Inv /\ t_t_loaded => Inv'
BY ConstantsDistinct DEF Inv, t_t_loaded, TypeInvariant, States

LEMMA ValidatedPreservesInv == Inv /\ t_t_validated => Inv'
BY ConstantsDistinct DEF Inv, t_t_validated, TypeInvariant, States

LEMMA GeneratedPreservesInv == Inv /\ t_t_generated => Inv'
BY ConstantsDistinct DEF Inv, t_t_generated, TypeInvariant, States

LEMMA SkipWritePreservesInv == Inv /\ t_t_skip_write => Inv'
BY ConstantsDistinct DEF Inv, t_t_skip_write, TypeInvariant, States

LEMMA SkipAllPreservesInv == Inv /\ t_t_skip_all => Inv'
BY ConstantsDistinct DEF Inv, t_t_skip_all, TypeInvariant, States

LEMMA WrittenPreservesInv == Inv /\ t_t_written => Inv'
BY ConstantsDistinct DEF Inv, t_t_written, TypeInvariant, States

LEMMA SkipTlaPreservesInv == Inv /\ t_t_skip_tla => Inv'
BY ConstantsDistinct DEF Inv, t_t_skip_tla, TypeInvariant, States

LEMMA TlaDonePreservesInv == Inv /\ t_t_tla_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_tla_done, TypeInvariant, States

LEMMA LoadErrPreservesInv == Inv /\ t_t_load_err => Inv'
BY ConstantsDistinct DEF Inv, t_t_load_err, TypeInvariant, States

LEMMA ValidateErrPreservesInv == Inv /\ t_t_validate_err => Inv'
BY ConstantsDistinct DEF Inv, t_t_validate_err, TypeInvariant, States

LEMMA GenErrPreservesInv == Inv /\ t_t_gen_err => Inv'
BY ConstantsDistinct DEF Inv, t_t_gen_err, TypeInvariant, States

LEMMA WriteErrPreservesInv == Inv /\ t_t_write_err => Inv'
BY ConstantsDistinct DEF Inv, t_t_write_err, TypeInvariant, States

LEMMA TlaErrPreservesInv == Inv /\ t_t_tla_err => Inv'
BY ConstantsDistinct DEF Inv, t_t_tla_err, TypeInvariant, States

LEMMA ResetPreservesInv == Inv /\ t_t_reset => Inv'
BY ConstantsDistinct DEF Inv, t_t_reset, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY CompilePreservesInv, LoadedPreservesInv, ValidatedPreservesInv, GeneratedPreservesInv, SkipWritePreservesInv, SkipAllPreservesInv, WrittenPreservesInv, SkipTlaPreservesInv, TlaDonePreservesInv, LoadErrPreservesInv, ValidateErrPreservesInv, GenErrPreservesInv, WriteErrPreservesInv, TlaErrPreservesInv, ResetPreservesInv DEF Next

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