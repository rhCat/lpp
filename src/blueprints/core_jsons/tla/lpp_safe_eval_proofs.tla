--------------------------- MODULE lpp_safe_eval_proofs ---------------------------
(*
 * L++ Blueprint: L++ Safe Evaluator
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_parsing, STATE_validating, STATE_evaluating, STATE_complete, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_parsing
    /\ STATE_idle /= STATE_validating
    /\ STATE_idle /= STATE_evaluating
    /\ STATE_idle /= STATE_complete
    /\ STATE_idle /= STATE_error
    /\ STATE_parsing /= STATE_validating
    /\ STATE_parsing /= STATE_evaluating
    /\ STATE_parsing /= STATE_complete
    /\ STATE_parsing /= STATE_error
    /\ STATE_validating /= STATE_evaluating
    /\ STATE_validating /= STATE_complete
    /\ STATE_validating /= STATE_error
    /\ STATE_evaluating /= STATE_complete
    /\ STATE_evaluating /= STATE_error
    /\ STATE_complete /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_parsing, STATE_validating, STATE_evaluating, STATE_complete, STATE_error}
TerminalStates == {STATE_complete, STATE_error}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_eval *)
t_t_eval ==
    /\ state = STATE_idle
    /\ state' = STATE_parsing

(* Transition: t_parsed *)
t_t_parsed ==
    /\ state = STATE_parsing
    /\ state' = STATE_validating

(* Transition: t_validated *)
t_t_validated ==
    /\ state = STATE_validating
    /\ state' = STATE_evaluating

(* Transition: t_done *)
t_t_done ==
    /\ state = STATE_evaluating
    /\ state' = STATE_complete

(* Transition: t_parse_err *)
t_t_parse_err ==
    /\ state = STATE_parsing
    /\ state' = STATE_error

(* Transition: t_unsafe *)
t_t_unsafe ==
    /\ state = STATE_validating
    /\ state' = STATE_error

(* Transition: t_eval_err *)
t_t_eval_err ==
    /\ state = STATE_evaluating
    /\ state' = STATE_error

(* Transition: t_reset *)
t_t_reset ==
    /\ TRUE  \* Global transition
    /\ state' = STATE_idle

Next ==
    \/ t_t_eval
    \/ t_t_parsed
    \/ t_t_validated
    \/ t_t_done
    \/ t_t_parse_err
    \/ t_t_unsafe
    \/ t_t_eval_err
    \/ t_t_reset

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA EvalPreservesInv == Inv /\ t_t_eval => Inv'
BY ConstantsDistinct DEF Inv, t_t_eval, TypeInvariant, States

LEMMA ParsedPreservesInv == Inv /\ t_t_parsed => Inv'
BY ConstantsDistinct DEF Inv, t_t_parsed, TypeInvariant, States

LEMMA ValidatedPreservesInv == Inv /\ t_t_validated => Inv'
BY ConstantsDistinct DEF Inv, t_t_validated, TypeInvariant, States

LEMMA DonePreservesInv == Inv /\ t_t_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_done, TypeInvariant, States

LEMMA ParseErrPreservesInv == Inv /\ t_t_parse_err => Inv'
BY ConstantsDistinct DEF Inv, t_t_parse_err, TypeInvariant, States

LEMMA UnsafePreservesInv == Inv /\ t_t_unsafe => Inv'
BY ConstantsDistinct DEF Inv, t_t_unsafe, TypeInvariant, States

LEMMA EvalErrPreservesInv == Inv /\ t_t_eval_err => Inv'
BY ConstantsDistinct DEF Inv, t_t_eval_err, TypeInvariant, States

LEMMA ResetPreservesInv == Inv /\ t_t_reset => Inv'
BY ConstantsDistinct DEF Inv, t_t_reset, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY EvalPreservesInv, ParsedPreservesInv, ValidatedPreservesInv, DonePreservesInv, ParseErrPreservesInv, UnsafePreservesInv, EvalErrPreservesInv, ResetPreservesInv DEF Next

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