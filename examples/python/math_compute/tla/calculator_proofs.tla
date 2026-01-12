--------------------------- MODULE calculator_proofs ---------------------------
(*
 * L++ Blueprint: L++ Calculator
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_has_operand, STATE_has_operator, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_has_operand /= STATE_has_operator
    /\ STATE_has_operand /= STATE_error
    /\ STATE_has_operator /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_has_operand, STATE_has_operator, STATE_error}
TerminalStates == {}

TypeInvariant == state \in States

Init == state = STATE_has_operand

(* Transition: t_set_operator *)
t_t_set_operator ==
    /\ state = STATE_has_operand
    /\ state' = STATE_has_operator

(* Transition: t_set_b *)
t_t_set_b ==
    /\ state = STATE_has_operator
    /\ state' = STATE_has_operand

(* Transition: t_set_a *)
t_t_set_a ==
    /\ state = STATE_has_operand
    /\ state' = STATE_has_operand

(* Transition: t_compute *)
t_t_compute ==
    /\ state = STATE_has_operand
    /\ state' = STATE_has_operand

(* Transition: t_div_zero *)
t_t_div_zero ==
    /\ state = STATE_has_operand
    /\ state' = STATE_error

(* Transition: t_clear *)
t_t_clear ==
    /\ TRUE  \* Global transition
    /\ state' = STATE_has_operand

Next ==
    \/ t_t_set_operator
    \/ t_t_set_b
    \/ t_t_set_a
    \/ t_t_compute
    \/ t_t_div_zero
    \/ t_t_clear

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA SeoperatorPreservesInv == Inv /\ t_t_set_operator => Inv'
BY ConstantsDistinct DEF Inv, t_t_set_operator, TypeInvariant, States

LEMMA SebPreservesInv == Inv /\ t_t_set_b => Inv'
BY ConstantsDistinct DEF Inv, t_t_set_b, TypeInvariant, States

LEMMA SeaPreservesInv == Inv /\ t_t_set_a => Inv'
BY ConstantsDistinct DEF Inv, t_t_set_a, TypeInvariant, States

LEMMA ComputePreservesInv == Inv /\ t_t_compute => Inv'
BY ConstantsDistinct DEF Inv, t_t_compute, TypeInvariant, States

LEMMA DivZeroPreservesInv == Inv /\ t_t_div_zero => Inv'
BY ConstantsDistinct DEF Inv, t_t_div_zero, TypeInvariant, States

LEMMA ClearPreservesInv == Inv /\ t_t_clear => Inv'
BY ConstantsDistinct DEF Inv, t_t_clear, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY SeoperatorPreservesInv, SebPreservesInv, SeaPreservesInv, ComputePreservesInv, DivZeroPreservesInv, ClearPreservesInv DEF Next

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