--------------------------- MODULE py2lpp_blueprint_gen_proofs ---------------------------
(*
 * L++ Blueprint: Blueprint Generator
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_generating, STATE_done, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_generating
    /\ STATE_idle /= STATE_done
    /\ STATE_idle /= STATE_error
    /\ STATE_generating /= STATE_done
    /\ STATE_generating /= STATE_error
    /\ STATE_done /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_generating, STATE_done, STATE_error}
TerminalStates == {STATE_done, STATE_error}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_start *)
t_t_start ==
    /\ state = STATE_idle
    /\ state' = STATE_generating

(* Transition: t_done *)
t_t_done ==
    /\ state = STATE_generating
    /\ state' = STATE_done

(* Transition: t_error *)
t_t_error ==
    /\ state = STATE_generating
    /\ state' = STATE_error

Next ==
    \/ t_t_start
    \/ t_t_done
    \/ t_t_error

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA StartPreservesInv == Inv /\ t_t_start => Inv'
BY ConstantsDistinct DEF Inv, t_t_start, TypeInvariant, States

LEMMA DonePreservesInv == Inv /\ t_t_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_done, TypeInvariant, States

LEMMA ErrorPreservesInv == Inv /\ t_t_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_error, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY StartPreservesInv, DonePreservesInv, ErrorPreservesInv DEF Next

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