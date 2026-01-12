--------------------------- MODULE test_old_workflow_proofs ---------------------------
(*
 * L++ Blueprint: Test Old Workflow
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_processing, STATE_done

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_processing
    /\ STATE_idle /= STATE_done
    /\ STATE_processing /= STATE_done

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_processing, STATE_done}
TerminalStates == {STATE_d, STATE_o, STATE_n, STATE_e}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_start *)
t_t_start ==
    /\ state = STATE_idle
    /\ state' = STATE_processing

(* Transition: t_complete *)
t_t_complete ==
    /\ state = STATE_processing
    /\ state' = STATE_done

Next ==
    \/ t_t_start
    \/ t_t_complete

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA StartPreservesInv == Inv /\ t_t_start => Inv'
BY ConstantsDistinct DEF Inv, t_t_start, TypeInvariant, States

LEMMA CompletePreservesInv == Inv /\ t_t_complete => Inv'
BY ConstantsDistinct DEF Inv, t_t_complete, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY StartPreservesInv, CompletePreservesInv DEF Next

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