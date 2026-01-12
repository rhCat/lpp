--------------------------- MODULE graph_visualizer_proofs ---------------------------
(*
 * L++ Blueprint: Graph Visualizer
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_generating, STATE_done

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_generating
    /\ STATE_idle /= STATE_done
    /\ STATE_generating /= STATE_done

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_generating, STATE_done}
TerminalStates == {STATE_done}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_start *)
t_t_start ==
    /\ state = STATE_idle
    /\ state' = STATE_generating

(* Transition: t_generate *)
t_t_generate ==
    /\ state = STATE_generating
    /\ state' = STATE_done

Next ==
    \/ t_t_start
    \/ t_t_generate

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA StartPreservesInv == Inv /\ t_t_start => Inv'
BY ConstantsDistinct DEF Inv, t_t_start, TypeInvariant, States

LEMMA GeneratePreservesInv == Inv /\ t_t_generate => Inv'
BY ConstantsDistinct DEF Inv, t_t_generate, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY StartPreservesInv, GeneratePreservesInv DEF Next

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