--------------------------- MODULE child_processor_proofs ---------------------------
(*
 * L++ Blueprint: Child Processor
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_init, STATE_step1, STATE_step2, STATE_step3, STATE_done

ASSUME ConstantsDistinct ==
    /\ STATE_init /= STATE_step1
    /\ STATE_init /= STATE_step2
    /\ STATE_init /= STATE_step3
    /\ STATE_init /= STATE_done
    /\ STATE_step1 /= STATE_step2
    /\ STATE_step1 /= STATE_step3
    /\ STATE_step1 /= STATE_done
    /\ STATE_step2 /= STATE_step3
    /\ STATE_step2 /= STATE_done
    /\ STATE_step3 /= STATE_done

VARIABLE state

vars == <<state>>

States == {STATE_init, STATE_step1, STATE_step2, STATE_step3, STATE_done}
TerminalStates == {STATE_done}

TypeInvariant == state \in States

Init == state = STATE_init

(* Transition: t_start_processing *)
t_t_start_processing ==
    /\ state = STATE_init
    /\ state' = STATE_step1

(* Transition: t_step1_execute *)
t_t_step1_execute ==
    /\ state = STATE_step1
    /\ state' = STATE_step2

(* Transition: t_step2_execute *)
t_t_step2_execute ==
    /\ state = STATE_step2
    /\ state' = STATE_step3

(* Transition: t_step3_execute *)
t_t_step3_execute ==
    /\ state = STATE_step3
    /\ state' = STATE_done

(* Transition: t_complete *)
t_t_complete ==
    /\ state = STATE_done
    /\ state' = STATE_done

Next ==
    \/ t_t_start_processing
    \/ t_t_step1_execute
    \/ t_t_step2_execute
    \/ t_t_step3_execute
    \/ t_t_complete

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA StarprocessingPreservesInv == Inv /\ t_t_start_processing => Inv'
BY ConstantsDistinct DEF Inv, t_t_start_processing, TypeInvariant, States

LEMMA Step1ExecutePreservesInv == Inv /\ t_t_step1_execute => Inv'
BY ConstantsDistinct DEF Inv, t_t_step1_execute, TypeInvariant, States

LEMMA Step2ExecutePreservesInv == Inv /\ t_t_step2_execute => Inv'
BY ConstantsDistinct DEF Inv, t_t_step2_execute, TypeInvariant, States

LEMMA Step3ExecutePreservesInv == Inv /\ t_t_step3_execute => Inv'
BY ConstantsDistinct DEF Inv, t_t_step3_execute, TypeInvariant, States

LEMMA CompletePreservesInv == Inv /\ t_t_complete => Inv'
BY ConstantsDistinct DEF Inv, t_t_complete, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY StarprocessingPreservesInv, Step1ExecutePreservesInv, Step2ExecutePreservesInv, Step3ExecutePreservesInv, CompletePreservesInv DEF Next

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