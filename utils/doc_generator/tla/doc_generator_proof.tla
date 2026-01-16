--------------------------- MODULE doc_generator_proofs ---------------------------
(*
 * L++ Blueprint: Documentation Generator
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_discovering, STATE_generating_graphs, STATE_generating_logic, STATE_generating_functions, STATE_generating_mermaid, STATE_updating_readmes, STATE_generating_report, STATE_generating_dashboard, STATE_complete, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_discovering
    /\ STATE_idle /= STATE_generating_graphs
    /\ STATE_idle /= STATE_generating_logic
    /\ STATE_idle /= STATE_generating_functions
    /\ STATE_idle /= STATE_generating_mermaid
    /\ STATE_idle /= STATE_updating_readmes
    /\ STATE_idle /= STATE_generating_report
    /\ STATE_idle /= STATE_generating_dashboard
    /\ STATE_idle /= STATE_complete
    /\ STATE_idle /= STATE_error
    /\ STATE_discovering /= STATE_generating_graphs
    /\ STATE_discovering /= STATE_generating_logic
    /\ STATE_discovering /= STATE_generating_functions
    /\ STATE_discovering /= STATE_generating_mermaid
    /\ STATE_discovering /= STATE_updating_readmes
    /\ STATE_discovering /= STATE_generating_report
    /\ STATE_discovering /= STATE_generating_dashboard
    /\ STATE_discovering /= STATE_complete
    /\ STATE_discovering /= STATE_error
    /\ STATE_generating_graphs /= STATE_generating_logic
    /\ STATE_generating_graphs /= STATE_generating_functions
    /\ STATE_generating_graphs /= STATE_generating_mermaid
    /\ STATE_generating_graphs /= STATE_updating_readmes
    /\ STATE_generating_graphs /= STATE_generating_report
    /\ STATE_generating_graphs /= STATE_generating_dashboard
    /\ STATE_generating_graphs /= STATE_complete
    /\ STATE_generating_graphs /= STATE_error
    /\ STATE_generating_logic /= STATE_generating_functions
    /\ STATE_generating_logic /= STATE_generating_mermaid
    /\ STATE_generating_logic /= STATE_updating_readmes
    /\ STATE_generating_logic /= STATE_generating_report
    /\ STATE_generating_logic /= STATE_generating_dashboard
    /\ STATE_generating_logic /= STATE_complete
    /\ STATE_generating_logic /= STATE_error
    /\ STATE_generating_functions /= STATE_generating_mermaid
    /\ STATE_generating_functions /= STATE_updating_readmes
    /\ STATE_generating_functions /= STATE_generating_report
    /\ STATE_generating_functions /= STATE_generating_dashboard
    /\ STATE_generating_functions /= STATE_complete
    /\ STATE_generating_functions /= STATE_error
    /\ STATE_generating_mermaid /= STATE_updating_readmes
    /\ STATE_generating_mermaid /= STATE_generating_report
    /\ STATE_generating_mermaid /= STATE_generating_dashboard
    /\ STATE_generating_mermaid /= STATE_complete
    /\ STATE_generating_mermaid /= STATE_error
    /\ STATE_updating_readmes /= STATE_generating_report
    /\ STATE_updating_readmes /= STATE_generating_dashboard
    /\ STATE_updating_readmes /= STATE_complete
    /\ STATE_updating_readmes /= STATE_error
    /\ STATE_generating_report /= STATE_generating_dashboard
    /\ STATE_generating_report /= STATE_complete
    /\ STATE_generating_report /= STATE_error
    /\ STATE_generating_dashboard /= STATE_complete
    /\ STATE_generating_dashboard /= STATE_error
    /\ STATE_complete /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_discovering, STATE_generating_graphs, STATE_generating_logic, STATE_generating_functions, STATE_generating_mermaid, STATE_updating_readmes, STATE_generating_report, STATE_generating_dashboard, STATE_complete, STATE_error}
TerminalStates == {STATE_complete, STATE_error}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t0 *)
t_t0 ==
    /\ state = STATE_idle
    /\ state' = STATE_idle

(* Transition: t1 *)
t_t1 ==
    /\ state = STATE_idle
    /\ state' = STATE_discovering

(* Transition: t2 *)
t_t2 ==
    /\ state = STATE_discovering
    /\ state' = STATE_generating_graphs

(* Transition: t3 *)
t_t3 ==
    /\ state = STATE_discovering
    /\ state' = STATE_generating_mermaid

(* Transition: t4 *)
t_t4 ==
    /\ state = STATE_discovering
    /\ state' = STATE_error

(* Transition: t5 *)
t_t5 ==
    /\ state = STATE_generating_graphs
    /\ state' = STATE_generating_logic

(* Transition: t6 *)
t_t6 ==
    /\ state = STATE_generating_graphs
    /\ state' = STATE_generating_mermaid

(* Transition: t7 *)
t_t7 ==
    /\ state = STATE_generating_logic
    /\ state' = STATE_generating_functions

(* Transition: t8 *)
t_t8 ==
    /\ state = STATE_generating_logic
    /\ state' = STATE_generating_mermaid

(* Transition: t9 *)
t_t9 ==
    /\ state = STATE_generating_functions
    /\ state' = STATE_generating_mermaid

(* Transition: t10 *)
t_t10 ==
    /\ state = STATE_generating_mermaid
    /\ state' = STATE_updating_readmes

(* Transition: t11 *)
t_t11 ==
    /\ state = STATE_generating_mermaid
    /\ state' = STATE_generating_report

(* Transition: t12 *)
t_t12 ==
    /\ state = STATE_updating_readmes
    /\ state' = STATE_generating_report

(* Transition: t13 *)
t_t13 ==
    /\ state = STATE_updating_readmes
    /\ state' = STATE_generating_dashboard

(* Transition: t14 *)
t_t14 ==
    /\ state = STATE_generating_report
    /\ state' = STATE_generating_dashboard

(* Transition: t15 *)
t_t15 ==
    /\ state = STATE_generating_report
    /\ state' = STATE_complete

(* Transition: t16 *)
t_t16 ==
    /\ state = STATE_generating_dashboard
    /\ state' = STATE_complete

(* Transition: t17 *)
t_t17 ==
    /\ TRUE  \* Global transition
    /\ state' = STATE_error

(* Transition: t18 *)
t_t18 ==
    /\ state = STATE_error
    /\ state' = STATE_idle

(* Transition: t19 *)
t_t19 ==
    /\ state = STATE_complete
    /\ state' = STATE_idle

Next ==
    \/ t_t0
    \/ t_t1
    \/ t_t2
    \/ t_t3
    \/ t_t4
    \/ t_t5
    \/ t_t6
    \/ t_t7
    \/ t_t8
    \/ t_t9
    \/ t_t10
    \/ t_t11
    \/ t_t12
    \/ t_t13
    \/ t_t14
    \/ t_t15
    \/ t_t16
    \/ t_t17
    \/ t_t18
    \/ t_t19

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA T0PreservesInv == Inv /\ t_t0 => Inv'
BY ConstantsDistinct DEF Inv, t_t0, TypeInvariant, States

LEMMA T1PreservesInv == Inv /\ t_t1 => Inv'
BY ConstantsDistinct DEF Inv, t_t1, TypeInvariant, States

LEMMA T2PreservesInv == Inv /\ t_t2 => Inv'
BY ConstantsDistinct DEF Inv, t_t2, TypeInvariant, States

LEMMA T3PreservesInv == Inv /\ t_t3 => Inv'
BY ConstantsDistinct DEF Inv, t_t3, TypeInvariant, States

LEMMA T4PreservesInv == Inv /\ t_t4 => Inv'
BY ConstantsDistinct DEF Inv, t_t4, TypeInvariant, States

LEMMA T5PreservesInv == Inv /\ t_t5 => Inv'
BY ConstantsDistinct DEF Inv, t_t5, TypeInvariant, States

LEMMA T6PreservesInv == Inv /\ t_t6 => Inv'
BY ConstantsDistinct DEF Inv, t_t6, TypeInvariant, States

LEMMA T7PreservesInv == Inv /\ t_t7 => Inv'
BY ConstantsDistinct DEF Inv, t_t7, TypeInvariant, States

LEMMA T8PreservesInv == Inv /\ t_t8 => Inv'
BY ConstantsDistinct DEF Inv, t_t8, TypeInvariant, States

LEMMA T9PreservesInv == Inv /\ t_t9 => Inv'
BY ConstantsDistinct DEF Inv, t_t9, TypeInvariant, States

LEMMA T10PreservesInv == Inv /\ t_t10 => Inv'
BY ConstantsDistinct DEF Inv, t_t10, TypeInvariant, States

LEMMA T11PreservesInv == Inv /\ t_t11 => Inv'
BY ConstantsDistinct DEF Inv, t_t11, TypeInvariant, States

LEMMA T12PreservesInv == Inv /\ t_t12 => Inv'
BY ConstantsDistinct DEF Inv, t_t12, TypeInvariant, States

LEMMA T13PreservesInv == Inv /\ t_t13 => Inv'
BY ConstantsDistinct DEF Inv, t_t13, TypeInvariant, States

LEMMA T14PreservesInv == Inv /\ t_t14 => Inv'
BY ConstantsDistinct DEF Inv, t_t14, TypeInvariant, States

LEMMA T15PreservesInv == Inv /\ t_t15 => Inv'
BY ConstantsDistinct DEF Inv, t_t15, TypeInvariant, States

LEMMA T16PreservesInv == Inv /\ t_t16 => Inv'
BY ConstantsDistinct DEF Inv, t_t16, TypeInvariant, States

LEMMA T17PreservesInv == Inv /\ t_t17 => Inv'
BY ConstantsDistinct DEF Inv, t_t17, TypeInvariant, States

LEMMA T18PreservesInv == Inv /\ t_t18 => Inv'
BY ConstantsDistinct DEF Inv, t_t18, TypeInvariant, States

LEMMA T19PreservesInv == Inv /\ t_t19 => Inv'
BY ConstantsDistinct DEF Inv, t_t19, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY T0PreservesInv, T1PreservesInv, T2PreservesInv, T3PreservesInv, T4PreservesInv, T5PreservesInv, T6PreservesInv, T7PreservesInv, T8PreservesInv, T9PreservesInv, T10PreservesInv, T11PreservesInv, T12PreservesInv, T13PreservesInv, T14PreservesInv, T15PreservesInv, T16PreservesInv, T17PreservesInv, T18PreservesInv, T19PreservesInv DEF Next

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