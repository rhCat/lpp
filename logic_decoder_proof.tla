--------------------------- MODULE logic_decoder_proofs ---------------------------
(*
 * L++ Blueprint: Python Logic Decoder
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_parsing, STATE_analyzing, STATE_inferring, STATE_generating

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_parsing
    /\ STATE_idle /= STATE_analyzing
    /\ STATE_idle /= STATE_inferring
    /\ STATE_idle /= STATE_generating
    /\ STATE_parsing /= STATE_analyzing
    /\ STATE_parsing /= STATE_inferring
    /\ STATE_parsing /= STATE_generating
    /\ STATE_analyzing /= STATE_inferring
    /\ STATE_analyzing /= STATE_generating
    /\ STATE_inferring /= STATE_generating

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_parsing, STATE_analyzing, STATE_inferring, STATE_generating}
TerminalStates == {STATE_error, STATE_complete}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t1_load *)
t_t1_load ==
    /\ state = STATE_idle
    /\ state' = STATE_parsing

(* Transition: t2_parse *)
t_t2_parse ==
    /\ state = STATE_parsing
    /\ state' = STATE_analyzing

(* Transition: t3_analyze *)
t_t3_analyze ==
    /\ state = STATE_analyzing
    /\ state' = STATE_inferring

(* Transition: t4_infer *)
t_t4_infer ==
    /\ state = STATE_inferring
    /\ state' = STATE_generating

(* Transition: t5_generate *)
t_t5_generate ==
    /\ state = STATE_generating
    /\ state' = STATE_complete

(* Transition: t6_error_parse *)
t_t6_error_parse ==
    /\ state = STATE_parsing
    /\ state' = STATE_error

(* Transition: t7_error_analyze *)
t_t7_error_analyze ==
    /\ state = STATE_analyzing
    /\ state' = STATE_error

(* Transition: t8_error_infer *)
t_t8_error_infer ==
    /\ state = STATE_inferring
    /\ state' = STATE_error

(* Transition: t9_reset *)
t_t9_reset ==
    /\ state = STATE_complete
    /\ state' = STATE_idle

(* Transition: t10_error_reset *)
t_t10_error_reset ==
    /\ state = STATE_error
    /\ state' = STATE_idle

Next ==
    \/ t_t1_load
    \/ t_t2_parse
    \/ t_t3_analyze
    \/ t_t4_infer
    \/ t_t5_generate
    \/ t_t6_error_parse
    \/ t_t7_error_analyze
    \/ t_t8_error_infer
    \/ t_t9_reset
    \/ t_t10_error_reset

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA T1LoadPreservesInv == Inv /\ t_t1_load => Inv'
BY ConstantsDistinct DEF Inv, t_t1_load, TypeInvariant, States

LEMMA T2ParsePreservesInv == Inv /\ t_t2_parse => Inv'
BY ConstantsDistinct DEF Inv, t_t2_parse, TypeInvariant, States

LEMMA T3AnalyzePreservesInv == Inv /\ t_t3_analyze => Inv'
BY ConstantsDistinct DEF Inv, t_t3_analyze, TypeInvariant, States

LEMMA T4InferPreservesInv == Inv /\ t_t4_infer => Inv'
BY ConstantsDistinct DEF Inv, t_t4_infer, TypeInvariant, States

LEMMA T5GeneratePreservesInv == Inv /\ t_t5_generate => Inv'
BY ConstantsDistinct DEF Inv, t_t5_generate, TypeInvariant, States

LEMMA T6ErrorParsePreservesInv == Inv /\ t_t6_error_parse => Inv'
BY ConstantsDistinct DEF Inv, t_t6_error_parse, TypeInvariant, States

LEMMA T7ErrorAnalyzePreservesInv == Inv /\ t_t7_error_analyze => Inv'
BY ConstantsDistinct DEF Inv, t_t7_error_analyze, TypeInvariant, States

LEMMA T8ErrorInferPreservesInv == Inv /\ t_t8_error_infer => Inv'
BY ConstantsDistinct DEF Inv, t_t8_error_infer, TypeInvariant, States

LEMMA T9ResetPreservesInv == Inv /\ t_t9_reset => Inv'
BY ConstantsDistinct DEF Inv, t_t9_reset, TypeInvariant, States

LEMMA T10ErrorResetPreservesInv == Inv /\ t_t10_error_reset => Inv'
BY ConstantsDistinct DEF Inv, t_t10_error_reset, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY T1LoadPreservesInv, T2ParsePreservesInv, T3AnalyzePreservesInv, T4InferPreservesInv, T5GeneratePreservesInv, T6ErrorParsePreservesInv, T7ErrorAnalyzePreservesInv, T8ErrorInferPreservesInv, T9ResetPreservesInv, T10ErrorResetPreservesInv DEF Next

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