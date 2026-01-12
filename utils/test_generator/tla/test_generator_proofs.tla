--------------------------- MODULE test_generator_proofs ---------------------------
(*
 * L++ Blueprint: L++ Test Case Generator
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_loaded, STATE_analyzing, STATE_generating, STATE_complete, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_loaded
    /\ STATE_idle /= STATE_analyzing
    /\ STATE_idle /= STATE_generating
    /\ STATE_idle /= STATE_complete
    /\ STATE_idle /= STATE_error
    /\ STATE_loaded /= STATE_analyzing
    /\ STATE_loaded /= STATE_generating
    /\ STATE_loaded /= STATE_complete
    /\ STATE_loaded /= STATE_error
    /\ STATE_analyzing /= STATE_generating
    /\ STATE_analyzing /= STATE_complete
    /\ STATE_analyzing /= STATE_error
    /\ STATE_generating /= STATE_complete
    /\ STATE_generating /= STATE_error
    /\ STATE_complete /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_loaded, STATE_analyzing, STATE_generating, STATE_complete, STATE_error}
TerminalStates == {}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_load *)
t_t_load ==
    /\ state = STATE_idle
    /\ state' = STATE_loaded

(* Transition: t_reload *)
t_t_reload ==
    /\ state = STATE_loaded
    /\ state' = STATE_loaded

(* Transition: t_reload_from_complete *)
t_t_reload_from_complete ==
    /\ state = STATE_complete
    /\ state' = STATE_loaded

(* Transition: t_analyze *)
t_t_analyze ==
    /\ state = STATE_loaded
    /\ state' = STATE_analyzing

(* Transition: t_generate_all *)
t_t_generate_all ==
    /\ state = STATE_analyzing
    /\ state' = STATE_generating

(* Transition: t_generate_from_loaded *)
t_t_generate_from_loaded ==
    /\ state = STATE_loaded
    /\ state' = STATE_generating

(* Transition: t_combine *)
t_t_combine ==
    /\ state = STATE_generating
    /\ state' = STATE_complete

(* Transition: t_auto_combine *)
t_t_auto_combine ==
    /\ state = STATE_generating
    /\ state' = STATE_complete

(* Transition: t_format_json *)
t_t_format_json ==
    /\ state = STATE_complete
    /\ state' = STATE_complete

(* Transition: t_format_pytest *)
t_t_format_pytest ==
    /\ state = STATE_complete
    /\ state' = STATE_complete

(* Transition: t_export *)
t_t_export ==
    /\ state = STATE_complete
    /\ state' = STATE_complete

(* Transition: t_view_coverage *)
t_t_view_coverage ==
    /\ state = STATE_complete
    /\ state' = STATE_complete

(* Transition: t_reset *)
t_t_reset ==
    /\ state = STATE_complete
    /\ state' = STATE_idle

(* Transition: t_reset_from_error *)
t_t_reset_from_error ==
    /\ state = STATE_error
    /\ state' = STATE_idle

(* Transition: t_error_load *)
t_t_error_load ==
    /\ state = STATE_idle
    /\ state' = STATE_error

(* Transition: t_error_analyze *)
t_t_error_analyze ==
    /\ state = STATE_analyzing
    /\ state' = STATE_error

(* Transition: t_error_generate *)
t_t_error_generate ==
    /\ state = STATE_generating
    /\ state' = STATE_error

(* Transition: t_back_to_loaded *)
t_t_back_to_loaded ==
    /\ state = STATE_analyzing
    /\ state' = STATE_loaded

(* Transition: t_back_from_complete *)
t_t_back_from_complete ==
    /\ state = STATE_complete
    /\ state' = STATE_loaded

Next ==
    \/ t_t_load
    \/ t_t_reload
    \/ t_t_reload_from_complete
    \/ t_t_analyze
    \/ t_t_generate_all
    \/ t_t_generate_from_loaded
    \/ t_t_combine
    \/ t_t_auto_combine
    \/ t_t_format_json
    \/ t_t_format_pytest
    \/ t_t_export
    \/ t_t_view_coverage
    \/ t_t_reset
    \/ t_t_reset_from_error
    \/ t_t_error_load
    \/ t_t_error_analyze
    \/ t_t_error_generate
    \/ t_t_back_to_loaded
    \/ t_t_back_from_complete

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA LoadPreservesInv == Inv /\ t_t_load => Inv'
BY ConstantsDistinct DEF Inv, t_t_load, TypeInvariant, States

LEMMA ReloadPreservesInv == Inv /\ t_t_reload => Inv'
BY ConstantsDistinct DEF Inv, t_t_reload, TypeInvariant, States

LEMMA ReloadFromCompletePreservesInv == Inv /\ t_t_reload_from_complete => Inv'
BY ConstantsDistinct DEF Inv, t_t_reload_from_complete, TypeInvariant, States

LEMMA AnalyzePreservesInv == Inv /\ t_t_analyze => Inv'
BY ConstantsDistinct DEF Inv, t_t_analyze, TypeInvariant, States

LEMMA GenerateAllPreservesInv == Inv /\ t_t_generate_all => Inv'
BY ConstantsDistinct DEF Inv, t_t_generate_all, TypeInvariant, States

LEMMA GenerateFromLoadedPreservesInv == Inv /\ t_t_generate_from_loaded => Inv'
BY ConstantsDistinct DEF Inv, t_t_generate_from_loaded, TypeInvariant, States

LEMMA CombinePreservesInv == Inv /\ t_t_combine => Inv'
BY ConstantsDistinct DEF Inv, t_t_combine, TypeInvariant, States

LEMMA AutoCombinePreservesInv == Inv /\ t_t_auto_combine => Inv'
BY ConstantsDistinct DEF Inv, t_t_auto_combine, TypeInvariant, States

LEMMA FormajsonPreservesInv == Inv /\ t_t_format_json => Inv'
BY ConstantsDistinct DEF Inv, t_t_format_json, TypeInvariant, States

LEMMA FormapytestPreservesInv == Inv /\ t_t_format_pytest => Inv'
BY ConstantsDistinct DEF Inv, t_t_format_pytest, TypeInvariant, States

LEMMA ExportPreservesInv == Inv /\ t_t_export => Inv'
BY ConstantsDistinct DEF Inv, t_t_export, TypeInvariant, States

LEMMA ViewCoveragePreservesInv == Inv /\ t_t_view_coverage => Inv'
BY ConstantsDistinct DEF Inv, t_t_view_coverage, TypeInvariant, States

LEMMA ResetPreservesInv == Inv /\ t_t_reset => Inv'
BY ConstantsDistinct DEF Inv, t_t_reset, TypeInvariant, States

LEMMA ResefromErrorPreservesInv == Inv /\ t_t_reset_from_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_reset_from_error, TypeInvariant, States

LEMMA ErrorLoadPreservesInv == Inv /\ t_t_error_load => Inv'
BY ConstantsDistinct DEF Inv, t_t_error_load, TypeInvariant, States

LEMMA ErrorAnalyzePreservesInv == Inv /\ t_t_error_analyze => Inv'
BY ConstantsDistinct DEF Inv, t_t_error_analyze, TypeInvariant, States

LEMMA ErrorGeneratePreservesInv == Inv /\ t_t_error_generate => Inv'
BY ConstantsDistinct DEF Inv, t_t_error_generate, TypeInvariant, States

LEMMA BackToLoadedPreservesInv == Inv /\ t_t_back_to_loaded => Inv'
BY ConstantsDistinct DEF Inv, t_t_back_to_loaded, TypeInvariant, States

LEMMA BackFromCompletePreservesInv == Inv /\ t_t_back_from_complete => Inv'
BY ConstantsDistinct DEF Inv, t_t_back_from_complete, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY LoadPreservesInv, ReloadPreservesInv, ReloadFromCompletePreservesInv, AnalyzePreservesInv, GenerateAllPreservesInv, GenerateFromLoadedPreservesInv, CombinePreservesInv, AutoCombinePreservesInv, FormajsonPreservesInv, FormapytestPreservesInv, ExportPreservesInv, ViewCoveragePreservesInv, ResetPreservesInv, ResefromErrorPreservesInv, ErrorLoadPreservesInv, ErrorAnalyzePreservesInv, ErrorGeneratePreservesInv, BackToLoadedPreservesInv, BackFromCompletePreservesInv DEF Next

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