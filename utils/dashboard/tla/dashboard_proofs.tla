--------------------------- MODULE dashboard_proofs ---------------------------
(*
 * L++ Blueprint: L++ Tools Dashboard
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_scanning, STATE_analyzing, STATE_categorizing, STATE_generating, STATE_complete, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_scanning
    /\ STATE_idle /= STATE_analyzing
    /\ STATE_idle /= STATE_categorizing
    /\ STATE_idle /= STATE_generating
    /\ STATE_idle /= STATE_complete
    /\ STATE_idle /= STATE_error
    /\ STATE_scanning /= STATE_analyzing
    /\ STATE_scanning /= STATE_categorizing
    /\ STATE_scanning /= STATE_generating
    /\ STATE_scanning /= STATE_complete
    /\ STATE_scanning /= STATE_error
    /\ STATE_analyzing /= STATE_categorizing
    /\ STATE_analyzing /= STATE_generating
    /\ STATE_analyzing /= STATE_complete
    /\ STATE_analyzing /= STATE_error
    /\ STATE_categorizing /= STATE_generating
    /\ STATE_categorizing /= STATE_complete
    /\ STATE_categorizing /= STATE_error
    /\ STATE_generating /= STATE_complete
    /\ STATE_generating /= STATE_error
    /\ STATE_complete /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_scanning, STATE_analyzing, STATE_categorizing, STATE_generating, STATE_complete, STATE_error}
TerminalStates == {STATE_complete}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_start_scan *)
t_t_start_scan ==
    /\ state = STATE_idle
    /\ state' = STATE_scanning

(* Transition: t_scan_error *)
t_t_scan_error ==
    /\ state = STATE_scanning
    /\ state' = STATE_error

(* Transition: t_scan_done *)
t_t_scan_done ==
    /\ state = STATE_scanning
    /\ state' = STATE_analyzing

(* Transition: t_analyze_error *)
t_t_analyze_error ==
    /\ state = STATE_analyzing
    /\ state' = STATE_error

(* Transition: t_analyze_done *)
t_t_analyze_done ==
    /\ state = STATE_analyzing
    /\ state' = STATE_categorizing

(* Transition: t_categorize_error *)
t_t_categorize_error ==
    /\ state = STATE_categorizing
    /\ state' = STATE_error

(* Transition: t_categorize_done *)
t_t_categorize_done ==
    /\ state = STATE_categorizing
    /\ state' = STATE_generating

(* Transition: t_generate_error *)
t_t_generate_error ==
    /\ state = STATE_generating
    /\ state' = STATE_error

(* Transition: t_generate_done *)
t_t_generate_done ==
    /\ state = STATE_generating
    /\ state' = STATE_complete

(* Transition: t_reset *)
t_t_reset ==
    /\ TRUE  \* Global transition
    /\ state' = STATE_idle

Next ==
    \/ t_t_start_scan
    \/ t_t_scan_error
    \/ t_t_scan_done
    \/ t_t_analyze_error
    \/ t_t_analyze_done
    \/ t_t_categorize_error
    \/ t_t_categorize_done
    \/ t_t_generate_error
    \/ t_t_generate_done
    \/ t_t_reset

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA StarscanPreservesInv == Inv /\ t_t_start_scan => Inv'
BY ConstantsDistinct DEF Inv, t_t_start_scan, TypeInvariant, States

LEMMA ScanErrorPreservesInv == Inv /\ t_t_scan_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_scan_error, TypeInvariant, States

LEMMA ScanDonePreservesInv == Inv /\ t_t_scan_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_scan_done, TypeInvariant, States

LEMMA AnalyzeErrorPreservesInv == Inv /\ t_t_analyze_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_analyze_error, TypeInvariant, States

LEMMA AnalyzeDonePreservesInv == Inv /\ t_t_analyze_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_analyze_done, TypeInvariant, States

LEMMA CategorizeErrorPreservesInv == Inv /\ t_t_categorize_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_categorize_error, TypeInvariant, States

LEMMA CategorizeDonePreservesInv == Inv /\ t_t_categorize_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_categorize_done, TypeInvariant, States

LEMMA GenerateErrorPreservesInv == Inv /\ t_t_generate_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_generate_error, TypeInvariant, States

LEMMA GenerateDonePreservesInv == Inv /\ t_t_generate_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_generate_done, TypeInvariant, States

LEMMA ResetPreservesInv == Inv /\ t_t_reset => Inv'
BY ConstantsDistinct DEF Inv, t_t_reset, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY StarscanPreservesInv, ScanErrorPreservesInv, ScanDonePreservesInv, AnalyzeErrorPreservesInv, AnalyzeDonePreservesInv, CategorizeErrorPreservesInv, CategorizeDonePreservesInv, GenerateErrorPreservesInv, GenerateDonePreservesInv, ResetPreservesInv DEF Next

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