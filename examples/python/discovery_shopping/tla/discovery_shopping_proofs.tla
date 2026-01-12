--------------------------- MODULE discovery_shopping_proofs ---------------------------
(*
 * L++ Blueprint: Fit-First Discovery Shopping
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_quizzing, STATE_fetching, STATE_analyzing, STATE_ranking, STATE_browsing, STATE_comparing, STATE_detail, STATE_alerting, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_quizzing
    /\ STATE_idle /= STATE_fetching
    /\ STATE_idle /= STATE_analyzing
    /\ STATE_idle /= STATE_ranking
    /\ STATE_idle /= STATE_browsing
    /\ STATE_idle /= STATE_comparing
    /\ STATE_idle /= STATE_detail
    /\ STATE_idle /= STATE_alerting
    /\ STATE_idle /= STATE_error
    /\ STATE_quizzing /= STATE_fetching
    /\ STATE_quizzing /= STATE_analyzing
    /\ STATE_quizzing /= STATE_ranking
    /\ STATE_quizzing /= STATE_browsing
    /\ STATE_quizzing /= STATE_comparing
    /\ STATE_quizzing /= STATE_detail
    /\ STATE_quizzing /= STATE_alerting
    /\ STATE_quizzing /= STATE_error
    /\ STATE_fetching /= STATE_analyzing
    /\ STATE_fetching /= STATE_ranking
    /\ STATE_fetching /= STATE_browsing
    /\ STATE_fetching /= STATE_comparing
    /\ STATE_fetching /= STATE_detail
    /\ STATE_fetching /= STATE_alerting
    /\ STATE_fetching /= STATE_error
    /\ STATE_analyzing /= STATE_ranking
    /\ STATE_analyzing /= STATE_browsing
    /\ STATE_analyzing /= STATE_comparing
    /\ STATE_analyzing /= STATE_detail
    /\ STATE_analyzing /= STATE_alerting
    /\ STATE_analyzing /= STATE_error
    /\ STATE_ranking /= STATE_browsing
    /\ STATE_ranking /= STATE_comparing
    /\ STATE_ranking /= STATE_detail
    /\ STATE_ranking /= STATE_alerting
    /\ STATE_ranking /= STATE_error
    /\ STATE_browsing /= STATE_comparing
    /\ STATE_browsing /= STATE_detail
    /\ STATE_browsing /= STATE_alerting
    /\ STATE_browsing /= STATE_error
    /\ STATE_comparing /= STATE_detail
    /\ STATE_comparing /= STATE_alerting
    /\ STATE_comparing /= STATE_error
    /\ STATE_detail /= STATE_alerting
    /\ STATE_detail /= STATE_error
    /\ STATE_alerting /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_quizzing, STATE_fetching, STATE_analyzing, STATE_ranking, STATE_browsing, STATE_comparing, STATE_detail, STATE_alerting, STATE_error}
TerminalStates == {}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_start *)
t_t_start ==
    /\ state = STATE_idle
    /\ state' = STATE_quizzing

(* Transition: t_answer *)
t_t_answer ==
    /\ state = STATE_quizzing
    /\ state' = STATE_quizzing

(* Transition: t_quiz_done *)
t_t_quiz_done ==
    /\ state = STATE_quizzing
    /\ state' = STATE_fetching

(* Transition: t_skip_quiz *)
t_t_skip_quiz ==
    /\ state = STATE_quizzing
    /\ state' = STATE_fetching

(* Transition: t_fetch_more *)
t_t_fetch_more ==
    /\ state = STATE_fetching
    /\ state' = STATE_fetching

(* Transition: t_fetch_done *)
t_t_fetch_done ==
    /\ state = STATE_fetching
    /\ state' = STATE_analyzing

(* Transition: t_fetch_error *)
t_t_fetch_error ==
    /\ state = STATE_fetching
    /\ state' = STATE_error

(* Transition: t_analyze_done *)
t_t_analyze_done ==
    /\ state = STATE_analyzing
    /\ state' = STATE_ranking

(* Transition: t_analyze_error *)
t_t_analyze_error ==
    /\ state = STATE_analyzing
    /\ state' = STATE_error

(* Transition: t_rank_done *)
t_t_rank_done ==
    /\ state = STATE_ranking
    /\ state' = STATE_browsing

(* Transition: t_rank_error *)
t_t_rank_error ==
    /\ state = STATE_ranking
    /\ state' = STATE_error

(* Transition: t_view_detail *)
t_t_view_detail ==
    /\ state = STATE_browsing
    /\ state' = STATE_detail

(* Transition: t_start_compare *)
t_t_start_compare ==
    /\ state = STATE_browsing
    /\ state' = STATE_comparing

(* Transition: t_back_from_detail *)
t_t_back_from_detail ==
    /\ state = STATE_detail
    /\ state' = STATE_browsing

(* Transition: t_back_from_compare *)
t_t_back_from_compare ==
    /\ state = STATE_comparing
    /\ state' = STATE_browsing

(* Transition: t_detail_to_compare *)
t_t_detail_to_compare ==
    /\ state = STATE_detail
    /\ state' = STATE_comparing

(* Transition: t_set_alert_from_detail *)
t_t_set_alert_from_detail ==
    /\ state = STATE_detail
    /\ state' = STATE_alerting

(* Transition: t_set_alert_from_browse *)
t_t_set_alert_from_browse ==
    /\ state = STATE_browsing
    /\ state' = STATE_alerting

(* Transition: t_confirm_alert *)
t_t_confirm_alert ==
    /\ state = STATE_alerting
    /\ state' = STATE_detail

(* Transition: t_cancel_alert *)
t_t_cancel_alert ==
    /\ state = STATE_alerting
    /\ state' = STATE_detail

(* Transition: t_new_search *)
t_t_new_search ==
    /\ state = STATE_browsing
    /\ state' = STATE_idle

(* Transition: t_refine *)
t_t_refine ==
    /\ state = STATE_browsing
    /\ state' = STATE_quizzing

(* Transition: t_recover *)
t_t_recover ==
    /\ state = STATE_error
    /\ state' = STATE_idle

(* Transition: t_global_reset *)
t_t_global_reset ==
    /\ TRUE  \* Global transition
    /\ state' = STATE_idle

Next ==
    \/ t_t_start
    \/ t_t_answer
    \/ t_t_quiz_done
    \/ t_t_skip_quiz
    \/ t_t_fetch_more
    \/ t_t_fetch_done
    \/ t_t_fetch_error
    \/ t_t_analyze_done
    \/ t_t_analyze_error
    \/ t_t_rank_done
    \/ t_t_rank_error
    \/ t_t_view_detail
    \/ t_t_start_compare
    \/ t_t_back_from_detail
    \/ t_t_back_from_compare
    \/ t_t_detail_to_compare
    \/ t_t_set_alert_from_detail
    \/ t_t_set_alert_from_browse
    \/ t_t_confirm_alert
    \/ t_t_cancel_alert
    \/ t_t_new_search
    \/ t_t_refine
    \/ t_t_recover
    \/ t_t_global_reset

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA StartPreservesInv == Inv /\ t_t_start => Inv'
BY ConstantsDistinct DEF Inv, t_t_start, TypeInvariant, States

LEMMA AnswerPreservesInv == Inv /\ t_t_answer => Inv'
BY ConstantsDistinct DEF Inv, t_t_answer, TypeInvariant, States

LEMMA QuizDonePreservesInv == Inv /\ t_t_quiz_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_quiz_done, TypeInvariant, States

LEMMA SkipQuizPreservesInv == Inv /\ t_t_skip_quiz => Inv'
BY ConstantsDistinct DEF Inv, t_t_skip_quiz, TypeInvariant, States

LEMMA FetchMorePreservesInv == Inv /\ t_t_fetch_more => Inv'
BY ConstantsDistinct DEF Inv, t_t_fetch_more, TypeInvariant, States

LEMMA FetchDonePreservesInv == Inv /\ t_t_fetch_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_fetch_done, TypeInvariant, States

LEMMA FetchErrorPreservesInv == Inv /\ t_t_fetch_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_fetch_error, TypeInvariant, States

LEMMA AnalyzeDonePreservesInv == Inv /\ t_t_analyze_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_analyze_done, TypeInvariant, States

LEMMA AnalyzeErrorPreservesInv == Inv /\ t_t_analyze_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_analyze_error, TypeInvariant, States

LEMMA RankDonePreservesInv == Inv /\ t_t_rank_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_rank_done, TypeInvariant, States

LEMMA RankErrorPreservesInv == Inv /\ t_t_rank_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_rank_error, TypeInvariant, States

LEMMA ViewDetailPreservesInv == Inv /\ t_t_view_detail => Inv'
BY ConstantsDistinct DEF Inv, t_t_view_detail, TypeInvariant, States

LEMMA StarcomparePreservesInv == Inv /\ t_t_start_compare => Inv'
BY ConstantsDistinct DEF Inv, t_t_start_compare, TypeInvariant, States

LEMMA BackFromDetailPreservesInv == Inv /\ t_t_back_from_detail => Inv'
BY ConstantsDistinct DEF Inv, t_t_back_from_detail, TypeInvariant, States

LEMMA BackFromComparePreservesInv == Inv /\ t_t_back_from_compare => Inv'
BY ConstantsDistinct DEF Inv, t_t_back_from_compare, TypeInvariant, States

LEMMA DetailToComparePreservesInv == Inv /\ t_t_detail_to_compare => Inv'
BY ConstantsDistinct DEF Inv, t_t_detail_to_compare, TypeInvariant, States

LEMMA SealerfromDetailPreservesInv == Inv /\ t_t_set_alert_from_detail => Inv'
BY ConstantsDistinct DEF Inv, t_t_set_alert_from_detail, TypeInvariant, States

LEMMA SealerfromBrowsePreservesInv == Inv /\ t_t_set_alert_from_browse => Inv'
BY ConstantsDistinct DEF Inv, t_t_set_alert_from_browse, TypeInvariant, States

LEMMA ConfirmAlertPreservesInv == Inv /\ t_t_confirm_alert => Inv'
BY ConstantsDistinct DEF Inv, t_t_confirm_alert, TypeInvariant, States

LEMMA CancelAlertPreservesInv == Inv /\ t_t_cancel_alert => Inv'
BY ConstantsDistinct DEF Inv, t_t_cancel_alert, TypeInvariant, States

LEMMA NewSearchPreservesInv == Inv /\ t_t_new_search => Inv'
BY ConstantsDistinct DEF Inv, t_t_new_search, TypeInvariant, States

LEMMA RefinePreservesInv == Inv /\ t_t_refine => Inv'
BY ConstantsDistinct DEF Inv, t_t_refine, TypeInvariant, States

LEMMA RecoverPreservesInv == Inv /\ t_t_recover => Inv'
BY ConstantsDistinct DEF Inv, t_t_recover, TypeInvariant, States

LEMMA GlobalResetPreservesInv == Inv /\ t_t_global_reset => Inv'
BY ConstantsDistinct DEF Inv, t_t_global_reset, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY StartPreservesInv, AnswerPreservesInv, QuizDonePreservesInv, SkipQuizPreservesInv, FetchMorePreservesInv, FetchDonePreservesInv, FetchErrorPreservesInv, AnalyzeDonePreservesInv, AnalyzeErrorPreservesInv, RankDonePreservesInv, RankErrorPreservesInv, ViewDetailPreservesInv, StarcomparePreservesInv, BackFromDetailPreservesInv, BackFromComparePreservesInv, DetailToComparePreservesInv, SealerfromDetailPreservesInv, SealerfromBrowsePreservesInv, ConfirmAlertPreservesInv, CancelAlertPreservesInv, NewSearchPreservesInv, RefinePreservesInv, RecoverPreservesInv, GlobalResetPreservesInv DEF Next

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