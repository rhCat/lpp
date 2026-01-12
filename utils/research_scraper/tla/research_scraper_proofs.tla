--------------------------- MODULE research_scraper_proofs ---------------------------
(*
 * L++ Blueprint: Research Scraper
 * Version: 1.0.1
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_hasResults, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_hasResults
    /\ STATE_idle /= STATE_error
    /\ STATE_hasResults /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_hasResults, STATE_error}
TerminalStates == {}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_search_arxiv *)
t_t_search_arxiv ==
    /\ state = STATE_idle
    /\ state' = STATE_hasResults

(* Transition: t_search_scholar *)
t_t_search_scholar ==
    /\ state = STATE_idle
    /\ state' = STATE_hasResults

(* Transition: t_search_web *)
t_t_search_web ==
    /\ state = STATE_idle
    /\ state' = STATE_hasResults

(* Transition: t_select *)
t_t_select ==
    /\ state = STATE_hasResults
    /\ state' = STATE_hasResults

(* Transition: t_search_new_arxiv *)
t_t_search_new_arxiv ==
    /\ state = STATE_hasResults
    /\ state' = STATE_hasResults

(* Transition: t_search_new_scholar *)
t_t_search_new_scholar ==
    /\ state = STATE_hasResults
    /\ state' = STATE_hasResults

(* Transition: t_search_new_web *)
t_t_search_new_web ==
    /\ state = STATE_hasResults
    /\ state' = STATE_hasResults

(* Transition: t_clear *)
t_t_clear ==
    /\ state = STATE_hasResults
    /\ state' = STATE_idle

(* Transition: t_retry *)
t_t_retry ==
    /\ state = STATE_error
    /\ state' = STATE_idle

(* Transition: t_error_from_idle *)
t_t_error_from_idle ==
    /\ state = STATE_idle
    /\ state' = STATE_error

(* Transition: t_error_from_results *)
t_t_error_from_results ==
    /\ state = STATE_hasResults
    /\ state' = STATE_error

Next ==
    \/ t_t_search_arxiv
    \/ t_t_search_scholar
    \/ t_t_search_web
    \/ t_t_select
    \/ t_t_search_new_arxiv
    \/ t_t_search_new_scholar
    \/ t_t_search_new_web
    \/ t_t_clear
    \/ t_t_retry
    \/ t_t_error_from_idle
    \/ t_t_error_from_results

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA SearchArxivPreservesInv == Inv /\ t_t_search_arxiv => Inv'
BY ConstantsDistinct DEF Inv, t_t_search_arxiv, TypeInvariant, States

LEMMA SearchScholarPreservesInv == Inv /\ t_t_search_scholar => Inv'
BY ConstantsDistinct DEF Inv, t_t_search_scholar, TypeInvariant, States

LEMMA SearchWebPreservesInv == Inv /\ t_t_search_web => Inv'
BY ConstantsDistinct DEF Inv, t_t_search_web, TypeInvariant, States

LEMMA SelectPreservesInv == Inv /\ t_t_select => Inv'
BY ConstantsDistinct DEF Inv, t_t_select, TypeInvariant, States

LEMMA SearchNewArxivPreservesInv == Inv /\ t_t_search_new_arxiv => Inv'
BY ConstantsDistinct DEF Inv, t_t_search_new_arxiv, TypeInvariant, States

LEMMA SearchNewScholarPreservesInv == Inv /\ t_t_search_new_scholar => Inv'
BY ConstantsDistinct DEF Inv, t_t_search_new_scholar, TypeInvariant, States

LEMMA SearchNewWebPreservesInv == Inv /\ t_t_search_new_web => Inv'
BY ConstantsDistinct DEF Inv, t_t_search_new_web, TypeInvariant, States

LEMMA ClearPreservesInv == Inv /\ t_t_clear => Inv'
BY ConstantsDistinct DEF Inv, t_t_clear, TypeInvariant, States

LEMMA RetryPreservesInv == Inv /\ t_t_retry => Inv'
BY ConstantsDistinct DEF Inv, t_t_retry, TypeInvariant, States

LEMMA ErrorFromIdlePreservesInv == Inv /\ t_t_error_from_idle => Inv'
BY ConstantsDistinct DEF Inv, t_t_error_from_idle, TypeInvariant, States

LEMMA ErrorFromResultsPreservesInv == Inv /\ t_t_error_from_results => Inv'
BY ConstantsDistinct DEF Inv, t_t_error_from_results, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY SearchArxivPreservesInv, SearchScholarPreservesInv, SearchWebPreservesInv, SelectPreservesInv, SearchNewArxivPreservesInv, SearchNewScholarPreservesInv, SearchNewWebPreservesInv, ClearPreservesInv, RetryPreservesInv, ErrorFromIdlePreservesInv, ErrorFromResultsPreservesInv DEF Next

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