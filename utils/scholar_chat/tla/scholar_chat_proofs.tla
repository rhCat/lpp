--------------------------- MODULE scholar_chat_proofs ---------------------------
(*
 * L++ Blueprint: Scholar Chatbot
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_searching, STATE_reviewing, STATE_analyzing, STATE_chatting, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_searching
    /\ STATE_idle /= STATE_reviewing
    /\ STATE_idle /= STATE_analyzing
    /\ STATE_idle /= STATE_chatting
    /\ STATE_idle /= STATE_error
    /\ STATE_searching /= STATE_reviewing
    /\ STATE_searching /= STATE_analyzing
    /\ STATE_searching /= STATE_chatting
    /\ STATE_searching /= STATE_error
    /\ STATE_reviewing /= STATE_analyzing
    /\ STATE_reviewing /= STATE_chatting
    /\ STATE_reviewing /= STATE_error
    /\ STATE_analyzing /= STATE_chatting
    /\ STATE_analyzing /= STATE_error
    /\ STATE_chatting /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_searching, STATE_reviewing, STATE_analyzing, STATE_chatting, STATE_error}
TerminalStates == {}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_init *)
t_t_init ==
    /\ state = STATE_idle
    /\ state' = STATE_idle

(* Transition: t_search *)
t_t_search ==
    /\ state = STATE_idle
    /\ state' = STATE_searching

(* Transition: t_search_done *)
t_t_search_done ==
    /\ state = STATE_searching
    /\ state' = STATE_reviewing

(* Transition: t_search_error *)
t_t_search_error ==
    /\ state = STATE_searching
    /\ state' = STATE_error

(* Transition: t_new_search *)
t_t_new_search ==
    /\ state = STATE_reviewing
    /\ state' = STATE_searching

(* Transition: t_select *)
t_t_select ==
    /\ state = STATE_reviewing
    /\ state' = STATE_analyzing

(* Transition: t_analyze_done *)
t_t_analyze_done ==
    /\ state = STATE_analyzing
    /\ state' = STATE_chatting

(* Transition: t_analyze_error *)
t_t_analyze_error ==
    /\ state = STATE_analyzing
    /\ state' = STATE_error

(* Transition: t_ask *)
t_t_ask ==
    /\ state = STATE_chatting
    /\ state' = STATE_chatting

(* Transition: t_new_search_chat *)
t_t_new_search_chat ==
    /\ state = STATE_chatting
    /\ state' = STATE_searching

(* Transition: t_reselect *)
t_t_reselect ==
    /\ state = STATE_chatting
    /\ state' = STATE_reviewing

(* Transition: t_reset *)
t_t_reset ==
    /\ state = STATE_reviewing
    /\ state' = STATE_idle

(* Transition: t_retry *)
t_t_retry ==
    /\ state = STATE_error
    /\ state' = STATE_idle

Next ==
    \/ t_t_init
    \/ t_t_search
    \/ t_t_search_done
    \/ t_t_search_error
    \/ t_t_new_search
    \/ t_t_select
    \/ t_t_analyze_done
    \/ t_t_analyze_error
    \/ t_t_ask
    \/ t_t_new_search_chat
    \/ t_t_reselect
    \/ t_t_reset
    \/ t_t_retry

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA InitPreservesInv == Inv /\ t_t_init => Inv'
BY ConstantsDistinct DEF Inv, t_t_init, TypeInvariant, States

LEMMA SearchPreservesInv == Inv /\ t_t_search => Inv'
BY ConstantsDistinct DEF Inv, t_t_search, TypeInvariant, States

LEMMA SearchDonePreservesInv == Inv /\ t_t_search_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_search_done, TypeInvariant, States

LEMMA SearchErrorPreservesInv == Inv /\ t_t_search_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_search_error, TypeInvariant, States

LEMMA NewSearchPreservesInv == Inv /\ t_t_new_search => Inv'
BY ConstantsDistinct DEF Inv, t_t_new_search, TypeInvariant, States

LEMMA SelectPreservesInv == Inv /\ t_t_select => Inv'
BY ConstantsDistinct DEF Inv, t_t_select, TypeInvariant, States

LEMMA AnalyzeDonePreservesInv == Inv /\ t_t_analyze_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_analyze_done, TypeInvariant, States

LEMMA AnalyzeErrorPreservesInv == Inv /\ t_t_analyze_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_analyze_error, TypeInvariant, States

LEMMA AskPreservesInv == Inv /\ t_t_ask => Inv'
BY ConstantsDistinct DEF Inv, t_t_ask, TypeInvariant, States

LEMMA NewSearchChatPreservesInv == Inv /\ t_t_new_search_chat => Inv'
BY ConstantsDistinct DEF Inv, t_t_new_search_chat, TypeInvariant, States

LEMMA ReselectPreservesInv == Inv /\ t_t_reselect => Inv'
BY ConstantsDistinct DEF Inv, t_t_reselect, TypeInvariant, States

LEMMA ResetPreservesInv == Inv /\ t_t_reset => Inv'
BY ConstantsDistinct DEF Inv, t_t_reset, TypeInvariant, States

LEMMA RetryPreservesInv == Inv /\ t_t_retry => Inv'
BY ConstantsDistinct DEF Inv, t_t_retry, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY InitPreservesInv, SearchPreservesInv, SearchDonePreservesInv, SearchErrorPreservesInv, NewSearchPreservesInv, SelectPreservesInv, AnalyzeDonePreservesInv, AnalyzeErrorPreservesInv, AskPreservesInv, NewSearchChatPreservesInv, ReselectPreservesInv, ResetPreservesInv, RetryPreservesInv DEF Next

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