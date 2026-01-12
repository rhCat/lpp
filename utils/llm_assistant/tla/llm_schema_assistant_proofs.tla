--------------------------- MODULE llm_schema_assistant_proofs ---------------------------
(*
 * L++ Blueprint: L++ LLM Schema Assistant
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_init, STATE_ready, STATE_querying, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_init /= STATE_ready
    /\ STATE_init /= STATE_querying
    /\ STATE_init /= STATE_error
    /\ STATE_ready /= STATE_querying
    /\ STATE_ready /= STATE_error
    /\ STATE_querying /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_init, STATE_ready, STATE_querying, STATE_error}
TerminalStates == {}

TypeInvariant == state \in States

Init == state = STATE_init

(* Transition: t_init_start *)
t_t_init_start ==
    /\ state = STATE_init
    /\ state' = STATE_ready

(* Transition: t_init_no_key *)
t_t_init_no_key ==
    /\ state = STATE_init
    /\ state' = STATE_error

(* Transition: t_configure *)
t_t_configure ==
    /\ TRUE  \* Global transition
    /\ state' = STATE_init

(* Transition: t_set_key *)
t_t_set_key ==
    /\ state = STATE_error
    /\ state' = STATE_init

(* Transition: t_load_blueprint *)
t_t_load_blueprint ==
    /\ state = STATE_ready
    /\ state' = STATE_ready

(* Transition: t_query *)
t_t_query ==
    /\ state = STATE_ready
    /\ state' = STATE_querying

(* Transition: t_explain *)
t_t_explain ==
    /\ state = STATE_ready
    /\ state' = STATE_querying

(* Transition: t_validate *)
t_t_validate ==
    /\ state = STATE_ready
    /\ state' = STATE_querying

(* Transition: t_suggest *)
t_t_suggest ==
    /\ state = STATE_ready
    /\ state' = STATE_querying

(* Transition: t_query_done *)
t_t_query_done ==
    /\ state = STATE_querying
    /\ state' = STATE_ready

(* Transition: t_query_error *)
t_t_query_error ==
    /\ state = STATE_querying
    /\ state' = STATE_error

(* Transition: t_clear *)
t_t_clear ==
    /\ state = STATE_ready
    /\ state' = STATE_ready

(* Transition: t_recover *)
t_t_recover ==
    /\ state = STATE_error
    /\ state' = STATE_ready

Next ==
    \/ t_t_init_start
    \/ t_t_init_no_key
    \/ t_t_configure
    \/ t_t_set_key
    \/ t_t_load_blueprint
    \/ t_t_query
    \/ t_t_explain
    \/ t_t_validate
    \/ t_t_suggest
    \/ t_t_query_done
    \/ t_t_query_error
    \/ t_t_clear
    \/ t_t_recover

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA InistartPreservesInv == Inv /\ t_t_init_start => Inv'
BY ConstantsDistinct DEF Inv, t_t_init_start, TypeInvariant, States

LEMMA IninoKeyPreservesInv == Inv /\ t_t_init_no_key => Inv'
BY ConstantsDistinct DEF Inv, t_t_init_no_key, TypeInvariant, States

LEMMA ConfigurePreservesInv == Inv /\ t_t_configure => Inv'
BY ConstantsDistinct DEF Inv, t_t_configure, TypeInvariant, States

LEMMA SekeyPreservesInv == Inv /\ t_t_set_key => Inv'
BY ConstantsDistinct DEF Inv, t_t_set_key, TypeInvariant, States

LEMMA LoadBlueprintPreservesInv == Inv /\ t_t_load_blueprint => Inv'
BY ConstantsDistinct DEF Inv, t_t_load_blueprint, TypeInvariant, States

LEMMA QueryPreservesInv == Inv /\ t_t_query => Inv'
BY ConstantsDistinct DEF Inv, t_t_query, TypeInvariant, States

LEMMA ExplainPreservesInv == Inv /\ t_t_explain => Inv'
BY ConstantsDistinct DEF Inv, t_t_explain, TypeInvariant, States

LEMMA ValidatePreservesInv == Inv /\ t_t_validate => Inv'
BY ConstantsDistinct DEF Inv, t_t_validate, TypeInvariant, States

LEMMA SuggestPreservesInv == Inv /\ t_t_suggest => Inv'
BY ConstantsDistinct DEF Inv, t_t_suggest, TypeInvariant, States

LEMMA QueryDonePreservesInv == Inv /\ t_t_query_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_query_done, TypeInvariant, States

LEMMA QueryErrorPreservesInv == Inv /\ t_t_query_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_query_error, TypeInvariant, States

LEMMA ClearPreservesInv == Inv /\ t_t_clear => Inv'
BY ConstantsDistinct DEF Inv, t_t_clear, TypeInvariant, States

LEMMA RecoverPreservesInv == Inv /\ t_t_recover => Inv'
BY ConstantsDistinct DEF Inv, t_t_recover, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY InistartPreservesInv, IninoKeyPreservesInv, ConfigurePreservesInv, SekeyPreservesInv, LoadBlueprintPreservesInv, QueryPreservesInv, ExplainPreservesInv, ValidatePreservesInv, SuggestPreservesInv, QueryDonePreservesInv, QueryErrorPreservesInv, ClearPreservesInv, RecoverPreservesInv DEF Next

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