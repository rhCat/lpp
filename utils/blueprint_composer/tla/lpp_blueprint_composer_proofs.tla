--------------------------- MODULE lpp_blueprint_composer_proofs ---------------------------
(*
 * L++ Blueprint: L++ Blueprint Composer
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_parent_loaded, STATE_child_loaded, STATE_defining_embedding, STATE_embedding_ready, STATE_composed, STATE_validated, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_parent_loaded
    /\ STATE_idle /= STATE_child_loaded
    /\ STATE_idle /= STATE_defining_embedding
    /\ STATE_idle /= STATE_embedding_ready
    /\ STATE_idle /= STATE_composed
    /\ STATE_idle /= STATE_validated
    /\ STATE_idle /= STATE_error
    /\ STATE_parent_loaded /= STATE_child_loaded
    /\ STATE_parent_loaded /= STATE_defining_embedding
    /\ STATE_parent_loaded /= STATE_embedding_ready
    /\ STATE_parent_loaded /= STATE_composed
    /\ STATE_parent_loaded /= STATE_validated
    /\ STATE_parent_loaded /= STATE_error
    /\ STATE_child_loaded /= STATE_defining_embedding
    /\ STATE_child_loaded /= STATE_embedding_ready
    /\ STATE_child_loaded /= STATE_composed
    /\ STATE_child_loaded /= STATE_validated
    /\ STATE_child_loaded /= STATE_error
    /\ STATE_defining_embedding /= STATE_embedding_ready
    /\ STATE_defining_embedding /= STATE_composed
    /\ STATE_defining_embedding /= STATE_validated
    /\ STATE_defining_embedding /= STATE_error
    /\ STATE_embedding_ready /= STATE_composed
    /\ STATE_embedding_ready /= STATE_validated
    /\ STATE_embedding_ready /= STATE_error
    /\ STATE_composed /= STATE_validated
    /\ STATE_composed /= STATE_error
    /\ STATE_validated /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_parent_loaded, STATE_child_loaded, STATE_defining_embedding, STATE_embedding_ready, STATE_composed, STATE_validated, STATE_error}
TerminalStates == {}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_load_parent_from_idle *)
t_t_load_parent_from_idle ==
    /\ state = STATE_idle
    /\ state' = STATE_parent_loaded

(* Transition: t_load_manifest *)
t_t_load_manifest ==
    /\ state = STATE_idle
    /\ state' = STATE_composed

(* Transition: t_load_child *)
t_t_load_child ==
    /\ state = STATE_parent_loaded
    /\ state' = STATE_child_loaded

(* Transition: t_reload_parent *)
t_t_reload_parent ==
    /\ state = STATE_parent_loaded
    /\ state' = STATE_parent_loaded

(* Transition: t_reload_child *)
t_t_reload_child ==
    /\ state = STATE_child_loaded
    /\ state' = STATE_child_loaded

(* Transition: t_define_embedding *)
t_t_define_embedding ==
    /\ state = STATE_child_loaded
    /\ state' = STATE_defining_embedding

(* Transition: t_set_input *)
t_t_set_input ==
    /\ state = STATE_defining_embedding
    /\ state' = STATE_defining_embedding

(* Transition: t_set_output *)
t_t_set_output ==
    /\ state = STATE_defining_embedding
    /\ state' = STATE_defining_embedding

(* Transition: t_set_events *)
t_t_set_events ==
    /\ state = STATE_defining_embedding
    /\ state' = STATE_defining_embedding

(* Transition: t_done_defining *)
t_t_done_defining ==
    /\ state = STATE_defining_embedding
    /\ state' = STATE_embedding_ready

(* Transition: t_add_more *)
t_t_add_more ==
    /\ state = STATE_embedding_ready
    /\ state' = STATE_child_loaded

(* Transition: t_compose *)
t_t_compose ==
    /\ state = STATE_embedding_ready
    /\ state' = STATE_composed

(* Transition: t_quick_compose *)
t_t_quick_compose ==
    /\ state = STATE_child_loaded
    /\ state' = STATE_composed

(* Transition: t_validate *)
t_t_validate ==
    /\ state = STATE_composed
    /\ state' = STATE_validated

(* Transition: t_flatten *)
t_t_flatten ==
    /\ state = STATE_composed
    /\ state' = STATE_composed

(* Transition: t_export *)
t_t_export ==
    /\ state = STATE_composed
    /\ state' = STATE_composed

(* Transition: t_export_after_validate *)
t_t_export_after_validate ==
    /\ state = STATE_validated
    /\ state' = STATE_validated

(* Transition: t_save_manifest *)
t_t_save_manifest ==
    /\ state = STATE_embedding_ready
    /\ state' = STATE_embedding_ready

(* Transition: t_revalidate *)
t_t_revalidate ==
    /\ state = STATE_validated
    /\ state' = STATE_validated

(* Transition: t_back_to_composed *)
t_t_back_to_composed ==
    /\ state = STATE_validated
    /\ state' = STATE_composed

(* Transition: t_back_to_embedding *)
t_t_back_to_embedding ==
    /\ state = STATE_composed
    /\ state' = STATE_embedding_ready

(* Transition: t_back_from_defining *)
t_t_back_from_defining ==
    /\ state = STATE_defining_embedding
    /\ state' = STATE_child_loaded

(* Transition: t_reset *)
t_t_reset ==
    /\ state = STATE_composed
    /\ state' = STATE_idle

(* Transition: t_reset_from_validated *)
t_t_reset_from_validated ==
    /\ state = STATE_validated
    /\ state' = STATE_idle

(* Transition: t_clear_from_parent *)
t_t_clear_from_parent ==
    /\ state = STATE_parent_loaded
    /\ state' = STATE_idle

(* Transition: t_clear_from_child *)
t_t_clear_from_child ==
    /\ state = STATE_child_loaded
    /\ state' = STATE_idle

(* Transition: t_error_recover *)
t_t_error_recover ==
    /\ state = STATE_error
    /\ state' = STATE_idle

(* Transition: t_load_error *)
t_t_load_error ==
    /\ TRUE  \* Global transition
    /\ state' = STATE_error

Next ==
    \/ t_t_load_parent_from_idle
    \/ t_t_load_manifest
    \/ t_t_load_child
    \/ t_t_reload_parent
    \/ t_t_reload_child
    \/ t_t_define_embedding
    \/ t_t_set_input
    \/ t_t_set_output
    \/ t_t_set_events
    \/ t_t_done_defining
    \/ t_t_add_more
    \/ t_t_compose
    \/ t_t_quick_compose
    \/ t_t_validate
    \/ t_t_flatten
    \/ t_t_export
    \/ t_t_export_after_validate
    \/ t_t_save_manifest
    \/ t_t_revalidate
    \/ t_t_back_to_composed
    \/ t_t_back_to_embedding
    \/ t_t_back_from_defining
    \/ t_t_reset
    \/ t_t_reset_from_validated
    \/ t_t_clear_from_parent
    \/ t_t_clear_from_child
    \/ t_t_error_recover
    \/ t_t_load_error

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA LoadParenfromIdlePreservesInv == Inv /\ t_t_load_parent_from_idle => Inv'
BY ConstantsDistinct DEF Inv, t_t_load_parent_from_idle, TypeInvariant, States

LEMMA LoadManifestPreservesInv == Inv /\ t_t_load_manifest => Inv'
BY ConstantsDistinct DEF Inv, t_t_load_manifest, TypeInvariant, States

LEMMA LoadChildPreservesInv == Inv /\ t_t_load_child => Inv'
BY ConstantsDistinct DEF Inv, t_t_load_child, TypeInvariant, States

LEMMA ReloadParentPreservesInv == Inv /\ t_t_reload_parent => Inv'
BY ConstantsDistinct DEF Inv, t_t_reload_parent, TypeInvariant, States

LEMMA ReloadChildPreservesInv == Inv /\ t_t_reload_child => Inv'
BY ConstantsDistinct DEF Inv, t_t_reload_child, TypeInvariant, States

LEMMA DefineEmbeddingPreservesInv == Inv /\ t_t_define_embedding => Inv'
BY ConstantsDistinct DEF Inv, t_t_define_embedding, TypeInvariant, States

LEMMA SeinputPreservesInv == Inv /\ t_t_set_input => Inv'
BY ConstantsDistinct DEF Inv, t_t_set_input, TypeInvariant, States

LEMMA SeoutputPreservesInv == Inv /\ t_t_set_output => Inv'
BY ConstantsDistinct DEF Inv, t_t_set_output, TypeInvariant, States

LEMMA SeeventsPreservesInv == Inv /\ t_t_set_events => Inv'
BY ConstantsDistinct DEF Inv, t_t_set_events, TypeInvariant, States

LEMMA DoneDefiningPreservesInv == Inv /\ t_t_done_defining => Inv'
BY ConstantsDistinct DEF Inv, t_t_done_defining, TypeInvariant, States

LEMMA AddMorePreservesInv == Inv /\ t_t_add_more => Inv'
BY ConstantsDistinct DEF Inv, t_t_add_more, TypeInvariant, States

LEMMA ComposePreservesInv == Inv /\ t_t_compose => Inv'
BY ConstantsDistinct DEF Inv, t_t_compose, TypeInvariant, States

LEMMA QuickComposePreservesInv == Inv /\ t_t_quick_compose => Inv'
BY ConstantsDistinct DEF Inv, t_t_quick_compose, TypeInvariant, States

LEMMA ValidatePreservesInv == Inv /\ t_t_validate => Inv'
BY ConstantsDistinct DEF Inv, t_t_validate, TypeInvariant, States

LEMMA FlattenPreservesInv == Inv /\ t_t_flatten => Inv'
BY ConstantsDistinct DEF Inv, t_t_flatten, TypeInvariant, States

LEMMA ExportPreservesInv == Inv /\ t_t_export => Inv'
BY ConstantsDistinct DEF Inv, t_t_export, TypeInvariant, States

LEMMA ExporafterValidatePreservesInv == Inv /\ t_t_export_after_validate => Inv'
BY ConstantsDistinct DEF Inv, t_t_export_after_validate, TypeInvariant, States

LEMMA SaveManifestPreservesInv == Inv /\ t_t_save_manifest => Inv'
BY ConstantsDistinct DEF Inv, t_t_save_manifest, TypeInvariant, States

LEMMA RevalidatePreservesInv == Inv /\ t_t_revalidate => Inv'
BY ConstantsDistinct DEF Inv, t_t_revalidate, TypeInvariant, States

LEMMA BackToComposedPreservesInv == Inv /\ t_t_back_to_composed => Inv'
BY ConstantsDistinct DEF Inv, t_t_back_to_composed, TypeInvariant, States

LEMMA BackToEmbeddingPreservesInv == Inv /\ t_t_back_to_embedding => Inv'
BY ConstantsDistinct DEF Inv, t_t_back_to_embedding, TypeInvariant, States

LEMMA BackFromDefiningPreservesInv == Inv /\ t_t_back_from_defining => Inv'
BY ConstantsDistinct DEF Inv, t_t_back_from_defining, TypeInvariant, States

LEMMA ResetPreservesInv == Inv /\ t_t_reset => Inv'
BY ConstantsDistinct DEF Inv, t_t_reset, TypeInvariant, States

LEMMA ResefromValidatedPreservesInv == Inv /\ t_t_reset_from_validated => Inv'
BY ConstantsDistinct DEF Inv, t_t_reset_from_validated, TypeInvariant, States

LEMMA ClearFromParentPreservesInv == Inv /\ t_t_clear_from_parent => Inv'
BY ConstantsDistinct DEF Inv, t_t_clear_from_parent, TypeInvariant, States

LEMMA ClearFromChildPreservesInv == Inv /\ t_t_clear_from_child => Inv'
BY ConstantsDistinct DEF Inv, t_t_clear_from_child, TypeInvariant, States

LEMMA ErrorRecoverPreservesInv == Inv /\ t_t_error_recover => Inv'
BY ConstantsDistinct DEF Inv, t_t_error_recover, TypeInvariant, States

LEMMA LoadErrorPreservesInv == Inv /\ t_t_load_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_load_error, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY LoadParenfromIdlePreservesInv, LoadManifestPreservesInv, LoadChildPreservesInv, ReloadParentPreservesInv, ReloadChildPreservesInv, DefineEmbeddingPreservesInv, SeinputPreservesInv, SeoutputPreservesInv, SeeventsPreservesInv, DoneDefiningPreservesInv, AddMorePreservesInv, ComposePreservesInv, QuickComposePreservesInv, ValidatePreservesInv, FlattenPreservesInv, ExportPreservesInv, ExporafterValidatePreservesInv, SaveManifestPreservesInv, RevalidatePreservesInv, BackToComposedPreservesInv, BackToEmbeddingPreservesInv, BackFromDefiningPreservesInv, ResetPreservesInv, ResefromValidatedPreservesInv, ClearFromParentPreservesInv, ClearFromChildPreservesInv, ErrorRecoverPreservesInv, LoadErrorPreservesInv DEF Next

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