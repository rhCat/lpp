--------------------------- MODULE lpp_visualizer_proofs ---------------------------
(*
 * L++ Blueprint: L++ Blueprint Visualizer
 * Version: 1.1.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_loaded, STATE_viewing, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_loaded
    /\ STATE_idle /= STATE_viewing
    /\ STATE_idle /= STATE_error
    /\ STATE_loaded /= STATE_viewing
    /\ STATE_loaded /= STATE_error
    /\ STATE_viewing /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_loaded, STATE_viewing, STATE_error}
TerminalStates == {}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_load *)
t_t_load ==
    /\ state = STATE_idle
    /\ state' = STATE_loaded

(* Transition: t_load_error *)
t_t_load_error ==
    /\ state = STATE_idle
    /\ state' = STATE_error

(* Transition: t_reload *)
t_t_reload ==
    /\ state = STATE_loaded
    /\ state' = STATE_loaded

(* Transition: t_reload_from_viewing *)
t_t_reload_from_viewing ==
    /\ state = STATE_viewing
    /\ state' = STATE_loaded

(* Transition: t_start_view *)
t_t_start_view ==
    /\ state = STATE_loaded
    /\ state' = STATE_viewing

(* Transition: t_switch_to_graph *)
t_t_switch_to_graph ==
    /\ state = STATE_viewing
    /\ state' = STATE_viewing

(* Transition: t_switch_to_table *)
t_t_switch_to_table ==
    /\ state = STATE_viewing
    /\ state' = STATE_viewing

(* Transition: t_switch_to_mermaid *)
t_t_switch_to_mermaid ==
    /\ state = STATE_viewing
    /\ state' = STATE_viewing

(* Transition: t_select *)
t_t_select ==
    /\ state = STATE_viewing
    /\ state' = STATE_viewing

(* Transition: t_deselect *)
t_t_deselect ==
    /\ state = STATE_viewing
    /\ state' = STATE_viewing

(* Transition: t_zoom_in *)
t_t_zoom_in ==
    /\ state = STATE_viewing
    /\ state' = STATE_viewing

(* Transition: t_zoom_out *)
t_t_zoom_out ==
    /\ state = STATE_viewing
    /\ state' = STATE_viewing

(* Transition: t_toggle_gates *)
t_t_toggle_gates ==
    /\ state = STATE_viewing
    /\ state' = STATE_viewing

(* Transition: t_toggle_actions *)
t_t_toggle_actions ==
    /\ state = STATE_viewing
    /\ state' = STATE_viewing

(* Transition: t_back_to_loaded *)
t_t_back_to_loaded ==
    /\ state = STATE_viewing
    /\ state' = STATE_loaded

(* Transition: t_unload *)
t_t_unload ==
    /\ state = STATE_loaded
    /\ state' = STATE_idle

(* Transition: t_unload_from_viewing *)
t_t_unload_from_viewing ==
    /\ state = STATE_viewing
    /\ state' = STATE_idle

(* Transition: t_export_readme_from_loaded *)
t_t_export_readme_from_loaded ==
    /\ state = STATE_loaded
    /\ state' = STATE_loaded

(* Transition: t_export_readme_from_viewing *)
t_t_export_readme_from_viewing ==
    /\ state = STATE_viewing
    /\ state' = STATE_viewing

(* Transition: t_recover *)
t_t_recover ==
    /\ state = STATE_error
    /\ state' = STATE_idle

(* Transition: t_load_tree *)
t_t_load_tree ==
    /\ state = STATE_idle
    /\ state' = STATE_loaded

(* Transition: t_set_tree *)
t_t_set_tree ==
    /\ state = STATE_loaded
    /\ state' = STATE_loaded

(* Transition: t_view_tree *)
t_t_view_tree ==
    /\ state = STATE_loaded
    /\ state' = STATE_viewing

(* Transition: t_switch_to_tree *)
t_t_switch_to_tree ==
    /\ state = STATE_viewing
    /\ state' = STATE_viewing

(* Transition: t_switch_to_tree_mermaid *)
t_t_switch_to_tree_mermaid ==
    /\ state = STATE_viewing
    /\ state' = STATE_viewing

(* Transition: t_unload_tree *)
t_t_unload_tree ==
    /\ state = STATE_viewing
    /\ state' = STATE_loaded

Next ==
    \/ t_t_load
    \/ t_t_load_error
    \/ t_t_reload
    \/ t_t_reload_from_viewing
    \/ t_t_start_view
    \/ t_t_switch_to_graph
    \/ t_t_switch_to_table
    \/ t_t_switch_to_mermaid
    \/ t_t_select
    \/ t_t_deselect
    \/ t_t_zoom_in
    \/ t_t_zoom_out
    \/ t_t_toggle_gates
    \/ t_t_toggle_actions
    \/ t_t_back_to_loaded
    \/ t_t_unload
    \/ t_t_unload_from_viewing
    \/ t_t_export_readme_from_loaded
    \/ t_t_export_readme_from_viewing
    \/ t_t_recover
    \/ t_t_load_tree
    \/ t_t_set_tree
    \/ t_t_view_tree
    \/ t_t_switch_to_tree
    \/ t_t_switch_to_tree_mermaid
    \/ t_t_unload_tree

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA LoadPreservesInv == Inv /\ t_t_load => Inv'
BY ConstantsDistinct DEF Inv, t_t_load, TypeInvariant, States

LEMMA LoadErrorPreservesInv == Inv /\ t_t_load_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_load_error, TypeInvariant, States

LEMMA ReloadPreservesInv == Inv /\ t_t_reload => Inv'
BY ConstantsDistinct DEF Inv, t_t_reload, TypeInvariant, States

LEMMA ReloadFromViewingPreservesInv == Inv /\ t_t_reload_from_viewing => Inv'
BY ConstantsDistinct DEF Inv, t_t_reload_from_viewing, TypeInvariant, States

LEMMA StarviewPreservesInv == Inv /\ t_t_start_view => Inv'
BY ConstantsDistinct DEF Inv, t_t_start_view, TypeInvariant, States

LEMMA SwitchToGraphPreservesInv == Inv /\ t_t_switch_to_graph => Inv'
BY ConstantsDistinct DEF Inv, t_t_switch_to_graph, TypeInvariant, States

LEMMA SwitchToTablePreservesInv == Inv /\ t_t_switch_to_table => Inv'
BY ConstantsDistinct DEF Inv, t_t_switch_to_table, TypeInvariant, States

LEMMA SwitchToMermaidPreservesInv == Inv /\ t_t_switch_to_mermaid => Inv'
BY ConstantsDistinct DEF Inv, t_t_switch_to_mermaid, TypeInvariant, States

LEMMA SelectPreservesInv == Inv /\ t_t_select => Inv'
BY ConstantsDistinct DEF Inv, t_t_select, TypeInvariant, States

LEMMA DeselectPreservesInv == Inv /\ t_t_deselect => Inv'
BY ConstantsDistinct DEF Inv, t_t_deselect, TypeInvariant, States

LEMMA ZoomInPreservesInv == Inv /\ t_t_zoom_in => Inv'
BY ConstantsDistinct DEF Inv, t_t_zoom_in, TypeInvariant, States

LEMMA ZoomOutPreservesInv == Inv /\ t_t_zoom_out => Inv'
BY ConstantsDistinct DEF Inv, t_t_zoom_out, TypeInvariant, States

LEMMA ToggleGatesPreservesInv == Inv /\ t_t_toggle_gates => Inv'
BY ConstantsDistinct DEF Inv, t_t_toggle_gates, TypeInvariant, States

LEMMA ToggleActionsPreservesInv == Inv /\ t_t_toggle_actions => Inv'
BY ConstantsDistinct DEF Inv, t_t_toggle_actions, TypeInvariant, States

LEMMA BackToLoadedPreservesInv == Inv /\ t_t_back_to_loaded => Inv'
BY ConstantsDistinct DEF Inv, t_t_back_to_loaded, TypeInvariant, States

LEMMA UnloadPreservesInv == Inv /\ t_t_unload => Inv'
BY ConstantsDistinct DEF Inv, t_t_unload, TypeInvariant, States

LEMMA UnloadFromViewingPreservesInv == Inv /\ t_t_unload_from_viewing => Inv'
BY ConstantsDistinct DEF Inv, t_t_unload_from_viewing, TypeInvariant, States

LEMMA ExporreadmeFromLoadedPreservesInv == Inv /\ t_t_export_readme_from_loaded => Inv'
BY ConstantsDistinct DEF Inv, t_t_export_readme_from_loaded, TypeInvariant, States

LEMMA ExporreadmeFromViewingPreservesInv == Inv /\ t_t_export_readme_from_viewing => Inv'
BY ConstantsDistinct DEF Inv, t_t_export_readme_from_viewing, TypeInvariant, States

LEMMA RecoverPreservesInv == Inv /\ t_t_recover => Inv'
BY ConstantsDistinct DEF Inv, t_t_recover, TypeInvariant, States

LEMMA LoadTreePreservesInv == Inv /\ t_t_load_tree => Inv'
BY ConstantsDistinct DEF Inv, t_t_load_tree, TypeInvariant, States

LEMMA SetreePreservesInv == Inv /\ t_t_set_tree => Inv'
BY ConstantsDistinct DEF Inv, t_t_set_tree, TypeInvariant, States

LEMMA ViewTreePreservesInv == Inv /\ t_t_view_tree => Inv'
BY ConstantsDistinct DEF Inv, t_t_view_tree, TypeInvariant, States

LEMMA SwitchToTreePreservesInv == Inv /\ t_t_switch_to_tree => Inv'
BY ConstantsDistinct DEF Inv, t_t_switch_to_tree, TypeInvariant, States

LEMMA SwitchToTreeMermaidPreservesInv == Inv /\ t_t_switch_to_tree_mermaid => Inv'
BY ConstantsDistinct DEF Inv, t_t_switch_to_tree_mermaid, TypeInvariant, States

LEMMA UnloadTreePreservesInv == Inv /\ t_t_unload_tree => Inv'
BY ConstantsDistinct DEF Inv, t_t_unload_tree, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY LoadPreservesInv, LoadErrorPreservesInv, ReloadPreservesInv, ReloadFromViewingPreservesInv, StarviewPreservesInv, SwitchToGraphPreservesInv, SwitchToTablePreservesInv, SwitchToMermaidPreservesInv, SelectPreservesInv, DeselectPreservesInv, ZoomInPreservesInv, ZoomOutPreservesInv, ToggleGatesPreservesInv, ToggleActionsPreservesInv, BackToLoadedPreservesInv, UnloadPreservesInv, UnloadFromViewingPreservesInv, ExporreadmeFromLoadedPreservesInv, ExporreadmeFromViewingPreservesInv, RecoverPreservesInv, LoadTreePreservesInv, SetreePreservesInv, ViewTreePreservesInv, SwitchToTreePreservesInv, SwitchToTreeMermaidPreservesInv, UnloadTreePreservesInv DEF Next

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