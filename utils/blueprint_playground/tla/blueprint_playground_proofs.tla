--------------------------- MODULE blueprint_playground_proofs ---------------------------
(*
 * L++ Blueprint: L++ Blueprint Playground
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_editing, STATE_simulating, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_editing
    /\ STATE_idle /= STATE_simulating
    /\ STATE_idle /= STATE_error
    /\ STATE_editing /= STATE_simulating
    /\ STATE_editing /= STATE_error
    /\ STATE_simulating /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_editing, STATE_simulating, STATE_error}
TerminalStates == {}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_load_from_idle *)
t_t_load_from_idle ==
    /\ state = STATE_idle
    /\ state' = STATE_editing

(* Transition: t_load_from_url *)
t_t_load_from_url ==
    /\ state = STATE_idle
    /\ state' = STATE_editing

(* Transition: t_reload *)
t_t_reload ==
    /\ state = STATE_editing
    /\ state' = STATE_editing

(* Transition: t_update *)
t_t_update ==
    /\ state = STATE_editing
    /\ state' = STATE_editing

(* Transition: t_validate *)
t_t_validate ==
    /\ state = STATE_editing
    /\ state' = STATE_editing

(* Transition: t_format *)
t_t_format ==
    /\ state = STATE_editing
    /\ state' = STATE_editing

(* Transition: t_regenerate_diagram *)
t_t_regenerate_diagram ==
    /\ state = STATE_editing
    /\ state' = STATE_editing

(* Transition: t_start_simulation *)
t_t_start_simulation ==
    /\ state = STATE_editing
    /\ state' = STATE_simulating

(* Transition: t_dispatch_event *)
t_t_dispatch_event ==
    /\ state = STATE_simulating
    /\ state' = STATE_simulating

(* Transition: t_reset_simulation *)
t_t_reset_simulation ==
    /\ state = STATE_simulating
    /\ state' = STATE_simulating

(* Transition: t_stop_simulation *)
t_t_stop_simulation ==
    /\ state = STATE_simulating
    /\ state' = STATE_editing

(* Transition: t_share *)
t_t_share ==
    /\ state = STATE_editing
    /\ state' = STATE_editing

(* Transition: t_share_from_sim *)
t_t_share_from_sim ==
    /\ state = STATE_simulating
    /\ state' = STATE_simulating

(* Transition: t_export *)
t_t_export ==
    /\ state = STATE_editing
    /\ state' = STATE_editing

(* Transition: t_export_from_sim *)
t_t_export_from_sim ==
    /\ state = STATE_simulating
    /\ state' = STATE_simulating

(* Transition: t_unload *)
t_t_unload ==
    /\ state = STATE_editing
    /\ state' = STATE_idle

(* Transition: t_unload_from_sim *)
t_t_unload_from_sim ==
    /\ state = STATE_simulating
    /\ state' = STATE_idle

(* Transition: t_error_from_editing *)
t_t_error_from_editing ==
    /\ state = STATE_editing
    /\ state' = STATE_error

(* Transition: t_error_from_simulating *)
t_t_error_from_simulating ==
    /\ state = STATE_simulating
    /\ state' = STATE_error

(* Transition: t_recover *)
t_t_recover ==
    /\ state = STATE_error
    /\ state' = STATE_idle

(* Transition: t_recover_to_editing *)
t_t_recover_to_editing ==
    /\ state = STATE_error
    /\ state' = STATE_editing

Next ==
    \/ t_t_load_from_idle
    \/ t_t_load_from_url
    \/ t_t_reload
    \/ t_t_update
    \/ t_t_validate
    \/ t_t_format
    \/ t_t_regenerate_diagram
    \/ t_t_start_simulation
    \/ t_t_dispatch_event
    \/ t_t_reset_simulation
    \/ t_t_stop_simulation
    \/ t_t_share
    \/ t_t_share_from_sim
    \/ t_t_export
    \/ t_t_export_from_sim
    \/ t_t_unload
    \/ t_t_unload_from_sim
    \/ t_t_error_from_editing
    \/ t_t_error_from_simulating
    \/ t_t_recover
    \/ t_t_recover_to_editing

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA LoadFromIdlePreservesInv == Inv /\ t_t_load_from_idle => Inv'
BY ConstantsDistinct DEF Inv, t_t_load_from_idle, TypeInvariant, States

LEMMA LoadFromUrlPreservesInv == Inv /\ t_t_load_from_url => Inv'
BY ConstantsDistinct DEF Inv, t_t_load_from_url, TypeInvariant, States

LEMMA ReloadPreservesInv == Inv /\ t_t_reload => Inv'
BY ConstantsDistinct DEF Inv, t_t_reload, TypeInvariant, States

LEMMA UpdatePreservesInv == Inv /\ t_t_update => Inv'
BY ConstantsDistinct DEF Inv, t_t_update, TypeInvariant, States

LEMMA ValidatePreservesInv == Inv /\ t_t_validate => Inv'
BY ConstantsDistinct DEF Inv, t_t_validate, TypeInvariant, States

LEMMA FormatPreservesInv == Inv /\ t_t_format => Inv'
BY ConstantsDistinct DEF Inv, t_t_format, TypeInvariant, States

LEMMA RegenerateDiagramPreservesInv == Inv /\ t_t_regenerate_diagram => Inv'
BY ConstantsDistinct DEF Inv, t_t_regenerate_diagram, TypeInvariant, States

LEMMA StarsimulationPreservesInv == Inv /\ t_t_start_simulation => Inv'
BY ConstantsDistinct DEF Inv, t_t_start_simulation, TypeInvariant, States

LEMMA DispatchEventPreservesInv == Inv /\ t_t_dispatch_event => Inv'
BY ConstantsDistinct DEF Inv, t_t_dispatch_event, TypeInvariant, States

LEMMA ResesimulationPreservesInv == Inv /\ t_t_reset_simulation => Inv'
BY ConstantsDistinct DEF Inv, t_t_reset_simulation, TypeInvariant, States

LEMMA StopSimulationPreservesInv == Inv /\ t_t_stop_simulation => Inv'
BY ConstantsDistinct DEF Inv, t_t_stop_simulation, TypeInvariant, States

LEMMA SharePreservesInv == Inv /\ t_t_share => Inv'
BY ConstantsDistinct DEF Inv, t_t_share, TypeInvariant, States

LEMMA ShareFromSimPreservesInv == Inv /\ t_t_share_from_sim => Inv'
BY ConstantsDistinct DEF Inv, t_t_share_from_sim, TypeInvariant, States

LEMMA ExportPreservesInv == Inv /\ t_t_export => Inv'
BY ConstantsDistinct DEF Inv, t_t_export, TypeInvariant, States

LEMMA ExporfromSimPreservesInv == Inv /\ t_t_export_from_sim => Inv'
BY ConstantsDistinct DEF Inv, t_t_export_from_sim, TypeInvariant, States

LEMMA UnloadPreservesInv == Inv /\ t_t_unload => Inv'
BY ConstantsDistinct DEF Inv, t_t_unload, TypeInvariant, States

LEMMA UnloadFromSimPreservesInv == Inv /\ t_t_unload_from_sim => Inv'
BY ConstantsDistinct DEF Inv, t_t_unload_from_sim, TypeInvariant, States

LEMMA ErrorFromEditingPreservesInv == Inv /\ t_t_error_from_editing => Inv'
BY ConstantsDistinct DEF Inv, t_t_error_from_editing, TypeInvariant, States

LEMMA ErrorFromSimulatingPreservesInv == Inv /\ t_t_error_from_simulating => Inv'
BY ConstantsDistinct DEF Inv, t_t_error_from_simulating, TypeInvariant, States

LEMMA RecoverPreservesInv == Inv /\ t_t_recover => Inv'
BY ConstantsDistinct DEF Inv, t_t_recover, TypeInvariant, States

LEMMA RecoverToEditingPreservesInv == Inv /\ t_t_recover_to_editing => Inv'
BY ConstantsDistinct DEF Inv, t_t_recover_to_editing, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY LoadFromIdlePreservesInv, LoadFromUrlPreservesInv, ReloadPreservesInv, UpdatePreservesInv, ValidatePreservesInv, FormatPreservesInv, RegenerateDiagramPreservesInv, StarsimulationPreservesInv, DispatchEventPreservesInv, ResesimulationPreservesInv, StopSimulationPreservesInv, SharePreservesInv, ShareFromSimPreservesInv, ExportPreservesInv, ExporfromSimPreservesInv, UnloadPreservesInv, UnloadFromSimPreservesInv, ErrorFromEditingPreservesInv, ErrorFromSimulatingPreservesInv, RecoverPreservesInv, RecoverToEditingPreservesInv DEF Next

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