--------------------------- MODULE lpp_blueprint_registry_proofs ---------------------------
(*
 * L++ Blueprint: L++ Blueprint Registry
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_ready, STATE_viewing, STATE_searching, STATE_comparing, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_ready
    /\ STATE_idle /= STATE_viewing
    /\ STATE_idle /= STATE_searching
    /\ STATE_idle /= STATE_comparing
    /\ STATE_idle /= STATE_error
    /\ STATE_ready /= STATE_viewing
    /\ STATE_ready /= STATE_searching
    /\ STATE_ready /= STATE_comparing
    /\ STATE_ready /= STATE_error
    /\ STATE_viewing /= STATE_searching
    /\ STATE_viewing /= STATE_comparing
    /\ STATE_viewing /= STATE_error
    /\ STATE_searching /= STATE_comparing
    /\ STATE_searching /= STATE_error
    /\ STATE_comparing /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_ready, STATE_viewing, STATE_searching, STATE_comparing, STATE_error}
TerminalStates == {}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_init_registry *)
t_t_init_registry ==
    /\ state = STATE_idle
    /\ state' = STATE_ready

(* Transition: t_load_registry *)
t_t_load_registry ==
    /\ state = STATE_idle
    /\ state' = STATE_ready

(* Transition: t_reload_registry *)
t_t_reload_registry ==
    /\ state = STATE_ready
    /\ state' = STATE_ready

(* Transition: t_register *)
t_t_register ==
    /\ state = STATE_ready
    /\ state' = STATE_ready

(* Transition: t_update *)
t_t_update ==
    /\ state = STATE_ready
    /\ state' = STATE_ready

(* Transition: t_update_from_viewing *)
t_t_update_from_viewing ==
    /\ state = STATE_viewing
    /\ state' = STATE_viewing

(* Transition: t_get *)
t_t_get ==
    /\ state = STATE_ready
    /\ state' = STATE_viewing

(* Transition: t_get_another *)
t_t_get_another ==
    /\ state = STATE_viewing
    /\ state' = STATE_viewing

(* Transition: t_list *)
t_t_list ==
    /\ state = STATE_ready
    /\ state' = STATE_searching

(* Transition: t_search *)
t_t_search ==
    /\ state = STATE_ready
    /\ state' = STATE_searching

(* Transition: t_search_again *)
t_t_search_again ==
    /\ state = STATE_searching
    /\ state' = STATE_searching

(* Transition: t_select_from_search *)
t_t_select_from_search ==
    /\ state = STATE_searching
    /\ state' = STATE_viewing

(* Transition: t_versions *)
t_t_versions ==
    /\ state = STATE_viewing
    /\ state' = STATE_viewing

(* Transition: t_compare *)
t_t_compare ==
    /\ state = STATE_viewing
    /\ state' = STATE_comparing

(* Transition: t_compare_again *)
t_t_compare_again ==
    /\ state = STATE_comparing
    /\ state' = STATE_comparing

(* Transition: t_rollback *)
t_t_rollback ==
    /\ state = STATE_viewing
    /\ state' = STATE_viewing

(* Transition: t_deps *)
t_t_deps ==
    /\ state = STATE_viewing
    /\ state' = STATE_viewing

(* Transition: t_check_deps *)
t_t_check_deps ==
    /\ state = STATE_viewing
    /\ state' = STATE_viewing

(* Transition: t_deprecate *)
t_t_deprecate ==
    /\ state = STATE_viewing
    /\ state' = STATE_viewing

(* Transition: t_delete *)
t_t_delete ==
    /\ state = STATE_viewing
    /\ state' = STATE_ready

(* Transition: t_delete_from_ready *)
t_t_delete_from_ready ==
    /\ state = STATE_ready
    /\ state' = STATE_ready

(* Transition: t_export *)
t_t_export ==
    /\ state = STATE_ready
    /\ state' = STATE_ready

(* Transition: t_export_from_viewing *)
t_t_export_from_viewing ==
    /\ state = STATE_viewing
    /\ state' = STATE_viewing

(* Transition: t_stats *)
t_t_stats ==
    /\ state = STATE_ready
    /\ state' = STATE_ready

(* Transition: t_back_from_viewing *)
t_t_back_from_viewing ==
    /\ state = STATE_viewing
    /\ state' = STATE_ready

(* Transition: t_back_from_searching *)
t_t_back_from_searching ==
    /\ state = STATE_searching
    /\ state' = STATE_ready

(* Transition: t_back_from_comparing *)
t_t_back_from_comparing ==
    /\ state = STATE_comparing
    /\ state' = STATE_viewing

(* Transition: t_error_recover *)
t_t_error_recover ==
    /\ state = STATE_error
    /\ state' = STATE_idle

(* Transition: t_load_failed *)
t_t_load_failed ==
    /\ TRUE  \* Global transition
    /\ state' = STATE_error

Next ==
    \/ t_t_init_registry
    \/ t_t_load_registry
    \/ t_t_reload_registry
    \/ t_t_register
    \/ t_t_update
    \/ t_t_update_from_viewing
    \/ t_t_get
    \/ t_t_get_another
    \/ t_t_list
    \/ t_t_search
    \/ t_t_search_again
    \/ t_t_select_from_search
    \/ t_t_versions
    \/ t_t_compare
    \/ t_t_compare_again
    \/ t_t_rollback
    \/ t_t_deps
    \/ t_t_check_deps
    \/ t_t_deprecate
    \/ t_t_delete
    \/ t_t_delete_from_ready
    \/ t_t_export
    \/ t_t_export_from_viewing
    \/ t_t_stats
    \/ t_t_back_from_viewing
    \/ t_t_back_from_searching
    \/ t_t_back_from_comparing
    \/ t_t_error_recover
    \/ t_t_load_failed

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA IniregistryPreservesInv == Inv /\ t_t_init_registry => Inv'
BY ConstantsDistinct DEF Inv, t_t_init_registry, TypeInvariant, States

LEMMA LoadRegistryPreservesInv == Inv /\ t_t_load_registry => Inv'
BY ConstantsDistinct DEF Inv, t_t_load_registry, TypeInvariant, States

LEMMA ReloadRegistryPreservesInv == Inv /\ t_t_reload_registry => Inv'
BY ConstantsDistinct DEF Inv, t_t_reload_registry, TypeInvariant, States

LEMMA RegisterPreservesInv == Inv /\ t_t_register => Inv'
BY ConstantsDistinct DEF Inv, t_t_register, TypeInvariant, States

LEMMA UpdatePreservesInv == Inv /\ t_t_update => Inv'
BY ConstantsDistinct DEF Inv, t_t_update, TypeInvariant, States

LEMMA UpdateFromViewingPreservesInv == Inv /\ t_t_update_from_viewing => Inv'
BY ConstantsDistinct DEF Inv, t_t_update_from_viewing, TypeInvariant, States

LEMMA GetPreservesInv == Inv /\ t_t_get => Inv'
BY ConstantsDistinct DEF Inv, t_t_get, TypeInvariant, States

LEMMA GeanotherPreservesInv == Inv /\ t_t_get_another => Inv'
BY ConstantsDistinct DEF Inv, t_t_get_another, TypeInvariant, States

LEMMA ListPreservesInv == Inv /\ t_t_list => Inv'
BY ConstantsDistinct DEF Inv, t_t_list, TypeInvariant, States

LEMMA SearchPreservesInv == Inv /\ t_t_search => Inv'
BY ConstantsDistinct DEF Inv, t_t_search, TypeInvariant, States

LEMMA SearchAgainPreservesInv == Inv /\ t_t_search_again => Inv'
BY ConstantsDistinct DEF Inv, t_t_search_again, TypeInvariant, States

LEMMA SelecfromSearchPreservesInv == Inv /\ t_t_select_from_search => Inv'
BY ConstantsDistinct DEF Inv, t_t_select_from_search, TypeInvariant, States

LEMMA VersionsPreservesInv == Inv /\ t_t_versions => Inv'
BY ConstantsDistinct DEF Inv, t_t_versions, TypeInvariant, States

LEMMA ComparePreservesInv == Inv /\ t_t_compare => Inv'
BY ConstantsDistinct DEF Inv, t_t_compare, TypeInvariant, States

LEMMA CompareAgainPreservesInv == Inv /\ t_t_compare_again => Inv'
BY ConstantsDistinct DEF Inv, t_t_compare_again, TypeInvariant, States

LEMMA RollbackPreservesInv == Inv /\ t_t_rollback => Inv'
BY ConstantsDistinct DEF Inv, t_t_rollback, TypeInvariant, States

LEMMA DepsPreservesInv == Inv /\ t_t_deps => Inv'
BY ConstantsDistinct DEF Inv, t_t_deps, TypeInvariant, States

LEMMA CheckDepsPreservesInv == Inv /\ t_t_check_deps => Inv'
BY ConstantsDistinct DEF Inv, t_t_check_deps, TypeInvariant, States

LEMMA DeprecatePreservesInv == Inv /\ t_t_deprecate => Inv'
BY ConstantsDistinct DEF Inv, t_t_deprecate, TypeInvariant, States

LEMMA DeletePreservesInv == Inv /\ t_t_delete => Inv'
BY ConstantsDistinct DEF Inv, t_t_delete, TypeInvariant, States

LEMMA DeleteFromReadyPreservesInv == Inv /\ t_t_delete_from_ready => Inv'
BY ConstantsDistinct DEF Inv, t_t_delete_from_ready, TypeInvariant, States

LEMMA ExportPreservesInv == Inv /\ t_t_export => Inv'
BY ConstantsDistinct DEF Inv, t_t_export, TypeInvariant, States

LEMMA ExporfromViewingPreservesInv == Inv /\ t_t_export_from_viewing => Inv'
BY ConstantsDistinct DEF Inv, t_t_export_from_viewing, TypeInvariant, States

LEMMA StatsPreservesInv == Inv /\ t_t_stats => Inv'
BY ConstantsDistinct DEF Inv, t_t_stats, TypeInvariant, States

LEMMA BackFromViewingPreservesInv == Inv /\ t_t_back_from_viewing => Inv'
BY ConstantsDistinct DEF Inv, t_t_back_from_viewing, TypeInvariant, States

LEMMA BackFromSearchingPreservesInv == Inv /\ t_t_back_from_searching => Inv'
BY ConstantsDistinct DEF Inv, t_t_back_from_searching, TypeInvariant, States

LEMMA BackFromComparingPreservesInv == Inv /\ t_t_back_from_comparing => Inv'
BY ConstantsDistinct DEF Inv, t_t_back_from_comparing, TypeInvariant, States

LEMMA ErrorRecoverPreservesInv == Inv /\ t_t_error_recover => Inv'
BY ConstantsDistinct DEF Inv, t_t_error_recover, TypeInvariant, States

LEMMA LoadFailedPreservesInv == Inv /\ t_t_load_failed => Inv'
BY ConstantsDistinct DEF Inv, t_t_load_failed, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY IniregistryPreservesInv, LoadRegistryPreservesInv, ReloadRegistryPreservesInv, RegisterPreservesInv, UpdatePreservesInv, UpdateFromViewingPreservesInv, GetPreservesInv, GeanotherPreservesInv, ListPreservesInv, SearchPreservesInv, SearchAgainPreservesInv, SelecfromSearchPreservesInv, VersionsPreservesInv, ComparePreservesInv, CompareAgainPreservesInv, RollbackPreservesInv, DepsPreservesInv, CheckDepsPreservesInv, DeprecatePreservesInv, DeletePreservesInv, DeleteFromReadyPreservesInv, ExportPreservesInv, ExporfromViewingPreservesInv, StatsPreservesInv, BackFromViewingPreservesInv, BackFromSearchingPreservesInv, BackFromComparingPreservesInv, ErrorRecoverPreservesInv, LoadFailedPreservesInv DEF Next

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