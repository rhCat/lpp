--------------------------- MODULE compliance_checker_proofs ---------------------------
(*
 * L++ Blueprint: L++ Compliance Checker
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_blueprint_loaded, STATE_ready, STATE_checking, STATE_report_ready, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_blueprint_loaded
    /\ STATE_idle /= STATE_ready
    /\ STATE_idle /= STATE_checking
    /\ STATE_idle /= STATE_report_ready
    /\ STATE_idle /= STATE_error
    /\ STATE_blueprint_loaded /= STATE_ready
    /\ STATE_blueprint_loaded /= STATE_checking
    /\ STATE_blueprint_loaded /= STATE_report_ready
    /\ STATE_blueprint_loaded /= STATE_error
    /\ STATE_ready /= STATE_checking
    /\ STATE_ready /= STATE_report_ready
    /\ STATE_ready /= STATE_error
    /\ STATE_checking /= STATE_report_ready
    /\ STATE_checking /= STATE_error
    /\ STATE_report_ready /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_blueprint_loaded, STATE_ready, STATE_checking, STATE_report_ready, STATE_error}
TerminalStates == {}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_load_blueprint *)
t_t_load_blueprint ==
    /\ state = STATE_idle
    /\ state' = STATE_blueprint_loaded

(* Transition: t_load_blueprint_error *)
t_t_load_blueprint_error ==
    /\ state = STATE_idle
    /\ state' = STATE_error

(* Transition: t_reload_blueprint *)
t_t_reload_blueprint ==
    /\ state = STATE_blueprint_loaded
    /\ state' = STATE_blueprint_loaded

(* Transition: t_reload_blueprint_ready *)
t_t_reload_blueprint_ready ==
    /\ state = STATE_ready
    /\ state' = STATE_ready

(* Transition: t_reload_blueprint_report *)
t_t_reload_blueprint_report ==
    /\ state = STATE_report_ready
    /\ state' = STATE_ready

(* Transition: t_load_policies *)
t_t_load_policies ==
    /\ state = STATE_blueprint_loaded
    /\ state' = STATE_ready

(* Transition: t_load_single_policy *)
t_t_load_single_policy ==
    /\ state = STATE_blueprint_loaded
    /\ state' = STATE_ready

(* Transition: t_reload_policies *)
t_t_reload_policies ==
    /\ state = STATE_ready
    /\ state' = STATE_ready

(* Transition: t_reload_policies_report *)
t_t_reload_policies_report ==
    /\ state = STATE_report_ready
    /\ state' = STATE_ready

(* Transition: t_add_policy *)
t_t_add_policy ==
    /\ state = STATE_ready
    /\ state' = STATE_ready

(* Transition: t_check_all *)
t_t_check_all ==
    /\ state = STATE_ready
    /\ state' = STATE_checking

(* Transition: t_check_single *)
t_t_check_single ==
    /\ state = STATE_ready
    /\ state' = STATE_checking

(* Transition: t_generate_report *)
t_t_generate_report ==
    /\ state = STATE_checking
    /\ state' = STATE_report_ready

(* Transition: t_auto_report *)
t_t_auto_report ==
    /\ state = STATE_checking
    /\ state' = STATE_report_ready

(* Transition: t_export_report *)
t_t_export_report ==
    /\ state = STATE_report_ready
    /\ state' = STATE_report_ready

(* Transition: t_recheck *)
t_t_recheck ==
    /\ state = STATE_report_ready
    /\ state' = STATE_checking

(* Transition: t_back_to_ready *)
t_t_back_to_ready ==
    /\ state = STATE_report_ready
    /\ state' = STATE_ready

(* Transition: t_back_to_loaded *)
t_t_back_to_loaded ==
    /\ state = STATE_ready
    /\ state' = STATE_blueprint_loaded

(* Transition: t_unload *)
t_t_unload ==
    /\ state = STATE_blueprint_loaded
    /\ state' = STATE_idle

(* Transition: t_unload_ready *)
t_t_unload_ready ==
    /\ state = STATE_ready
    /\ state' = STATE_idle

(* Transition: t_unload_report *)
t_t_unload_report ==
    /\ state = STATE_report_ready
    /\ state' = STATE_idle

(* Transition: t_recover *)
t_t_recover ==
    /\ state = STATE_error
    /\ state' = STATE_idle

(* Transition: t_global_error *)
t_t_global_error ==
    /\ TRUE  \* Global transition
    /\ state' = STATE_error

Next ==
    \/ t_t_load_blueprint
    \/ t_t_load_blueprint_error
    \/ t_t_reload_blueprint
    \/ t_t_reload_blueprint_ready
    \/ t_t_reload_blueprint_report
    \/ t_t_load_policies
    \/ t_t_load_single_policy
    \/ t_t_reload_policies
    \/ t_t_reload_policies_report
    \/ t_t_add_policy
    \/ t_t_check_all
    \/ t_t_check_single
    \/ t_t_generate_report
    \/ t_t_auto_report
    \/ t_t_export_report
    \/ t_t_recheck
    \/ t_t_back_to_ready
    \/ t_t_back_to_loaded
    \/ t_t_unload
    \/ t_t_unload_ready
    \/ t_t_unload_report
    \/ t_t_recover
    \/ t_t_global_error

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA LoadBlueprintPreservesInv == Inv /\ t_t_load_blueprint => Inv'
BY ConstantsDistinct DEF Inv, t_t_load_blueprint, TypeInvariant, States

LEMMA LoadBlueprinerrorPreservesInv == Inv /\ t_t_load_blueprint_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_load_blueprint_error, TypeInvariant, States

LEMMA ReloadBlueprintPreservesInv == Inv /\ t_t_reload_blueprint => Inv'
BY ConstantsDistinct DEF Inv, t_t_reload_blueprint, TypeInvariant, States

LEMMA ReloadBlueprinreadyPreservesInv == Inv /\ t_t_reload_blueprint_ready => Inv'
BY ConstantsDistinct DEF Inv, t_t_reload_blueprint_ready, TypeInvariant, States

LEMMA ReloadBlueprinreportPreservesInv == Inv /\ t_t_reload_blueprint_report => Inv'
BY ConstantsDistinct DEF Inv, t_t_reload_blueprint_report, TypeInvariant, States

LEMMA LoadPoliciesPreservesInv == Inv /\ t_t_load_policies => Inv'
BY ConstantsDistinct DEF Inv, t_t_load_policies, TypeInvariant, States

LEMMA LoadSinglePolicyPreservesInv == Inv /\ t_t_load_single_policy => Inv'
BY ConstantsDistinct DEF Inv, t_t_load_single_policy, TypeInvariant, States

LEMMA ReloadPoliciesPreservesInv == Inv /\ t_t_reload_policies => Inv'
BY ConstantsDistinct DEF Inv, t_t_reload_policies, TypeInvariant, States

LEMMA ReloadPoliciesReportPreservesInv == Inv /\ t_t_reload_policies_report => Inv'
BY ConstantsDistinct DEF Inv, t_t_reload_policies_report, TypeInvariant, States

LEMMA AddPolicyPreservesInv == Inv /\ t_t_add_policy => Inv'
BY ConstantsDistinct DEF Inv, t_t_add_policy, TypeInvariant, States

LEMMA CheckAllPreservesInv == Inv /\ t_t_check_all => Inv'
BY ConstantsDistinct DEF Inv, t_t_check_all, TypeInvariant, States

LEMMA CheckSinglePreservesInv == Inv /\ t_t_check_single => Inv'
BY ConstantsDistinct DEF Inv, t_t_check_single, TypeInvariant, States

LEMMA GenerateReportPreservesInv == Inv /\ t_t_generate_report => Inv'
BY ConstantsDistinct DEF Inv, t_t_generate_report, TypeInvariant, States

LEMMA AutoReportPreservesInv == Inv /\ t_t_auto_report => Inv'
BY ConstantsDistinct DEF Inv, t_t_auto_report, TypeInvariant, States

LEMMA ExporreportPreservesInv == Inv /\ t_t_export_report => Inv'
BY ConstantsDistinct DEF Inv, t_t_export_report, TypeInvariant, States

LEMMA RecheckPreservesInv == Inv /\ t_t_recheck => Inv'
BY ConstantsDistinct DEF Inv, t_t_recheck, TypeInvariant, States

LEMMA BackToReadyPreservesInv == Inv /\ t_t_back_to_ready => Inv'
BY ConstantsDistinct DEF Inv, t_t_back_to_ready, TypeInvariant, States

LEMMA BackToLoadedPreservesInv == Inv /\ t_t_back_to_loaded => Inv'
BY ConstantsDistinct DEF Inv, t_t_back_to_loaded, TypeInvariant, States

LEMMA UnloadPreservesInv == Inv /\ t_t_unload => Inv'
BY ConstantsDistinct DEF Inv, t_t_unload, TypeInvariant, States

LEMMA UnloadReadyPreservesInv == Inv /\ t_t_unload_ready => Inv'
BY ConstantsDistinct DEF Inv, t_t_unload_ready, TypeInvariant, States

LEMMA UnloadReportPreservesInv == Inv /\ t_t_unload_report => Inv'
BY ConstantsDistinct DEF Inv, t_t_unload_report, TypeInvariant, States

LEMMA RecoverPreservesInv == Inv /\ t_t_recover => Inv'
BY ConstantsDistinct DEF Inv, t_t_recover, TypeInvariant, States

LEMMA GlobalErrorPreservesInv == Inv /\ t_t_global_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_global_error, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY LoadBlueprintPreservesInv, LoadBlueprinerrorPreservesInv, ReloadBlueprintPreservesInv, ReloadBlueprinreadyPreservesInv, ReloadBlueprinreportPreservesInv, LoadPoliciesPreservesInv, LoadSinglePolicyPreservesInv, ReloadPoliciesPreservesInv, ReloadPoliciesReportPreservesInv, AddPolicyPreservesInv, CheckAllPreservesInv, CheckSinglePreservesInv, GenerateReportPreservesInv, AutoReportPreservesInv, ExporreportPreservesInv, RecheckPreservesInv, BackToReadyPreservesInv, BackToLoadedPreservesInv, UnloadPreservesInv, UnloadReadyPreservesInv, UnloadReportPreservesInv, RecoverPreservesInv, GlobalErrorPreservesInv DEF Next

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