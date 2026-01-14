--------------------------- MODULE task_tracker_proofs ---------------------------
(*
 * L++ Blueprint: Task Tracker
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_init, STATE_menu, STATE_adding, STATE_listing, STATE_viewing, STATE_completing, STATE_deleting, STATE_saving, STATE_done, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_init /= STATE_menu
    /\ STATE_init /= STATE_adding
    /\ STATE_init /= STATE_listing
    /\ STATE_init /= STATE_viewing
    /\ STATE_init /= STATE_completing
    /\ STATE_init /= STATE_deleting
    /\ STATE_init /= STATE_saving
    /\ STATE_init /= STATE_done
    /\ STATE_init /= STATE_error
    /\ STATE_menu /= STATE_adding
    /\ STATE_menu /= STATE_listing
    /\ STATE_menu /= STATE_viewing
    /\ STATE_menu /= STATE_completing
    /\ STATE_menu /= STATE_deleting
    /\ STATE_menu /= STATE_saving
    /\ STATE_menu /= STATE_done
    /\ STATE_menu /= STATE_error
    /\ STATE_adding /= STATE_listing
    /\ STATE_adding /= STATE_viewing
    /\ STATE_adding /= STATE_completing
    /\ STATE_adding /= STATE_deleting
    /\ STATE_adding /= STATE_saving
    /\ STATE_adding /= STATE_done
    /\ STATE_adding /= STATE_error
    /\ STATE_listing /= STATE_viewing
    /\ STATE_listing /= STATE_completing
    /\ STATE_listing /= STATE_deleting
    /\ STATE_listing /= STATE_saving
    /\ STATE_listing /= STATE_done
    /\ STATE_listing /= STATE_error
    /\ STATE_viewing /= STATE_completing
    /\ STATE_viewing /= STATE_deleting
    /\ STATE_viewing /= STATE_saving
    /\ STATE_viewing /= STATE_done
    /\ STATE_viewing /= STATE_error
    /\ STATE_completing /= STATE_deleting
    /\ STATE_completing /= STATE_saving
    /\ STATE_completing /= STATE_done
    /\ STATE_completing /= STATE_error
    /\ STATE_deleting /= STATE_saving
    /\ STATE_deleting /= STATE_done
    /\ STATE_deleting /= STATE_error
    /\ STATE_saving /= STATE_done
    /\ STATE_saving /= STATE_error
    /\ STATE_done /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_init, STATE_menu, STATE_adding, STATE_listing, STATE_viewing, STATE_completing, STATE_deleting, STATE_saving, STATE_done, STATE_error}
TerminalStates == {STATE_done, STATE_error}

TypeInvariant == state \in States

Init == state = STATE_init

(* Transition: t_init *)
t_t_init ==
    /\ state = STATE_init
    /\ state' = STATE_menu

(* Transition: t_add_start *)
t_t_add_start ==
    /\ state = STATE_menu
    /\ state' = STATE_adding

(* Transition: t_add_confirm *)
t_t_add_confirm ==
    /\ state = STATE_adding
    /\ state' = STATE_saving

(* Transition: t_add_cancel *)
t_t_add_cancel ==
    /\ state = STATE_adding
    /\ state' = STATE_menu

(* Transition: t_list *)
t_t_list ==
    /\ state = STATE_menu
    /\ state' = STATE_listing

(* Transition: t_list_back *)
t_t_list_back ==
    /\ state = STATE_listing
    /\ state' = STATE_menu

(* Transition: t_view *)
t_t_view ==
    /\ state = STATE_listing
    /\ state' = STATE_viewing

(* Transition: t_view_back *)
t_t_view_back ==
    /\ state = STATE_viewing
    /\ state' = STATE_listing

(* Transition: t_complete_start *)
t_t_complete_start ==
    /\ state = STATE_viewing
    /\ state' = STATE_completing

(* Transition: t_complete_confirm *)
t_t_complete_confirm ==
    /\ state = STATE_completing
    /\ state' = STATE_saving

(* Transition: t_complete_cancel *)
t_t_complete_cancel ==
    /\ state = STATE_completing
    /\ state' = STATE_viewing

(* Transition: t_delete_start *)
t_t_delete_start ==
    /\ state = STATE_viewing
    /\ state' = STATE_deleting

(* Transition: t_delete_confirm *)
t_t_delete_confirm ==
    /\ state = STATE_deleting
    /\ state' = STATE_saving

(* Transition: t_delete_cancel *)
t_t_delete_cancel ==
    /\ state = STATE_deleting
    /\ state' = STATE_viewing

(* Transition: t_save_success *)
t_t_save_success ==
    /\ state = STATE_saving
    /\ state' = STATE_menu

(* Transition: t_save_error *)
t_t_save_error ==
    /\ state = STATE_saving
    /\ state' = STATE_error

(* Transition: t_quit *)
t_t_quit ==
    /\ state = STATE_menu
    /\ state' = STATE_done

(* Transition: t_error_retry *)
t_t_error_retry ==
    /\ state = STATE_error
    /\ state' = STATE_menu

Next ==
    \/ t_t_init
    \/ t_t_add_start
    \/ t_t_add_confirm
    \/ t_t_add_cancel
    \/ t_t_list
    \/ t_t_list_back
    \/ t_t_view
    \/ t_t_view_back
    \/ t_t_complete_start
    \/ t_t_complete_confirm
    \/ t_t_complete_cancel
    \/ t_t_delete_start
    \/ t_t_delete_confirm
    \/ t_t_delete_cancel
    \/ t_t_save_success
    \/ t_t_save_error
    \/ t_t_quit
    \/ t_t_error_retry

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA InitPreservesInv == Inv /\ t_t_init => Inv'
BY ConstantsDistinct DEF Inv, t_t_init, TypeInvariant, States

LEMMA AddStartPreservesInv == Inv /\ t_t_add_start => Inv'
BY ConstantsDistinct DEF Inv, t_t_add_start, TypeInvariant, States

LEMMA AddConfirmPreservesInv == Inv /\ t_t_add_confirm => Inv'
BY ConstantsDistinct DEF Inv, t_t_add_confirm, TypeInvariant, States

LEMMA AddCancelPreservesInv == Inv /\ t_t_add_cancel => Inv'
BY ConstantsDistinct DEF Inv, t_t_add_cancel, TypeInvariant, States

LEMMA ListPreservesInv == Inv /\ t_t_list => Inv'
BY ConstantsDistinct DEF Inv, t_t_list, TypeInvariant, States

LEMMA LisbackPreservesInv == Inv /\ t_t_list_back => Inv'
BY ConstantsDistinct DEF Inv, t_t_list_back, TypeInvariant, States

LEMMA ViewPreservesInv == Inv /\ t_t_view => Inv'
BY ConstantsDistinct DEF Inv, t_t_view, TypeInvariant, States

LEMMA ViewBackPreservesInv == Inv /\ t_t_view_back => Inv'
BY ConstantsDistinct DEF Inv, t_t_view_back, TypeInvariant, States

LEMMA CompleteStartPreservesInv == Inv /\ t_t_complete_start => Inv'
BY ConstantsDistinct DEF Inv, t_t_complete_start, TypeInvariant, States

LEMMA CompleteConfirmPreservesInv == Inv /\ t_t_complete_confirm => Inv'
BY ConstantsDistinct DEF Inv, t_t_complete_confirm, TypeInvariant, States

LEMMA CompleteCancelPreservesInv == Inv /\ t_t_complete_cancel => Inv'
BY ConstantsDistinct DEF Inv, t_t_complete_cancel, TypeInvariant, States

LEMMA DeleteStartPreservesInv == Inv /\ t_t_delete_start => Inv'
BY ConstantsDistinct DEF Inv, t_t_delete_start, TypeInvariant, States

LEMMA DeleteConfirmPreservesInv == Inv /\ t_t_delete_confirm => Inv'
BY ConstantsDistinct DEF Inv, t_t_delete_confirm, TypeInvariant, States

LEMMA DeleteCancelPreservesInv == Inv /\ t_t_delete_cancel => Inv'
BY ConstantsDistinct DEF Inv, t_t_delete_cancel, TypeInvariant, States

LEMMA SaveSuccessPreservesInv == Inv /\ t_t_save_success => Inv'
BY ConstantsDistinct DEF Inv, t_t_save_success, TypeInvariant, States

LEMMA SaveErrorPreservesInv == Inv /\ t_t_save_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_save_error, TypeInvariant, States

LEMMA QuitPreservesInv == Inv /\ t_t_quit => Inv'
BY ConstantsDistinct DEF Inv, t_t_quit, TypeInvariant, States

LEMMA ErrorRetryPreservesInv == Inv /\ t_t_error_retry => Inv'
BY ConstantsDistinct DEF Inv, t_t_error_retry, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY InitPreservesInv, AddStartPreservesInv, AddConfirmPreservesInv, AddCancelPreservesInv, ListPreservesInv, LisbackPreservesInv, ViewPreservesInv, ViewBackPreservesInv, CompleteStartPreservesInv, CompleteConfirmPreservesInv, CompleteCancelPreservesInv, DeleteStartPreservesInv, DeleteConfirmPreservesInv, DeleteCancelPreservesInv, SaveSuccessPreservesInv, SaveErrorPreservesInv, QuitPreservesInv, ErrorRetryPreservesInv DEF Next

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