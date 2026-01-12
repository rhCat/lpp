--------------------------- MODULE lpp_visualizer_proofs ---------------------------
(*
 * L++ Blueprint: L++ Blueprint Visualizer
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_loading, STATE_rendering, STATE_complete, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_loading
    /\ STATE_idle /= STATE_rendering
    /\ STATE_idle /= STATE_complete
    /\ STATE_idle /= STATE_error
    /\ STATE_loading /= STATE_rendering
    /\ STATE_loading /= STATE_complete
    /\ STATE_loading /= STATE_error
    /\ STATE_rendering /= STATE_complete
    /\ STATE_rendering /= STATE_error
    /\ STATE_complete /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_loading, STATE_rendering, STATE_complete, STATE_error}
TerminalStates == {STATE_complete, STATE_error}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_visualize *)
t_t_visualize ==
    /\ state = STATE_idle
    /\ state' = STATE_loading

(* Transition: t_loaded *)
t_t_loaded ==
    /\ state = STATE_loading
    /\ state' = STATE_rendering

(* Transition: t_rendered *)
t_t_rendered ==
    /\ state = STATE_rendering
    /\ state' = STATE_complete

(* Transition: t_load_err *)
t_t_load_err ==
    /\ state = STATE_loading
    /\ state' = STATE_error

(* Transition: t_render_err *)
t_t_render_err ==
    /\ state = STATE_rendering
    /\ state' = STATE_error

(* Transition: t_reset *)
t_t_reset ==
    /\ TRUE  \* Global transition
    /\ state' = STATE_idle

Next ==
    \/ t_t_visualize
    \/ t_t_loaded
    \/ t_t_rendered
    \/ t_t_load_err
    \/ t_t_render_err
    \/ t_t_reset

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA VisualizePreservesInv == Inv /\ t_t_visualize => Inv'
BY ConstantsDistinct DEF Inv, t_t_visualize, TypeInvariant, States

LEMMA LoadedPreservesInv == Inv /\ t_t_loaded => Inv'
BY ConstantsDistinct DEF Inv, t_t_loaded, TypeInvariant, States

LEMMA RenderedPreservesInv == Inv /\ t_t_rendered => Inv'
BY ConstantsDistinct DEF Inv, t_t_rendered, TypeInvariant, States

LEMMA LoadErrPreservesInv == Inv /\ t_t_load_err => Inv'
BY ConstantsDistinct DEF Inv, t_t_load_err, TypeInvariant, States

LEMMA RenderErrPreservesInv == Inv /\ t_t_render_err => Inv'
BY ConstantsDistinct DEF Inv, t_t_render_err, TypeInvariant, States

LEMMA ResetPreservesInv == Inv /\ t_t_reset => Inv'
BY ConstantsDistinct DEF Inv, t_t_reset, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY VisualizePreservesInv, LoadedPreservesInv, RenderedPreservesInv, LoadErrPreservesInv, RenderErrPreservesInv, ResetPreservesInv DEF Next

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