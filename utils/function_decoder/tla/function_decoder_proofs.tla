--------------------------- MODULE function_decoder_proofs ---------------------------
(*
 * L++ Blueprint: Python Function Decoder
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_parsing, STATE_extracting, STATE_tracing, STATE_computing, STATE_complete, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_parsing
    /\ STATE_idle /= STATE_extracting
    /\ STATE_idle /= STATE_tracing
    /\ STATE_idle /= STATE_computing
    /\ STATE_idle /= STATE_complete
    /\ STATE_idle /= STATE_error
    /\ STATE_parsing /= STATE_extracting
    /\ STATE_parsing /= STATE_tracing
    /\ STATE_parsing /= STATE_computing
    /\ STATE_parsing /= STATE_complete
    /\ STATE_parsing /= STATE_error
    /\ STATE_extracting /= STATE_tracing
    /\ STATE_extracting /= STATE_computing
    /\ STATE_extracting /= STATE_complete
    /\ STATE_extracting /= STATE_error
    /\ STATE_tracing /= STATE_computing
    /\ STATE_tracing /= STATE_complete
    /\ STATE_tracing /= STATE_error
    /\ STATE_computing /= STATE_complete
    /\ STATE_computing /= STATE_error
    /\ STATE_complete /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_parsing, STATE_extracting, STATE_tracing, STATE_computing, STATE_complete, STATE_error}
TerminalStates == {}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_start_decode *)
t_t_start_decode ==
    /\ state = STATE_idle
    /\ state' = STATE_parsing

(* Transition: t_parse_error *)
t_t_parse_error ==
    /\ state = STATE_parsing
    /\ state' = STATE_error

(* Transition: t_parse_done *)
t_t_parse_done ==
    /\ state = STATE_parsing
    /\ state' = STATE_extracting

(* Transition: t_extract_error *)
t_t_extract_error ==
    /\ state = STATE_extracting
    /\ state' = STATE_error

(* Transition: t_extract_done *)
t_t_extract_done ==
    /\ state = STATE_extracting
    /\ state' = STATE_tracing

(* Transition: t_trace_error *)
t_t_trace_error ==
    /\ state = STATE_tracing
    /\ state' = STATE_error

(* Transition: t_trace_done *)
t_t_trace_done ==
    /\ state = STATE_tracing
    /\ state' = STATE_computing

(* Transition: t_compute_error *)
t_t_compute_error ==
    /\ state = STATE_computing
    /\ state' = STATE_error

(* Transition: t_compute_done *)
t_t_compute_done ==
    /\ state = STATE_computing
    /\ state' = STATE_complete

(* Transition: t_reset *)
t_t_reset ==
    /\ TRUE  \* Global transition
    /\ state' = STATE_idle

Next ==
    \/ t_t_start_decode
    \/ t_t_parse_error
    \/ t_t_parse_done
    \/ t_t_extract_error
    \/ t_t_extract_done
    \/ t_t_trace_error
    \/ t_t_trace_done
    \/ t_t_compute_error
    \/ t_t_compute_done
    \/ t_t_reset

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA StardecodePreservesInv == Inv /\ t_t_start_decode => Inv'
BY ConstantsDistinct DEF Inv, t_t_start_decode, TypeInvariant, States

LEMMA ParseErrorPreservesInv == Inv /\ t_t_parse_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_parse_error, TypeInvariant, States

LEMMA ParseDonePreservesInv == Inv /\ t_t_parse_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_parse_done, TypeInvariant, States

LEMMA ExtracerrorPreservesInv == Inv /\ t_t_extract_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_extract_error, TypeInvariant, States

LEMMA ExtracdonePreservesInv == Inv /\ t_t_extract_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_extract_done, TypeInvariant, States

LEMMA TraceErrorPreservesInv == Inv /\ t_t_trace_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_trace_error, TypeInvariant, States

LEMMA TraceDonePreservesInv == Inv /\ t_t_trace_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_trace_done, TypeInvariant, States

LEMMA ComputeErrorPreservesInv == Inv /\ t_t_compute_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_compute_error, TypeInvariant, States

LEMMA ComputeDonePreservesInv == Inv /\ t_t_compute_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_compute_done, TypeInvariant, States

LEMMA ResetPreservesInv == Inv /\ t_t_reset => Inv'
BY ConstantsDistinct DEF Inv, t_t_reset, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY StardecodePreservesInv, ParseErrorPreservesInv, ParseDonePreservesInv, ExtracerrorPreservesInv, ExtracdonePreservesInv, TraceErrorPreservesInv, TraceDonePreservesInv, ComputeErrorPreservesInv, ComputeDonePreservesInv, ResetPreservesInv DEF Next

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