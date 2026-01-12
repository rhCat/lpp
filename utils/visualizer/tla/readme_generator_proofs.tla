--------------------------- MODULE readme_generator_proofs ---------------------------
(*
 * L++ Blueprint: L++ README Generator
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_init, STATE_generating_header, STATE_generating_mermaid, STATE_generating_tables, STATE_assembling, STATE_writing, STATE_done, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_init /= STATE_generating_header
    /\ STATE_init /= STATE_generating_mermaid
    /\ STATE_init /= STATE_generating_tables
    /\ STATE_init /= STATE_assembling
    /\ STATE_init /= STATE_writing
    /\ STATE_init /= STATE_done
    /\ STATE_init /= STATE_error
    /\ STATE_generating_header /= STATE_generating_mermaid
    /\ STATE_generating_header /= STATE_generating_tables
    /\ STATE_generating_header /= STATE_assembling
    /\ STATE_generating_header /= STATE_writing
    /\ STATE_generating_header /= STATE_done
    /\ STATE_generating_header /= STATE_error
    /\ STATE_generating_mermaid /= STATE_generating_tables
    /\ STATE_generating_mermaid /= STATE_assembling
    /\ STATE_generating_mermaid /= STATE_writing
    /\ STATE_generating_mermaid /= STATE_done
    /\ STATE_generating_mermaid /= STATE_error
    /\ STATE_generating_tables /= STATE_assembling
    /\ STATE_generating_tables /= STATE_writing
    /\ STATE_generating_tables /= STATE_done
    /\ STATE_generating_tables /= STATE_error
    /\ STATE_assembling /= STATE_writing
    /\ STATE_assembling /= STATE_done
    /\ STATE_assembling /= STATE_error
    /\ STATE_writing /= STATE_done
    /\ STATE_writing /= STATE_error
    /\ STATE_done /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_init, STATE_generating_header, STATE_generating_mermaid, STATE_generating_tables, STATE_assembling, STATE_writing, STATE_done, STATE_error}
TerminalStates == {STATE_done, STATE_error}

TypeInvariant == state \in States

Init == state = STATE_init

(* Transition: t_start *)
t_t_start ==
    /\ state = STATE_init
    /\ state' = STATE_generating_header

(* Transition: t_no_blueprint *)
t_t_no_blueprint ==
    /\ state = STATE_init
    /\ state' = STATE_error

(* Transition: t_to_mermaid *)
t_t_to_mermaid ==
    /\ state = STATE_generating_header
    /\ state' = STATE_generating_mermaid

(* Transition: t_to_tables *)
t_t_to_tables ==
    /\ state = STATE_generating_mermaid
    /\ state' = STATE_generating_tables

(* Transition: t_to_assemble *)
t_t_to_assemble ==
    /\ state = STATE_generating_tables
    /\ state' = STATE_assembling

(* Transition: t_to_write *)
t_t_to_write ==
    /\ state = STATE_assembling
    /\ state' = STATE_writing

(* Transition: t_done *)
t_t_done ==
    /\ state = STATE_writing
    /\ state' = STATE_done

Next ==
    \/ t_t_start
    \/ t_t_no_blueprint
    \/ t_t_to_mermaid
    \/ t_t_to_tables
    \/ t_t_to_assemble
    \/ t_t_to_write
    \/ t_t_done

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA StartPreservesInv == Inv /\ t_t_start => Inv'
BY ConstantsDistinct DEF Inv, t_t_start, TypeInvariant, States

LEMMA NoBlueprintPreservesInv == Inv /\ t_t_no_blueprint => Inv'
BY ConstantsDistinct DEF Inv, t_t_no_blueprint, TypeInvariant, States

LEMMA ToMermaidPreservesInv == Inv /\ t_t_to_mermaid => Inv'
BY ConstantsDistinct DEF Inv, t_t_to_mermaid, TypeInvariant, States

LEMMA ToTablesPreservesInv == Inv /\ t_t_to_tables => Inv'
BY ConstantsDistinct DEF Inv, t_t_to_tables, TypeInvariant, States

LEMMA ToAssemblePreservesInv == Inv /\ t_t_to_assemble => Inv'
BY ConstantsDistinct DEF Inv, t_t_to_assemble, TypeInvariant, States

LEMMA ToWritePreservesInv == Inv /\ t_t_to_write => Inv'
BY ConstantsDistinct DEF Inv, t_t_to_write, TypeInvariant, States

LEMMA DonePreservesInv == Inv /\ t_t_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_done, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY StartPreservesInv, NoBlueprintPreservesInv, ToMermaidPreservesInv, ToTablesPreservesInv, ToAssemblePreservesInv, ToWritePreservesInv, DonePreservesInv DEF Next

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