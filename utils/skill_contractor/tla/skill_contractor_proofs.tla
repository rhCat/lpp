--------------------------- MODULE skill_contractor_proofs ---------------------------
(*
 * L++ Blueprint: Skill Contractor
 * Version: 1.7.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_planning, STATE_executing, STATE_parsing, STATE_correcting, STATE_stepping, STATE_validating, STATE_eval_interactive, STATE_evaluating, STATE_refining, STATE_reviewing, STATE_complete, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_planning
    /\ STATE_idle /= STATE_executing
    /\ STATE_idle /= STATE_parsing
    /\ STATE_idle /= STATE_correcting
    /\ STATE_idle /= STATE_stepping
    /\ STATE_idle /= STATE_validating
    /\ STATE_idle /= STATE_eval_interactive
    /\ STATE_idle /= STATE_evaluating
    /\ STATE_idle /= STATE_refining
    /\ STATE_idle /= STATE_reviewing
    /\ STATE_idle /= STATE_complete
    /\ STATE_idle /= STATE_error
    /\ STATE_planning /= STATE_executing
    /\ STATE_planning /= STATE_parsing
    /\ STATE_planning /= STATE_correcting
    /\ STATE_planning /= STATE_stepping
    /\ STATE_planning /= STATE_validating
    /\ STATE_planning /= STATE_eval_interactive
    /\ STATE_planning /= STATE_evaluating
    /\ STATE_planning /= STATE_refining
    /\ STATE_planning /= STATE_reviewing
    /\ STATE_planning /= STATE_complete
    /\ STATE_planning /= STATE_error
    /\ STATE_executing /= STATE_parsing
    /\ STATE_executing /= STATE_correcting
    /\ STATE_executing /= STATE_stepping
    /\ STATE_executing /= STATE_validating
    /\ STATE_executing /= STATE_eval_interactive
    /\ STATE_executing /= STATE_evaluating
    /\ STATE_executing /= STATE_refining
    /\ STATE_executing /= STATE_reviewing
    /\ STATE_executing /= STATE_complete
    /\ STATE_executing /= STATE_error
    /\ STATE_parsing /= STATE_correcting
    /\ STATE_parsing /= STATE_stepping
    /\ STATE_parsing /= STATE_validating
    /\ STATE_parsing /= STATE_eval_interactive
    /\ STATE_parsing /= STATE_evaluating
    /\ STATE_parsing /= STATE_refining
    /\ STATE_parsing /= STATE_reviewing
    /\ STATE_parsing /= STATE_complete
    /\ STATE_parsing /= STATE_error
    /\ STATE_correcting /= STATE_stepping
    /\ STATE_correcting /= STATE_validating
    /\ STATE_correcting /= STATE_eval_interactive
    /\ STATE_correcting /= STATE_evaluating
    /\ STATE_correcting /= STATE_refining
    /\ STATE_correcting /= STATE_reviewing
    /\ STATE_correcting /= STATE_complete
    /\ STATE_correcting /= STATE_error
    /\ STATE_stepping /= STATE_validating
    /\ STATE_stepping /= STATE_eval_interactive
    /\ STATE_stepping /= STATE_evaluating
    /\ STATE_stepping /= STATE_refining
    /\ STATE_stepping /= STATE_reviewing
    /\ STATE_stepping /= STATE_complete
    /\ STATE_stepping /= STATE_error
    /\ STATE_validating /= STATE_eval_interactive
    /\ STATE_validating /= STATE_evaluating
    /\ STATE_validating /= STATE_refining
    /\ STATE_validating /= STATE_reviewing
    /\ STATE_validating /= STATE_complete
    /\ STATE_validating /= STATE_error
    /\ STATE_eval_interactive /= STATE_evaluating
    /\ STATE_eval_interactive /= STATE_refining
    /\ STATE_eval_interactive /= STATE_reviewing
    /\ STATE_eval_interactive /= STATE_complete
    /\ STATE_eval_interactive /= STATE_error
    /\ STATE_evaluating /= STATE_refining
    /\ STATE_evaluating /= STATE_reviewing
    /\ STATE_evaluating /= STATE_complete
    /\ STATE_evaluating /= STATE_error
    /\ STATE_refining /= STATE_reviewing
    /\ STATE_refining /= STATE_complete
    /\ STATE_refining /= STATE_error
    /\ STATE_reviewing /= STATE_complete
    /\ STATE_reviewing /= STATE_error
    /\ STATE_complete /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_planning, STATE_executing, STATE_parsing, STATE_correcting, STATE_stepping, STATE_validating, STATE_eval_interactive, STATE_evaluating, STATE_refining, STATE_reviewing, STATE_complete, STATE_error}
TerminalStates == {STATE_complete}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_start *)
t_t_start ==
    /\ state = STATE_idle
    /\ state' = STATE_idle

(* Transition: t_submit_target *)
t_t_submit_target ==
    /\ state = STATE_idle
    /\ state' = STATE_planning

(* Transition: t_plan_ready *)
t_t_plan_ready ==
    /\ state = STATE_planning
    /\ state' = STATE_executing

(* Transition: t_plan_error *)
t_t_plan_error ==
    /\ state = STATE_planning
    /\ state' = STATE_error

(* Transition: t_exec_to_parse *)
t_t_exec_to_parse ==
    /\ state = STATE_executing
    /\ state' = STATE_parsing

(* Transition: t_exec_error *)
t_t_exec_error ==
    /\ state = STATE_executing
    /\ state' = STATE_error

(* Transition: t_parse_ok_correct_step *)
t_t_parse_ok_correct_step ==
    /\ state = STATE_parsing
    /\ state' = STATE_correcting

(* Transition: t_parse_ok_step *)
t_t_parse_ok_step ==
    /\ state = STATE_parsing
    /\ state' = STATE_stepping

(* Transition: t_parse_ok_correct_blueprint_validate *)
t_t_parse_ok_correct_blueprint_validate ==
    /\ state = STATE_parsing
    /\ state' = STATE_correcting

(* Transition: t_parse_ok_blueprint_validate *)
t_t_parse_ok_blueprint_validate ==
    /\ state = STATE_parsing
    /\ state' = STATE_validating

(* Transition: t_parse_ok_correct_impl_validate *)
t_t_parse_ok_correct_impl_validate ==
    /\ state = STATE_parsing
    /\ state' = STATE_correcting

(* Transition: t_parse_ok_impl_validate *)
t_t_parse_ok_impl_validate ==
    /\ state = STATE_parsing
    /\ state' = STATE_validating

(* Transition: t_parse_ok_correct_eval *)
t_t_parse_ok_correct_eval ==
    /\ state = STATE_parsing
    /\ state' = STATE_correcting

(* Transition: t_parse_ok_eval *)
t_t_parse_ok_eval ==
    /\ state = STATE_parsing
    /\ state' = STATE_evaluating

(* Transition: t_correct_to_step *)
t_t_correct_to_step ==
    /\ state = STATE_correcting
    /\ state' = STATE_stepping

(* Transition: t_correct_to_validate_blueprint *)
t_t_correct_to_validate_blueprint ==
    /\ state = STATE_correcting
    /\ state' = STATE_validating

(* Transition: t_correct_to_validate_impl *)
t_t_correct_to_validate_impl ==
    /\ state = STATE_correcting
    /\ state' = STATE_validating

(* Transition: t_correct_to_eval *)
t_t_correct_to_eval ==
    /\ state = STATE_correcting
    /\ state' = STATE_evaluating

(* Transition: t_parse_fail_retry *)
t_t_parse_fail_retry ==
    /\ state = STATE_parsing
    /\ state' = STATE_executing

(* Transition: t_parse_fail_max *)
t_t_parse_fail_max ==
    /\ state = STATE_parsing
    /\ state' = STATE_error

(* Transition: t_step_exec *)
t_t_step_exec ==
    /\ state = STATE_stepping
    /\ state' = STATE_executing

(* Transition: t_step_validate_blueprint *)
t_t_step_validate_blueprint ==
    /\ state = STATE_stepping
    /\ state' = STATE_validating

(* Transition: t_step_validate_impl *)
t_t_step_validate_impl ==
    /\ state = STATE_stepping
    /\ state' = STATE_validating

(* Transition: t_step_eval *)
t_t_step_eval ==
    /\ state = STATE_stepping
    /\ state' = STATE_evaluating

(* Transition: t_step_error *)
t_t_step_error ==
    /\ state = STATE_stepping
    /\ state' = STATE_error

(* Transition: t_validate_blueprint_pass *)
t_t_validate_blueprint_pass ==
    /\ state = STATE_validating
    /\ state' = STATE_planning

(* Transition: t_validate_impl_pass *)
t_t_validate_impl_pass ==
    /\ state = STATE_validating
    /\ state' = STATE_eval_interactive

(* Transition: t_eval_interactive_pass *)
t_t_eval_interactive_pass ==
    /\ state = STATE_eval_interactive
    /\ state' = STATE_evaluating

(* Transition: t_eval_interactive_fail *)
t_t_eval_interactive_fail ==
    /\ state = STATE_eval_interactive
    /\ state' = STATE_refining

(* Transition: t_eval_interactive_maxiter *)
t_t_eval_interactive_maxiter ==
    /\ state = STATE_eval_interactive
    /\ state' = STATE_evaluating

(* Transition: t_eval_interactive_error *)
t_t_eval_interactive_error ==
    /\ state = STATE_eval_interactive
    /\ state' = STATE_error

(* Transition: t_validate_blueprint_fail *)
t_t_validate_blueprint_fail ==
    /\ state = STATE_validating
    /\ state' = STATE_refining

(* Transition: t_validate_impl_fail *)
t_t_validate_impl_fail ==
    /\ state = STATE_validating
    /\ state' = STATE_refining

(* Transition: t_validate_fail_maxiter *)
t_t_validate_fail_maxiter ==
    /\ state = STATE_validating
    /\ state' = STATE_evaluating

(* Transition: t_validate_error *)
t_t_validate_error ==
    /\ state = STATE_validating
    /\ state' = STATE_error

(* Transition: t_eval_satisfied *)
t_t_eval_satisfied ==
    /\ state = STATE_evaluating
    /\ state' = STATE_complete

(* Transition: t_eval_lpp_fail *)
t_t_eval_lpp_fail ==
    /\ state = STATE_evaluating
    /\ state' = STATE_refining

(* Transition: t_eval_refine *)
t_t_eval_refine ==
    /\ state = STATE_evaluating
    /\ state' = STATE_refining

(* Transition: t_eval_maxiter *)
t_t_eval_maxiter ==
    /\ state = STATE_evaluating
    /\ state' = STATE_complete

(* Transition: t_eval_lpp_hard_fail *)
t_t_eval_lpp_hard_fail ==
    /\ state = STATE_evaluating
    /\ state' = STATE_error

(* Transition: t_eval_error *)
t_t_eval_error ==
    /\ state = STATE_evaluating
    /\ state' = STATE_error

(* Transition: t_refine_plan *)
t_t_refine_plan ==
    /\ state = STATE_refining
    /\ state' = STATE_planning

(* Transition: t_refine_error *)
t_t_refine_error ==
    /\ state = STATE_refining
    /\ state' = STATE_error

(* Transition: t_error_step_retry *)
t_t_error_step_retry ==
    /\ state = STATE_error
    /\ state' = STATE_executing

(* Transition: t_error_no_plan *)
t_t_error_no_plan ==
    /\ state = STATE_error
    /\ state' = STATE_refining

(* Transition: t_error_no_plan_maxiter *)
t_t_error_no_plan_maxiter ==
    /\ state = STATE_error
    /\ state' = STATE_complete

(* Transition: t_error_to_review *)
t_t_error_to_review ==
    /\ state = STATE_error
    /\ state' = STATE_reviewing

(* Transition: t_error_maxiter_complete *)
t_t_error_maxiter_complete ==
    /\ state = STATE_error
    /\ state' = STATE_complete

(* Transition: t_review_too_many_fails *)
t_t_review_too_many_fails ==
    /\ state = STATE_reviewing
    /\ state' = STATE_evaluating

(* Transition: t_review_skip *)
t_t_review_skip ==
    /\ state = STATE_reviewing
    /\ state' = STATE_stepping

(* Transition: t_review_skip_eval *)
t_t_review_skip_eval ==
    /\ state = STATE_reviewing
    /\ state' = STATE_evaluating

(* Transition: t_review_replan *)
t_t_review_replan ==
    /\ state = STATE_reviewing
    /\ state' = STATE_refining

(* Transition: t_review_replan_maxiter *)
t_t_review_replan_maxiter ==
    /\ state = STATE_reviewing
    /\ state' = STATE_evaluating

(* Transition: t_review_invalid_skip *)
t_t_review_invalid_skip ==
    /\ state = STATE_reviewing
    /\ state' = STATE_stepping

(* Transition: t_review_invalid_eval *)
t_t_review_invalid_eval ==
    /\ state = STATE_reviewing
    /\ state' = STATE_evaluating

(* Transition: t_review_no_plan *)
t_t_review_no_plan ==
    /\ state = STATE_reviewing
    /\ state' = STATE_refining

(* Transition: t_review_no_plan_maxiter *)
t_t_review_no_plan_maxiter ==
    /\ state = STATE_reviewing
    /\ state' = STATE_complete

(* Transition: t_recover *)
t_t_recover ==
    /\ state = STATE_error
    /\ state' = STATE_idle

(* Transition: t_reset *)
t_t_reset ==
    /\ TRUE  \* Global transition
    /\ state' = STATE_idle

Next ==
    \/ t_t_start
    \/ t_t_submit_target
    \/ t_t_plan_ready
    \/ t_t_plan_error
    \/ t_t_exec_to_parse
    \/ t_t_exec_error
    \/ t_t_parse_ok_correct_step
    \/ t_t_parse_ok_step
    \/ t_t_parse_ok_correct_blueprint_validate
    \/ t_t_parse_ok_blueprint_validate
    \/ t_t_parse_ok_correct_impl_validate
    \/ t_t_parse_ok_impl_validate
    \/ t_t_parse_ok_correct_eval
    \/ t_t_parse_ok_eval
    \/ t_t_correct_to_step
    \/ t_t_correct_to_validate_blueprint
    \/ t_t_correct_to_validate_impl
    \/ t_t_correct_to_eval
    \/ t_t_parse_fail_retry
    \/ t_t_parse_fail_max
    \/ t_t_step_exec
    \/ t_t_step_validate_blueprint
    \/ t_t_step_validate_impl
    \/ t_t_step_eval
    \/ t_t_step_error
    \/ t_t_validate_blueprint_pass
    \/ t_t_validate_impl_pass
    \/ t_t_eval_interactive_pass
    \/ t_t_eval_interactive_fail
    \/ t_t_eval_interactive_maxiter
    \/ t_t_eval_interactive_error
    \/ t_t_validate_blueprint_fail
    \/ t_t_validate_impl_fail
    \/ t_t_validate_fail_maxiter
    \/ t_t_validate_error
    \/ t_t_eval_satisfied
    \/ t_t_eval_lpp_fail
    \/ t_t_eval_refine
    \/ t_t_eval_maxiter
    \/ t_t_eval_lpp_hard_fail
    \/ t_t_eval_error
    \/ t_t_refine_plan
    \/ t_t_refine_error
    \/ t_t_error_step_retry
    \/ t_t_error_no_plan
    \/ t_t_error_no_plan_maxiter
    \/ t_t_error_to_review
    \/ t_t_error_maxiter_complete
    \/ t_t_review_too_many_fails
    \/ t_t_review_skip
    \/ t_t_review_skip_eval
    \/ t_t_review_replan
    \/ t_t_review_replan_maxiter
    \/ t_t_review_invalid_skip
    \/ t_t_review_invalid_eval
    \/ t_t_review_no_plan
    \/ t_t_review_no_plan_maxiter
    \/ t_t_recover
    \/ t_t_reset

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA StartPreservesInv == Inv /\ t_t_start => Inv'
BY ConstantsDistinct DEF Inv, t_t_start, TypeInvariant, States

LEMMA SubmitargetPreservesInv == Inv /\ t_t_submit_target => Inv'
BY ConstantsDistinct DEF Inv, t_t_submit_target, TypeInvariant, States

LEMMA PlanReadyPreservesInv == Inv /\ t_t_plan_ready => Inv'
BY ConstantsDistinct DEF Inv, t_t_plan_ready, TypeInvariant, States

LEMMA PlanErrorPreservesInv == Inv /\ t_t_plan_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_plan_error, TypeInvariant, States

LEMMA ExecToParsePreservesInv == Inv /\ t_t_exec_to_parse => Inv'
BY ConstantsDistinct DEF Inv, t_t_exec_to_parse, TypeInvariant, States

LEMMA ExecErrorPreservesInv == Inv /\ t_t_exec_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_exec_error, TypeInvariant, States

LEMMA ParseOkCorrecstepPreservesInv == Inv /\ t_t_parse_ok_correct_step => Inv'
BY ConstantsDistinct DEF Inv, t_t_parse_ok_correct_step, TypeInvariant, States

LEMMA ParseOkStepPreservesInv == Inv /\ t_t_parse_ok_step => Inv'
BY ConstantsDistinct DEF Inv, t_t_parse_ok_step, TypeInvariant, States

LEMMA ParseOkCorrecblueprinvalidatePreservesInv == Inv /\ t_t_parse_ok_correct_blueprint_validate => Inv'
BY ConstantsDistinct DEF Inv, t_t_parse_ok_correct_blueprint_validate, TypeInvariant, States

LEMMA ParseOkBlueprinvalidatePreservesInv == Inv /\ t_t_parse_ok_blueprint_validate => Inv'
BY ConstantsDistinct DEF Inv, t_t_parse_ok_blueprint_validate, TypeInvariant, States

LEMMA ParseOkCorrecimplValidatePreservesInv == Inv /\ t_t_parse_ok_correct_impl_validate => Inv'
BY ConstantsDistinct DEF Inv, t_t_parse_ok_correct_impl_validate, TypeInvariant, States

LEMMA ParseOkImplValidatePreservesInv == Inv /\ t_t_parse_ok_impl_validate => Inv'
BY ConstantsDistinct DEF Inv, t_t_parse_ok_impl_validate, TypeInvariant, States

LEMMA ParseOkCorrecevalPreservesInv == Inv /\ t_t_parse_ok_correct_eval => Inv'
BY ConstantsDistinct DEF Inv, t_t_parse_ok_correct_eval, TypeInvariant, States

LEMMA ParseOkEvalPreservesInv == Inv /\ t_t_parse_ok_eval => Inv'
BY ConstantsDistinct DEF Inv, t_t_parse_ok_eval, TypeInvariant, States

LEMMA CorrectoStepPreservesInv == Inv /\ t_t_correct_to_step => Inv'
BY ConstantsDistinct DEF Inv, t_t_correct_to_step, TypeInvariant, States

LEMMA CorrectoValidateBlueprintPreservesInv == Inv /\ t_t_correct_to_validate_blueprint => Inv'
BY ConstantsDistinct DEF Inv, t_t_correct_to_validate_blueprint, TypeInvariant, States

LEMMA CorrectoValidateImplPreservesInv == Inv /\ t_t_correct_to_validate_impl => Inv'
BY ConstantsDistinct DEF Inv, t_t_correct_to_validate_impl, TypeInvariant, States

LEMMA CorrectoEvalPreservesInv == Inv /\ t_t_correct_to_eval => Inv'
BY ConstantsDistinct DEF Inv, t_t_correct_to_eval, TypeInvariant, States

LEMMA ParseFailRetryPreservesInv == Inv /\ t_t_parse_fail_retry => Inv'
BY ConstantsDistinct DEF Inv, t_t_parse_fail_retry, TypeInvariant, States

LEMMA ParseFailMaxPreservesInv == Inv /\ t_t_parse_fail_max => Inv'
BY ConstantsDistinct DEF Inv, t_t_parse_fail_max, TypeInvariant, States

LEMMA StepExecPreservesInv == Inv /\ t_t_step_exec => Inv'
BY ConstantsDistinct DEF Inv, t_t_step_exec, TypeInvariant, States

LEMMA StepValidateBlueprintPreservesInv == Inv /\ t_t_step_validate_blueprint => Inv'
BY ConstantsDistinct DEF Inv, t_t_step_validate_blueprint, TypeInvariant, States

LEMMA StepValidateImplPreservesInv == Inv /\ t_t_step_validate_impl => Inv'
BY ConstantsDistinct DEF Inv, t_t_step_validate_impl, TypeInvariant, States

LEMMA StepEvalPreservesInv == Inv /\ t_t_step_eval => Inv'
BY ConstantsDistinct DEF Inv, t_t_step_eval, TypeInvariant, States

LEMMA StepErrorPreservesInv == Inv /\ t_t_step_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_step_error, TypeInvariant, States

LEMMA ValidateBlueprinpassPreservesInv == Inv /\ t_t_validate_blueprint_pass => Inv'
BY ConstantsDistinct DEF Inv, t_t_validate_blueprint_pass, TypeInvariant, States

LEMMA ValidateImplPassPreservesInv == Inv /\ t_t_validate_impl_pass => Inv'
BY ConstantsDistinct DEF Inv, t_t_validate_impl_pass, TypeInvariant, States

LEMMA EvalInteractivePassPreservesInv == Inv /\ t_t_eval_interactive_pass => Inv'
BY ConstantsDistinct DEF Inv, t_t_eval_interactive_pass, TypeInvariant, States

LEMMA EvalInteractiveFailPreservesInv == Inv /\ t_t_eval_interactive_fail => Inv'
BY ConstantsDistinct DEF Inv, t_t_eval_interactive_fail, TypeInvariant, States

LEMMA EvalInteractiveMaxiterPreservesInv == Inv /\ t_t_eval_interactive_maxiter => Inv'
BY ConstantsDistinct DEF Inv, t_t_eval_interactive_maxiter, TypeInvariant, States

LEMMA EvalInteractiveErrorPreservesInv == Inv /\ t_t_eval_interactive_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_eval_interactive_error, TypeInvariant, States

LEMMA ValidateBlueprinfailPreservesInv == Inv /\ t_t_validate_blueprint_fail => Inv'
BY ConstantsDistinct DEF Inv, t_t_validate_blueprint_fail, TypeInvariant, States

LEMMA ValidateImplFailPreservesInv == Inv /\ t_t_validate_impl_fail => Inv'
BY ConstantsDistinct DEF Inv, t_t_validate_impl_fail, TypeInvariant, States

LEMMA ValidateFailMaxiterPreservesInv == Inv /\ t_t_validate_fail_maxiter => Inv'
BY ConstantsDistinct DEF Inv, t_t_validate_fail_maxiter, TypeInvariant, States

LEMMA ValidateErrorPreservesInv == Inv /\ t_t_validate_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_validate_error, TypeInvariant, States

LEMMA EvalSatisfiedPreservesInv == Inv /\ t_t_eval_satisfied => Inv'
BY ConstantsDistinct DEF Inv, t_t_eval_satisfied, TypeInvariant, States

LEMMA EvalLppFailPreservesInv == Inv /\ t_t_eval_lpp_fail => Inv'
BY ConstantsDistinct DEF Inv, t_t_eval_lpp_fail, TypeInvariant, States

LEMMA EvalRefinePreservesInv == Inv /\ t_t_eval_refine => Inv'
BY ConstantsDistinct DEF Inv, t_t_eval_refine, TypeInvariant, States

LEMMA EvalMaxiterPreservesInv == Inv /\ t_t_eval_maxiter => Inv'
BY ConstantsDistinct DEF Inv, t_t_eval_maxiter, TypeInvariant, States

LEMMA EvalLppHardFailPreservesInv == Inv /\ t_t_eval_lpp_hard_fail => Inv'
BY ConstantsDistinct DEF Inv, t_t_eval_lpp_hard_fail, TypeInvariant, States

LEMMA EvalErrorPreservesInv == Inv /\ t_t_eval_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_eval_error, TypeInvariant, States

LEMMA RefinePlanPreservesInv == Inv /\ t_t_refine_plan => Inv'
BY ConstantsDistinct DEF Inv, t_t_refine_plan, TypeInvariant, States

LEMMA RefineErrorPreservesInv == Inv /\ t_t_refine_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_refine_error, TypeInvariant, States

LEMMA ErrorStepRetryPreservesInv == Inv /\ t_t_error_step_retry => Inv'
BY ConstantsDistinct DEF Inv, t_t_error_step_retry, TypeInvariant, States

LEMMA ErrorNoPlanPreservesInv == Inv /\ t_t_error_no_plan => Inv'
BY ConstantsDistinct DEF Inv, t_t_error_no_plan, TypeInvariant, States

LEMMA ErrorNoPlanMaxiterPreservesInv == Inv /\ t_t_error_no_plan_maxiter => Inv'
BY ConstantsDistinct DEF Inv, t_t_error_no_plan_maxiter, TypeInvariant, States

LEMMA ErrorToReviewPreservesInv == Inv /\ t_t_error_to_review => Inv'
BY ConstantsDistinct DEF Inv, t_t_error_to_review, TypeInvariant, States

LEMMA ErrorMaxiterCompletePreservesInv == Inv /\ t_t_error_maxiter_complete => Inv'
BY ConstantsDistinct DEF Inv, t_t_error_maxiter_complete, TypeInvariant, States

LEMMA ReviewTooManyFailsPreservesInv == Inv /\ t_t_review_too_many_fails => Inv'
BY ConstantsDistinct DEF Inv, t_t_review_too_many_fails, TypeInvariant, States

LEMMA ReviewSkipPreservesInv == Inv /\ t_t_review_skip => Inv'
BY ConstantsDistinct DEF Inv, t_t_review_skip, TypeInvariant, States

LEMMA ReviewSkipEvalPreservesInv == Inv /\ t_t_review_skip_eval => Inv'
BY ConstantsDistinct DEF Inv, t_t_review_skip_eval, TypeInvariant, States

LEMMA ReviewReplanPreservesInv == Inv /\ t_t_review_replan => Inv'
BY ConstantsDistinct DEF Inv, t_t_review_replan, TypeInvariant, States

LEMMA ReviewReplanMaxiterPreservesInv == Inv /\ t_t_review_replan_maxiter => Inv'
BY ConstantsDistinct DEF Inv, t_t_review_replan_maxiter, TypeInvariant, States

LEMMA ReviewInvalidSkipPreservesInv == Inv /\ t_t_review_invalid_skip => Inv'
BY ConstantsDistinct DEF Inv, t_t_review_invalid_skip, TypeInvariant, States

LEMMA ReviewInvalidEvalPreservesInv == Inv /\ t_t_review_invalid_eval => Inv'
BY ConstantsDistinct DEF Inv, t_t_review_invalid_eval, TypeInvariant, States

LEMMA ReviewNoPlanPreservesInv == Inv /\ t_t_review_no_plan => Inv'
BY ConstantsDistinct DEF Inv, t_t_review_no_plan, TypeInvariant, States

LEMMA ReviewNoPlanMaxiterPreservesInv == Inv /\ t_t_review_no_plan_maxiter => Inv'
BY ConstantsDistinct DEF Inv, t_t_review_no_plan_maxiter, TypeInvariant, States

LEMMA RecoverPreservesInv == Inv /\ t_t_recover => Inv'
BY ConstantsDistinct DEF Inv, t_t_recover, TypeInvariant, States

LEMMA ResetPreservesInv == Inv /\ t_t_reset => Inv'
BY ConstantsDistinct DEF Inv, t_t_reset, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY StartPreservesInv, SubmitargetPreservesInv, PlanReadyPreservesInv, PlanErrorPreservesInv, ExecToParsePreservesInv, ExecErrorPreservesInv, ParseOkCorrecstepPreservesInv, ParseOkStepPreservesInv, ParseOkCorrecblueprinvalidatePreservesInv, ParseOkBlueprinvalidatePreservesInv, ParseOkCorrecimplValidatePreservesInv, ParseOkImplValidatePreservesInv, ParseOkCorrecevalPreservesInv, ParseOkEvalPreservesInv, CorrectoStepPreservesInv, CorrectoValidateBlueprintPreservesInv, CorrectoValidateImplPreservesInv, CorrectoEvalPreservesInv, ParseFailRetryPreservesInv, ParseFailMaxPreservesInv, StepExecPreservesInv, StepValidateBlueprintPreservesInv, StepValidateImplPreservesInv, StepEvalPreservesInv, StepErrorPreservesInv, ValidateBlueprinpassPreservesInv, ValidateImplPassPreservesInv, EvalInteractivePassPreservesInv, EvalInteractiveFailPreservesInv, EvalInteractiveMaxiterPreservesInv, EvalInteractiveErrorPreservesInv, ValidateBlueprinfailPreservesInv, ValidateImplFailPreservesInv, ValidateFailMaxiterPreservesInv, ValidateErrorPreservesInv, EvalSatisfiedPreservesInv, EvalLppFailPreservesInv, EvalRefinePreservesInv, EvalMaxiterPreservesInv, EvalLppHardFailPreservesInv, EvalErrorPreservesInv, RefinePlanPreservesInv, RefineErrorPreservesInv, ErrorStepRetryPreservesInv, ErrorNoPlanPreservesInv, ErrorNoPlanMaxiterPreservesInv, ErrorToReviewPreservesInv, ErrorMaxiterCompletePreservesInv, ReviewTooManyFailsPreservesInv, ReviewSkipPreservesInv, ReviewSkipEvalPreservesInv, ReviewReplanPreservesInv, ReviewReplanMaxiterPreservesInv, ReviewInvalidSkipPreservesInv, ReviewInvalidEvalPreservesInv, ReviewNoPlanPreservesInv, ReviewNoPlanMaxiterPreservesInv, RecoverPreservesInv, ResetPreservesInv DEF Next

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