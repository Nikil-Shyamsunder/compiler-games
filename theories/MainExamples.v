From Stdlib Require Import List Arith Lia.
From VerifPerf Require Import Syntax Semantics Inlining InliningProof BackwardSim
  InliningWellformed InliningCorrectness Main.
Import ListNotations.

Module MainExamples.
  Definition source : program :=
    [mk_function []
       [Icall 1 [] 0 1; Icall 1 [] 0 2; Icall 2 [] 0 3; Iret 0];
     mk_function [] [Iret 0];
     mk_function [] [Icall 1 [] 0 1; Iret 0]].

  (** Calling function 2 is excluded because it is not initially a leaf. *)
  Example extracts_only_valid_leaf_sites :
    candidate_sites source =
      [mk_callsite 0 0; mk_callsite 0 1; mk_callsite 2 0].
  Proof. vm_compute. reflexivity. Qed.

  (** Inlining occupies shared resource 0 with latency equal to its load;
      leaving the call intact costs 2 on a private resource. *)
  Definition uses (i : nat) (bi : bool) (r : nat) : bool :=
    if bi then Nat.eqb r 0 else Nat.eqb r (S i).
  Definition slope (r : nat) : nat := if Nat.eqb r 0 then 1 else 0.
  Definition offset (r : nat) : nat := if Nat.eqb r 0 then 0 else 2.

  Definition selected (initial : profile) : profile :=
    select_profile 3 4 uses slope offset initial.

  Example selects_an_improving_inline :
    map (selected (fun _ => false)) [0; 1; 2] = [false; false; true].
  Proof. vm_compute. reflexivity. Qed.

  Example retracts_a_congested_inline :
    map (selected (fun _ => true)) [0; 1; 2] = [true; true; false].
  Proof. vm_compute. reflexivity. Qed.

  Example compiles_selected_inline_using_the_actual_pass :
    pass source 4 uses slope offset
      (fun _ => false) = inline source (mk_callsite 2 0).
  Proof. vm_compute. reflexivity. Qed.

  (** Starting from all-inline does not leave the retracted call inlined:
      emission starts from [source] and only applies the two selected passes. *)
  Example rebuilds_after_retraction :
    pass source 4 uses slope offset
      (fun _ => true) =
    match inline source (mk_callsite 0 0) with
    | Some q => inline q (mk_callsite 0 1)
    | None => None
    end.
  Proof. vm_compute. reflexivity. Qed.

  Example rejects_invalid_selected_sites :
    compile_profile source [mk_callsite 0 2] (fun _ => true) = None.
  Proof. vm_compute. reflexivity. Qed.

  Example leaves_unselected_sites_intact :
    compile_profile source (candidate_sites source) (fun _ => false) = Some source.
  Proof. vm_compute. reflexivity. Qed.
End MainExamples.

Module ReturnExamples.
  Definition caller := mk_function []
    [Icall 1 [] 0 1; Icall 1 [] 1 2; Iop Oadd [0; 1] 0 3; Iret 0].
  Definition callee := mk_function [] [Iop (Oconst 7) [] 0 1; Iret 0].
  Definition source := [caller; callee].

  Lemma source_wf : wf_program source.
  Proof.
    intros fi f pc instr Hf Hcode.
    destruct fi as [|[|fi]]; simpl in Hf;
      try rewrite nth_error_nil in Hf; try discriminate;
      inversion Hf; subst f.
    all: destruct pc as [|[|[|[|pc]]]]; simpl in Hcode;
      try rewrite nth_error_nil in Hcode; try discriminate;
      inversion Hcode; subst instr; unfold wf_instr; split.
    all: try exact I.
    all: try (eexists; split; [reflexivity|eexists; reflexivity]).
    all: intros next Hnext; simpl in Hnext; try contradiction;
      destruct Hnext as [<-|[]]; eexists; reflexivity.
  Qed.

  Lemma source_entrypoints : wf_entrypoints source.
  Proof.
    intros fi f Hf. destruct fi as [|[|fi]]; simpl in Hf;
      try rewrite nth_error_nil in Hf; try discriminate;
      inversion Hf; subst f; eexists; reflexivity.
  Qed.

  Lemma source_returns_fourteen : returns source 14.
  Proof.
    eexists (State [] caller 0 (init_regs [] [])), _.
    split; [exists caller; split; reflexivity|]. split.
    - eapply star_step; [eapply exec_Icall; reflexivity|].
      eapply star_step; [eapply exec_Iop; reflexivity|].
      eapply star_step; [eapply exec_Iret; reflexivity|].
      eapply star_step; [eapply exec_Icall; reflexivity|].
      eapply star_step; [eapply exec_Iop; reflexivity|].
      eapply star_step; [eapply exec_Iret; reflexivity|].
      eapply star_step; [eapply exec_Iop; reflexivity|constructor].
    - eexists; eexists; eexists; eexists. repeat split; reflexivity.
  Qed.

  (** Both calls may be inlined independently. Every chosen profile still
      returns 14, and the reverse direction excludes any new return value. *)
  Example pass_preserves_returns initial :
    exists q,
      pass source 0 (fun _ _ _ => false) (fun _ => 0) (fun _ => 0) initial = Some q /\
      returns q 14 /\ (forall v, returns q v -> returns source v).
  Proof.
    destruct (pass_correct source 0 (fun _ _ _ => false) (fun _ => 0)
      (fun _ => 0) initial source_wf source_entrypoints) as [q [Hpass Hsem]].
    exists q. split; [assumption|]. split.
    - apply (proj1 (return_values_preserved source q Hsem 14)).
      exact source_returns_fourteen.
    - intros v Hv. apply (proj2 (return_values_preserved source q Hsem v)). exact Hv.
  Qed.
End ReturnExamples.

Module IntermediateCostExamples.
  Definition uses (i : nat) (bi : bool) (r : nat) :=
    if Nat.eqb i 0 then Nat.eqb r (if bi then 1 else 0) else Nat.eqb r 1.
  Definition slope r := if Nat.eqb r 0 then 0 else 2.
  Definition offset r := if Nat.eqb r 0 then 5 else 0.
  Definition initial : profile := fun _ => false.
  Definition after_move := upd initial 0 true.

  Lemma accepted_move : CongestionGame.step 2 2 uses slope offset initial after_move.
  Proof. constructor. split; [lia|]. vm_compute. lia. Qed.

  Example decreasing_potential_does_not_require_decreasing_cost :
    SocialCost 2 2 uses slope offset initial = 7 /\
    SocialCost 2 2 uses slope offset after_move = 8 /\
    Phi 2 2 uses slope offset initial = 7 /\
    Phi 2 2 uses slope offset after_move = 6.
  Proof. vm_compute. repeat split; reflexivity. Qed.

  Example intermediate_bound_after_accepted_move :
    SocialCost 2 2 uses slope offset after_move <=
      2 * (2 * (2 * 2 * 2 + 5 * 2) - 1).
  Proof.
    eapply intermediate_cost_bound_by_global_params with (s := initial).
    - intros r Hr. unfold slope. destruct (Nat.eqb r 0); lia.
    - intros r Hr. unfold offset. destruct (Nat.eqb r 0); lia.
    - eapply steps_cons; [exact accepted_move|constructor].
  Qed.
End IntermediateCostExamples.

Module CommonRelationExamples.
  Definition body := mk_function [] [Iop (Oconst 7) [] 0 1; Iret 0].
  Definition program_with_return := [body].
  Definition start := State [] body 0 empty_regs.
  Definition finish := State [] body 1 (update empty_regs 0 7).

  Lemma program_wf : wf_program program_with_return.
  Proof.
    intros fi f pc instr Hf Hcode.
    destruct fi; simpl in Hf; try rewrite nth_error_nil in Hf; try discriminate.
    inversion Hf; subst f.
    destruct pc as [|[|pc]]; simpl in Hcode;
      try rewrite nth_error_nil in Hcode; try discriminate;
      inversion Hcode; subst instr; split; try exact I.
    all: intros next Hnext; simpl in Hnext; try contradiction;
      destruct Hnext as [<-|[]]; eexists; reflexivity.
  Qed.

  Lemma program_entrypoints : wf_entrypoints program_with_return.
  Proof.
    intros fi f Hf. destruct fi; simpl in Hf;
      try rewrite nth_error_nil in Hf; try discriminate.
    inversion Hf; subst f. eexists; reflexivity.
  Qed.

  Lemma identity_bisimulation : bisimulation program_with_return program_with_return.
  Proof.
    constructor.
    - apply inline_trace_forward_sim; [constructor|exact program_wf|exact program_entrypoints].
    - apply inline_trace_backward_sim; [constructor|exact program_wf|exact program_entrypoints].
  Qed.

  Lemma final_result : final_state finish 7.
  Proof. exists body, 1, (update empty_regs 0 7), 0. repeat split; reflexivity. Qed.

  Lemma pending_step : Semantics.step program_with_return start finish.
  Proof. eapply exec_Iop; reflexivity. Qed.

  (** The very same relation covers a source that has returned while the
      target still has one administrative step left to perform. *)
  Lemma pending_match : sim_rel program_with_return program_with_return 1 finish start.
  Proof.
    exists finish. split.
    - eapply starN_step; [exact pending_step|constructor].
    - split; [constructor|]. split; [eexists; reflexivity|].
      split; [exists 0; reflexivity|constructor].
  Qed.

  Example forward_final_allows_cleanup :
    exists target_final,
      reachable program_with_return start target_final /\ final_state target_final 7.
  Proof.
    destruct (fsim_final _ _ (bisim_forward _ _ identity_bisimulation)
      finish start 1 7 pending_match final_result) as [target_final [Hreach [Hfinal Hrel]]].
    exists target_final. auto.
  Qed.

  Example backward_pending_step_decreases_rank :
    exists m', sim_rel program_with_return program_with_return m' finish finish /\ m' < 1.
  Proof.
    destruct (bsim_step _ _ (bisim_backward _ _ identity_bisimulation)
      finish start 1 finish pending_match pending_step)
      as [[source' [m' [Hsource Hmatch]]]|[m' [Hmatch Hlt]]].
    - exfalso. inversion Hsource; subst; eapply final_no_step; eauto using final_result.
    - exists m'. auto.
  Qed.
End CommonRelationExamples.
