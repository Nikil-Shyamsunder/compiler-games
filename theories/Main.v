(** * Verified inlining pass

    This file connects the executable inlining pass to its correctness and
    cost guarantees. A profile says which candidate callsites should be
    inlined. The compiler applies those decisions to the original program,
    and [compile_from_trace] shows that the resulting program was produced
    by a finite sequence of successful inline operations.

    We prove that any such sequence preserves execution in both directions,
    provided the source has valid control flow and function entrypoints
    (we don't jump to functions or statements that don't exist).
    The source and target use the same state relation, which is written to allow the
    target to finish the extra instructions introduced by inlining before
    reaching a matching state. The result is a weak bisimulation, from which
    we derive that the programs have the same possible top-level return
    values.

    The key results are [pass_correct] and [pass_cost]. The first says that
    the executable pass succeeds and produces a program bisimilar to the
    source. The second says that the selected profile has congestion cost
    at most five halves of the best cost over the same candidate callsites.
    We take [SocialCost] itself as the objective to optimize. We also bound
    the number of improving decisions before convergence and the cost after
    any number of accepted decisions, although the actual cost need not
    decrease at every decision. *)
From VerifPerf Require Export ProfileInlining CongestionGame.
From VerifPerf Require Import Syntax Semantics InliningProof BackwardSim
  InliningCorrectness.
From Stdlib Require Import List Wf_nat.

(** A forward simulation matches initial states and source steps with
    target execution, and preserves return values after finite target cleanup. *)
Record forward_sim (p q : program) : Prop := {
  fsim_initial : forall x, initial_state p x ->
    exists y m, initial_state q y /\ sim_rel p q m x y;
  fsim_step : forall x y m x', sim_rel p q m x y -> step p x x' ->
    exists y' m', plus (step q) y y' /\ sim_rel p q m' x' y';
  fsim_final : forall x y m v, sim_rel p q m x y -> final_state x v ->
    exists y', reachable q y y' /\ final_state y' v /\ sim_rel p q 0 x y'
}.

(** A backward simulation matches target steps with source execution or a
    smaller natural rank, so matching cannot stutter forever without progress. *)
Record backward_sim (p q : program) : Prop := {
  bsim_order_wf : well_founded lt;
  bsim_initial_exists : forall x, initial_state p x ->
    exists y, initial_state q y;
  bsim_initial : forall y, initial_state q y ->
    exists x m, initial_state p x /\ sim_rel p q m x y;
  bsim_step : forall x y m y', sim_rel p q m x y -> step q y y' ->
    (exists x' m', plus (step p) x x' /\ sim_rel p q m' x' y') \/
    (exists m', sim_rel p q m' x y' /\ m' < m);
  bsim_final : forall x y m v, sim_rel p q m x y ->
    final_state y v -> final_state x v;
  bsim_progress : forall x y m, sim_rel p q m x y ->
    ((exists v, final_state x v) \/ (exists x', step p x x')) ->
    (exists v, final_state y v) \/ (exists y', step q y y')
}.

(** A weak bisimulation uses the same relation for both execution directions
    and allows finite target cleanup before observing a source return.
    Note this is different from CompCert's forward-final clause, which requires an
    immediately final target state. *)
Record bisimulation (p q : program) : Prop := {
  bisim_forward : forward_sim p q;
  bisim_backward : backward_sim p q
}.

(** Any finite sequence of successful inlines from a well-formed source with
    valid entrypoints gives a forward simulation of the source by the
    resulting program. *)
Theorem inline_trace_forward_sim p q :
  inline_trace p q -> wf_program p -> wf_entrypoints p -> forward_sim p q.
Proof.
  intros Htrace Hwf Hentry. constructor.
  - intros x Hinit. destruct (trace_initial_match p q Htrace x Hinit)
      as [y [Hinity Hmatch]].
    exists y, 0. split; [assumption|]. exists y. split; [constructor|].
    split; [assumption|]. eapply initial_state_valid; eauto.
  - intros x y m x' Hmatch Hstep.
    destruct (trace_common_forward p q Hwf x y m Hmatch x' Hstep)
      as [y' [Hsteps Hmatch']]. exists y', 0. auto.
  - intros x y m v [sync [Hpending [Hmatch Hvalid]]] Hfinal.
    exists sync. split.
    + apply starN_to_star with (n := m). exact Hpending.
    + split; [eapply sync_rel_final; eauto|].
      exists sync. split; [constructor|]. split; assumption.
Qed.

(** Any finite sequence of successful inlines from a well-formed source with
    valid entrypoints gives a backward simulation of the resulting program
    by the source. *)
Theorem inline_trace_backward_sim p q :
  inline_trace p q -> wf_program p -> wf_entrypoints p -> backward_sim p q.
Proof.
  intros Htrace Hwf Hentry. constructor.
  - exact lt_wf.
  - intros x Hinit. destruct (trace_initial_match p q Htrace x Hinit)
      as [y [Hinity Hmatch]]. eauto.
  - intros y Hinity.
    assert (Hsource : exists x, initial_state p x).
    { destruct Htrace as [p|p cs q r Hinline Htail];
        [eauto|eapply inline_source_initial; eauto]. }
    destruct Hsource as [x Hinitx].
    destruct (trace_initial_match p q Htrace x Hinitx) as [y0 [Hinity0 Hmatch]].
    assert (y0 = y) by (eapply initial_state_unique; eauto). subst y0.
    exists x, 0. split; [assumption|]. exists y. split; [constructor|].
    split; [assumption|]. eapply initial_state_valid; eauto.
  - intros x y m y' Hmatch Hstep.
    exact (trace_backward_simulation p q Hwf x y m Hmatch y' Hstep).
  - intros x y m v [sync [Hsteps [Hmatch Hvalid]]] Hfinal.
    assert (y = sync) by (eapply final_starN; eauto). subst sync.
    eapply sync_rel_final_backward; eauto.
  - intros x y m [sync [Hsteps [Hmatch Hvalid]]] Hprogress.
    destruct m as [|m].
    + apply starN_inv_O in Hsteps. subst sync.
      destruct Hprogress as [[v Hfinal]|[x' Hstep]].
      * left. exists v. eapply sync_rel_final; eauto.
      * right. destruct (trace_step_simulation p q x y Hmatch x' Hstep)
          as [y' [Hplus Hmatch']]. inversion Hplus; subst; eauto.
    + right. destruct (starN_inv_S (step q) m y sync Hsteps)
        as [y' [Hstep Hrest]]. eauto.
Qed.

(** Every profile over the valid candidate callsites of a well-formed source
    with valid entrypoints compiles successfully to a program bisimilar to
    that source. *)
Theorem compile_profile_bisimulation p s :
  wf_program p -> wf_entrypoints p ->
  exists q, compile_profile p (candidate_sites p) s = Some q /\ bisimulation p q.
Proof.
  intros Hwf Hentry. destruct (candidate_profiles_compile p s) as [q Hcompile].
  assert (Htrace : inline_trace p q) by (eapply compile_from_trace; exact Hcompile).
  exists q. split; [assumption|]. constructor.
  - apply inline_trace_forward_sim; assumption.
  - apply inline_trace_backward_sim; assumption.
Qed.

(** A forward simulation matches every finite source execution from related
    states with a finite target execution ending in related states. *)
Corollary forward_sim_reachable p q :
  forward_sim p q -> forall x x', reachable p x x' ->
    forall y m, sim_rel p q m x y ->
      exists y' m', reachable q y y' /\ sim_rel p q m' x' y'.
Proof.
  intros Hsim x x' Hreach. unfold reachable in Hreach.
  induction Hreach; intros y m Hmatch.
  - exists y, m. split; [constructor|assumption].
  - destruct (fsim_step p q Hsim s1 y m s2 Hmatch H)
      as [y' [m' [Hsteps Hmatch']]].
    destruct (IHHreach y' m' Hmatch') as [y'' [m'' [Hrest Hmatch'']]].
    exists y'', m''. split; [|assumption].
    eapply star_trans; [apply plus_to_star; exact Hsteps|exact Hrest].
Qed.

(** A backward simulation matches every finite target execution from related
    states with a finite source execution that extends the existing source
    execution and ends in related states. *)
Corollary backward_sim_reachable p q :
  backward_sim p q -> forall y y', reachable q y y' ->
    forall start x m, reachable p start x -> sim_rel p q m x y ->
      exists x' m', reachable p start x' /\ sim_rel p q m' x' y'.
Proof.
  intros Hsim y y' Hreach. unfold reachable in Hreach.
  induction Hreach; intros start x m Hsource Hmatch.
  - exists x, m. auto.
  - destruct (bsim_step p q Hsim x s1 m s2 Hmatch H)
      as [[x' [m' [Hsteps Hmatch']]]|[m' [Hmatch' Hlt]]].
    + apply IHHreach with (x := x') (m := m'); [|assumption].
      eapply star_trans; [exact Hsource|]. apply plus_to_star. exact Hsteps.
    + apply IHHreach with (x := x) (m := m'); assumption.
Qed.

(** A program returns [v] when its top-level function reaches an [Iret]
    with an empty call stack and the return register contains [v]. *)
Definition returns (p : program) (v : nat) : Prop :=
  exists start finish,
    initial_state p start /\ reachable p start finish /\ final_state finish v.

(** Bisimilar programs have exactly the same possible return values from
    their top-level functions. *)
Corollary return_values_preserved p q :
  bisimulation p q -> forall v, returns p v <-> returns q v.
Proof.
  intros [Hforward Hbackward] v. split;
    intros [start [finish [Hinit [Hreach Hfinal]]]].
  - destruct (fsim_initial p q Hforward start Hinit)
      as [start' [m [Hinit' Hmatch]]].
    destruct (forward_sim_reachable p q Hforward start finish Hreach start' m Hmatch)
      as [sync [m' [Hreach' Hmatch']]].
    destruct (fsim_final p q Hforward finish sync m' v Hmatch' Hfinal)
      as [finish' [Hcleanup [Hfinal' Hmatch'']]].
    exists start', finish'. split; [assumption|]. split; [|assumption].
    eapply star_trans; eauto.
  - destruct (bsim_initial p q Hbackward start Hinit) as [start' [m [Hinit' Hmatch]]].
    destruct (backward_sim_reachable p q Hbackward start finish Hreach
      start' start' m (star_refl (step p) start') Hmatch)
      as [finish' [m' [Hreach' Hmatch']]].
    exists start', finish'. repeat split; try assumption.
    eapply bsim_final; eauto.
Qed.

Section Pass.
  Variable source : program.
  Variable E : nat.
  Variable uses : nat -> bool -> nat -> bool.
  Variables a b : nat -> nat.

  Let sites := candidate_sites source.
  Let N := length sites.

  (** The selector chooses the inlining decisions using the congestion model. *)
  Definition selected_profile (initial : profile) : profile :=
    select_profile N E uses a b initial.

  (** The pass applies the selected inlining decisions to the original program. *)
  Definition pass (initial : profile) : option program :=
    compile_profile source sites (selected_profile initial).

  (** For a well-formed source with valid entrypoints, the executable pass
      succeeds and produces a program bisimilar to the source. *)
  Theorem pass_correct initial :
    wf_program source -> wf_entrypoints source ->
    exists q, pass initial = Some q /\ bisimulation source q.
  Proof. apply compile_profile_bisimulation. Qed.

  (** The profile selected by the pass has congestion cost at most five
      halves of the cost of any profile over the same candidate callsites. *)
  Theorem pass_cost initial :
    forall alternative,
      2 * SocialCost N E uses a b (selected_profile initial) <=
      5 * SocialCost N E uses a b alternative.
  Proof.
    intros alternative. apply price_of_anarchy. apply select_profile_PNE.
  Qed.
  (** The selected profile is reached within the initial potential's bound
      on improving moves and is an equilibrium where no callsite can lower
      its own cost by changing its decision. *)
  Theorem pass_convergence initial :
    exists k,
      k <= Phi N E uses a b initial /\
      steps N E uses a b k initial (selected_profile initial) /\
      PNE N E uses a b (selected_profile initial).
  Proof. apply select_profile_correct. Qed.

  (** After [k] accepted improving moves, the social cost is at most twice
      [E * (A * N * N + B * N) - k] when [A] and [B] bound every resource's
      slope and offset. *)
  Theorem pass_intermediate_cost A B initial k current :
    (forall r, r < E -> a r <= A) ->
    (forall r, r < E -> b r <= B) ->
    steps N E uses a b k initial current ->
    SocialCost N E uses a b current <=
      2 * (E * (A * N * N + B * N) - k).
  Proof. apply intermediate_cost_bound_by_global_params. Qed.
End Pass.
