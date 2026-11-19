(** * CongestionGame.v

    Inlining-as-congestion-game.

    Model: players = candidate call sites; strategy = [bool] ([true] = inline);
    resources = I-cache lines [0..E-1]; resource costs linear over [nat]
    ([rcost r x = a r * x + b r]).

    Top-level results:
      (GOAL 1) [step_decreases_Phi] : every improving best-response move
               strictly decreases the Rosenthal potential.
      (GOAL 2) [convergence_bounded] / [exists_PNE] : iterative better
               response reaches, and hence there exists, a pure Nash
               equilibrium, with an explicit potential-sized step bound.
      (GOAL 3) [price_of_anarchy] : every pure Nash equilibrium has social cost
               at most 5/2 the optimum, i.e. [2*Cost(nash) <= 5*Cost(opt)]. *)

From Stdlib Require Import List Nat Bool Lia Arith Relations Wf_nat.
Import ListNotations.

(** [Sum n f = f 0 + f 1 + ... + f (n-1)]. *)
Definition Sum (n : nat) (f : nat -> nat) : nat :=
  fold_right (fun i acc => f i + acc) 0 (seq 0 n).


Section CongestionGame.

  Variable N : nat.                       (* number of players (call sites)    *)
  Variable E : nat.                       (* number of resources (cache lines) *)
  Variable uses : nat -> bool -> nat -> bool.
                                          (* uses i b r : player i, strategy b,*)
                                          (* occupies resource r               *)
  Variable a : nat -> nat.                (* linear cost slope  per resource   *)
  Variable b : nat -> nat.                (* linear cost offset per resource   *)

  (** A pure strategy profile (only coordinates [< N] are ever inspected). *)
  Definition profile := nat -> bool.

  (** Linear resource cost. *)
  Definition rcost (r x : nat) : nat := a r * x + b r.

  (** Load of resource [r]: number of players (< N) occupying it. *)
  Definition load (s : profile) (r : nat) : nat :=
    length (filter (fun i => uses i (s i) r) (seq 0 N)).

  (** Cost experienced by player [i]. *)
  Definition pcost (s : profile) (i : nat) : nat :=
    Sum E (fun r => if uses i (s i) r then rcost r (load s r) else 0).

  (** Social cost = sum of player costs. *)
  Definition SocialCost (s : profile) : nat := Sum N (pcost s).

  (** Rosenthal potential.  [Phi_res r m = rcost r 1 + ... + rcost r m]. *)
  Definition Phi_res (r m : nat) : nat := Sum m (fun k => rcost r (S k)).
  Definition Phi (s : profile) : nat := Sum E (fun r => Phi_res r (load s r)).

  (** Unilateral update: player [i] switches to [bi]. *)
  Definition upd (s : profile) (i : nat) (bi : bool) : profile :=
    fun j => if Nat.eqb j i then bi else s j.

  (** An improving move strictly lowers the mover's own cost. *)
  Definition improving (s : profile) (i : nat) (bi : bool) : Prop :=
    i < N /\ pcost (upd s i bi) i < pcost s i.

  (** One step of iterative better response. *)
  Inductive step : profile -> profile -> Prop :=
  | step_intro : forall s i bi, improving s i bi -> step s (upd s i bi).

  (** Exactly [k] better-response steps. *)
  Inductive steps : nat -> profile -> profile -> Prop :=
  | steps_refl : forall s,
      steps 0 s s
  | steps_cons : forall k s1 s2 s3,
      step s1 s2 ->
      steps k s2 s3 ->
      steps (S k) s1 s3.

  (** Pure Nash equilibrium: no player has an improving deviation. *)
  Definition PNE (s : profile) : Prop :=
    forall i bi, i < N -> pcost s i <= pcost (upd s i bi) i.

  (** Elementary finite sums and update bookkeeping *)

  Lemma fold_right_sum_acc (l : list nat) (f : nat -> nat) (z : nat) :
    fold_right (fun i acc => f i + acc) z l =
    fold_right (fun i acc => f i + acc) 0 l + z.
  Proof.
    induction l as [|x xs IH]; simpl; lia.
  Qed.

  Lemma Sum_S n f :
    Sum (S n) f = Sum n f + f n.
  Proof.
    unfold Sum.
    rewrite seq_S, fold_right_app.
    simpl.
    rewrite fold_right_sum_acc.
    lia.
  Qed.

  Lemma Sum_ext n f g :
    (forall i, i < n -> f i = g i) ->
    Sum n f = Sum n g.
  Proof.
    induction n as [|n IH]; intros Hext.
    - reflexivity.
    - repeat rewrite Sum_S.
      rewrite IH by (intros i Hi; apply Hext; lia).
      rewrite Hext by lia.
      reflexivity.
  Qed.

  Lemma Sum_split n f g :
    Sum n (fun i => f i + g i) = Sum n f + Sum n g.
  Proof.
    induction n as [|n IH].
    - reflexivity.
    - repeat rewrite Sum_S.
      rewrite IH; lia.
  Qed.

  Lemma Sum_zero n :
    Sum n (fun _ => 0) = 0.
  Proof.
    induction n as [|n IH].
    - unfold Sum; simpl; lia.
    - rewrite Sum_S, IH; reflexivity.
  Qed.

  Lemma Sum_const n c :
    Sum n (fun _ => c) = n * c.
  Proof.
    induction n as [|n IH].
    - reflexivity.
    - rewrite Sum_S, IH; lia.
  Qed.

  Lemma Sum_le n f g :
    (forall i, i < n -> f i <= g i) ->
    Sum n f <= Sum n g.
  Proof.
    induction n as [|n IH]; intros Hle.
    - reflexivity.
    - repeat rewrite Sum_S.
      assert (Hprefix : Sum n f <= Sum n g).
      { apply IH; intros i Hi; apply Hle; lia. }
      specialize (Hle n (Nat.lt_succ_diag_r n)).
      lia.
  Qed.

  Lemma Sum_scal n c f :
    Sum n (fun i => c * f i) = c * Sum n f.
  Proof.
    induction n as [|n IH].
    - unfold Sum; simpl; lia.
    - repeat rewrite Sum_S.
      rewrite IH; lia.
  Qed.

  Lemma Sum_swap n m g :
    Sum n (fun i => Sum m (g i)) =
    Sum m (fun j => Sum n (fun i => g i j)).
  Proof.
    induction n as [|n IH].
    - replace (Sum m (fun j : nat => Sum 0 (fun i : nat => g i j)))
        with (Sum m (fun _ : nat => 0)).
      + change (0 = Sum m (fun _ : nat => 0)).
        rewrite Sum_zero; reflexivity.
      + apply Sum_ext; intros j Hj.
        reflexivity.
    - rewrite Sum_S, IH.
      rewrite <- Sum_split.
      apply Sum_ext; intros j Hj.
      rewrite Sum_S.
      reflexivity.
  Qed.

  Lemma Sum_indicator_const n (P : nat -> bool) c :
    Sum n (fun i => if P i then c else 0) =
    Sum n (fun i => if P i then 1 else 0) * c.
  Proof.
    induction n as [|n IH].
    - reflexivity.
    - repeat rewrite Sum_S.
      rewrite IH.
      destruct (P n); lia.
  Qed.

  Lemma Sum_one_more n i f g :
    i < n ->
    (forall j, j < n -> j <> i -> f j = g j) ->
    f i = S (g i) ->
    Sum n f = S (Sum n g).
  Proof.
    revert i f g.
    induction n as [|n IH]; intros i f g Hi Hsame Hone.
    - lia.
    - repeat rewrite Sum_S.
      destruct (Nat.eq_dec i n) as [->|Hne].
      + rewrite (Sum_ext n f g).
        * rewrite Hone; lia.
        * intros j Hj. apply Hsame; lia.
      + rewrite (IH i f g) by (try lia; intros; apply Hsame; lia).
        rewrite Hsame by lia.
        lia.
  Qed.

  Lemma length_filter_singleton (P : nat -> bool) (x : nat) :
    length (filter P [x]) = if P x then 1 else 0.
  Proof.
    simpl.
    destruct (P x) eqn:HP; try setoid_rewrite HP; reflexivity.
  Qed.

  Lemma length_filter_seq_sum n P :
    length (filter P (seq 0 n)) = Sum n (fun i => if P i then 1 else 0).
  Proof.
    induction n as [|n IH].
    - reflexivity.
    - rewrite seq_S, filter_app, length_app, Sum_S.
      rewrite IH.
      replace (0 + n) with n by lia.
      rewrite length_filter_singleton.
      lia.
  Qed.

  Lemma upd_same s i bi :
    upd s i bi i = bi.
  Proof.
    unfold upd; rewrite Nat.eqb_refl; reflexivity.
  Qed.

  Lemma upd_other s i bi j :
    j <> i -> upd s i bi j = s j.
  Proof.
    intros Hne.
    unfold upd.
    apply Nat.eqb_neq in Hne.
    rewrite Hne; reflexivity.
  Qed.

  Lemma load_eq_sum s r :
    load s r = Sum N (fun i => if uses i (s i) r then 1 else 0).
  Proof.
    unfold load.
    apply length_filter_seq_sum.
  Qed.

  Lemma load_le_N s r :
    load s r <= N.
  Proof.
    rewrite load_eq_sum.
    eapply Nat.le_trans with (m := Sum N (fun _ => 1)).
    - apply Sum_le; intros i Hi.
      destruct (uses i (s i) r); lia.
    - rewrite Sum_const; lia.
  Qed.

  Lemma load_upd_same s i bi r :
    i < N ->
    uses i (s i) r = uses i bi r ->
    load (upd s i bi) r = load s r.
  Proof.
    intros Hi Hbit.
    repeat rewrite load_eq_sum.
    apply Sum_ext; intros j Hj.
    destruct (Nat.eq_dec j i) as [->|Hne].
    - rewrite upd_same, Hbit; reflexivity.
    - rewrite upd_other by exact Hne; reflexivity.
  Qed.

  Lemma load_upd_leave s i bi r :
    i < N ->
    uses i (s i) r = true ->
    uses i bi r = false ->
    load s r = S (load (upd s i bi) r).
  Proof.
    intros Hi Hold Hnew.
    repeat rewrite load_eq_sum.
    apply Sum_one_more with (i := i).
    - exact Hi.
    - intros j Hj Hne.
      rewrite upd_other by exact Hne.
      reflexivity.
    - rewrite Hold, upd_same, Hnew.
      reflexivity.
  Qed.

  Lemma load_upd_join s i bi r :
    i < N ->
    uses i (s i) r = false ->
    uses i bi r = true ->
    load (upd s i bi) r = S (load s r).
  Proof.
    intros Hi Hold Hnew.
    repeat rewrite load_eq_sum.
    apply Sum_one_more with (i := i).
    - exact Hi.
    - intros j Hj Hne.
      rewrite upd_other by exact Hne.
      reflexivity.
    - rewrite upd_same, Hnew, Hold.
      reflexivity.
  Qed.

  Lemma load_upd_le s i bi r :
    i < N ->
    load (upd s i bi) r <= S (load s r).
  Proof.
    intros Hi.
    destruct (uses i (s i) r) eqn:Hold;
      destruct (uses i bi r) eqn:Hnew.
    - assert (Hbit : uses i (s i) r = uses i bi r)
        by (rewrite Hold, Hnew; reflexivity).
      rewrite (load_upd_same s i bi r Hi Hbit); lia.
    - pose proof (load_upd_leave s i bi r Hi Hold Hnew).
      lia.
    - rewrite (load_upd_join s i bi r Hi Hold Hnew); lia.
    - assert (Hbit : uses i (s i) r = uses i bi r)
        by (rewrite Hold, Hnew; reflexivity).
      rewrite (load_upd_same s i bi r Hi Hbit); lia.
  Qed.

  Lemma rcost_mono r x y :
    x <= y -> rcost r x <= rcost r y.
  Proof.
    unfold rcost; intros Hle.
    nia.
  Qed.

  Lemma SocialCost_eq s :
    SocialCost s =
    Sum E (fun r => load s r * rcost r (load s r)).
  Proof.
    unfold SocialCost, pcost.
    rewrite Sum_swap.
    apply Sum_ext; intros r Hr.
    rewrite Sum_indicator_const.
    rewrite <- load_eq_sum.
    reflexivity.
  Qed.

  Lemma deviation_cost_bound s p i :
    i < N ->
    pcost (upd s i (p i)) i <=
    Sum E (fun r =>
      if uses i (p i) r then rcost r (S (load s r)) else 0).
  Proof.
    intros Hi.
    unfold pcost.
    rewrite upd_same.
    apply Sum_le; intros r Hr.
    destruct (uses i (p i) r) eqn:Huses.
    - apply rcost_mono.
      apply load_upd_le; exact Hi.
    - lia.
  Qed.

  Lemma nash_deviation_bound s p :
    PNE s ->
    SocialCost s <=
    Sum E (fun r => load p r * rcost r (S (load s r))).
  Proof.
    intros Hpne.
    unfold SocialCost.
    eapply Nat.le_trans.
    - apply Sum_le; intros i Hi.
      apply Hpne; exact Hi.
    - eapply Nat.le_trans.
      + apply Sum_le; intros i Hi.
        apply deviation_cost_bound; exact Hi.
      + rewrite Sum_swap.
        apply Sum_le; intros r Hr.
        rewrite Sum_indicator_const.
        rewrite <- load_eq_sum.
        reflexivity.
  Qed.

  Lemma cross_term_bound x y :
    3 * x * y <= x * x + 3 * y * y.
  Proof.
    destruct (le_gt_dec x y) as [Hxy|Hxy].
    - assert (x * y <= y * y) by (apply Nat.mul_le_mono_r; lia).
      nia.
    - set (d := x - y).
      assert (Hx : x = y + d) by (unfold d; lia).
      destruct (le_gt_dec d y) as [Hdy|Hdy].
      + assert (d * y <= y * y) by (apply Nat.mul_le_mono_r; lia).
        nia.
      + assert (d * y <= d * d) by (apply Nat.mul_le_mono_l; lia).
        nia.
  Qed.

  Lemma christodoulou_nat x y :
    3 * y * S x <= 5 * y * y + x * x.
  Proof.
    destruct y as [|[|y']].
    - nia.
    - destruct (le_gt_dec x 2) as [Hx|Hx]; nia.
    - pose proof (cross_term_bound x (S (S y'))) as Hxy.
      nia.
  Qed.

  Lemma resource_smoothness r x y :
    3 * (y * rcost r (S x)) <=
    5 * (y * rcost r y) + x * rcost r x.
  Proof.
    unfold rcost.
    remember (a r) as ar.
    remember (b r) as br.
    pose proof (christodoulou_nat x y) as Hcore.
    nia.
  Qed.

  Lemma Phi_res_S r m :
    Phi_res r (S m) = Phi_res r m + rcost r (S m).
  Proof.
    unfold Phi_res.
    change (Sum (S m) (fun k => rcost r (S k)) =
            Sum m (fun k => rcost r (S k)) +
            (fun k => rcost r (S k)) m).
    apply Sum_S.
  Qed.

  Lemma Phi_res_linear_bound r m :
    m <= N ->
    Phi_res r m <= m * rcost r N.
  Proof.
    induction m as [|m IH]; intros Hm.
    - unfold Phi_res, Sum; simpl; lia.
    - rewrite Phi_res_S.
      assert (Hm' : m <= N) by lia.
      specialize (IH Hm').
      assert (Hcost : rcost r (S m) <= rcost r N).
      { apply rcost_mono; lia. }
      lia.
  Qed.

  Definition PhiBound : nat :=
    Sum E (fun r => a r * N * N + b r * N).

  Theorem Phi_bounded s :
    Phi s <= PhiBound.
  Proof.
    unfold Phi, PhiBound.
    apply Sum_le; intros r Hr.
    eapply Nat.le_trans with (m := load s r * rcost r N).
    - apply Phi_res_linear_bound.
      apply load_le_N.
    - unfold rcost.
      pose proof (load_le_N s r) as Hload.
      assert (Hmul : load s r * (a r * N + b r) <=
                     N * (a r * N + b r)).
      { apply Nat.mul_le_mono_r; exact Hload. }
      nia.
  Qed.

  Theorem PhiBound_global A B :
    (forall r, r < E -> a r <= A) ->
    (forall r, r < E -> b r <= B) ->
    PhiBound <= E * (A * N * N + B * N).
  Proof.
    intros Ha Hb.
    unfold PhiBound.
    eapply Nat.le_trans with
      (m := Sum E (fun _ => A * N * N + B * N)).
    - apply Sum_le; intros r Hr.
      specialize (Ha r Hr).
      specialize (Hb r Hr).
      assert (HaNN : a r * N * N <= A * N * N).
      { apply Nat.mul_le_mono_r.
        apply Nat.mul_le_mono_r.
        exact Ha. }
      assert (HbN : b r * N <= B * N).
      { apply Nat.mul_le_mono_r; exact Hb. }
      lia.
    - rewrite Sum_const.
      reflexivity.
  Qed.

  Lemma potential_exact s i bi :
    i < N ->
    Phi (upd s i bi) + pcost s i =
    Phi s + pcost (upd s i bi) i.
  Proof.
    intros Hi.
    unfold Phi, pcost.
    rewrite <- Sum_split.
    rewrite <- Sum_split.
    apply Sum_ext; intros r Hr.
    rewrite upd_same.
    destruct (uses i (s i) r) eqn:Hold;
      destruct (uses i bi r) eqn:Hnew.
    - assert (Hbit : uses i (s i) r = uses i bi r)
        by (rewrite Hold, Hnew; reflexivity).
      rewrite (load_upd_same s i bi r Hi Hbit).
      reflexivity.
    - pose proof (load_upd_leave s i bi r Hi Hold Hnew) as Hload.
      rewrite Hload.
      rewrite Phi_res_S.
      lia.
    - pose proof (load_upd_join s i bi r Hi Hold Hnew) as Hload.
      rewrite Hload.
      rewrite Phi_res_S.
      lia.
    - assert (Hbit : uses i (s i) r = uses i bi r)
        by (rewrite Hold, Hnew; reflexivity).
      rewrite (load_upd_same s i bi r Hi Hbit).
      reflexivity.
  Qed.

  (** monotone progress *)

  Theorem step_decreases_Phi s s' :
    step s s' -> Phi s' < Phi s.
  Proof.
    intros Hstep.
    inversion Hstep as [s0 i bi Himprove Heq]; subst s0 s'.
    destruct Himprove as [Hi Hcost].
    pose proof (potential_exact s i bi Hi) as Hpot.
    lia.
  Qed.

  Theorem steps_decrease_Phi_by_length k s s' :
    steps k s s' -> Phi s' + k <= Phi s.
  Proof.
    induction 1.
    - lia.
    - pose proof (step_decreases_Phi s1 s2 H) as Hdec.
      lia.
  Qed.

  Corollary steps_length_le_Phi k s s' :
    steps k s s' -> k <= Phi s.
  Proof.
    intros Hsteps.
    pose proof (steps_decrease_Phi_by_length k s s' Hsteps).
    lia.
  Qed.

  Corollary potential_after_k_steps k s s' :
    steps k s s' -> Phi s' <= Phi s - k.
  Proof.
    intros Hsteps.
    pose proof (steps_decrease_Phi_by_length k s s' Hsteps).
    lia.
  Qed.

  (** Deterministic exhaustive search of both choices for players [0..n-1]. *)
  Fixpoint find_move (s : profile) (n : nat) : option (nat * bool) :=
    match n with
    | 0 => None
    | S j =>
        if pcost (upd s j true) j <? pcost s j then Some (j, true)
        else if pcost (upd s j false) j <? pcost s j then Some (j, false)
        else find_move s j
    end.

  Lemma find_move_sound n : forall s i bi,
    find_move s n = Some (i, bi) ->
    i < n /\ pcost (upd s i bi) i < pcost s i.
  Proof.
    induction n as [|j IH]; intros s i bi Hfind; simpl in Hfind.
    - discriminate.
    - destruct (pcost (upd s j true) j <? pcost s j) eqn:Ht.
      + inversion Hfind; subst. apply Nat.ltb_lt in Ht. split; lia.
      + destruct (pcost (upd s j false) j <? pcost s j) eqn:Hf.
        * inversion Hfind; subst. apply Nat.ltb_lt in Hf. split; lia.
        * destruct (IH s i bi Hfind) as [Hi Hcost]. split; lia.
  Qed.

  Lemma find_move_none n : forall s,
    find_move s n = None ->
    forall i bi, i < n -> pcost s i <= pcost (upd s i bi) i.
  Proof.
    induction n as [|j IH]; intros s Hfind i bi Hi; [lia|].
    simpl in Hfind.
    destruct (pcost (upd s j true) j <? pcost s j) eqn:Ht;
      try discriminate.
    destruct (pcost (upd s j false) j <? pcost s j) eqn:Hf;
      try discriminate.
    apply Nat.ltb_ge in Ht. apply Nat.ltb_ge in Hf.
    destruct (Nat.eq_dec i j) as [->|Hne].
    - destruct bi; assumption.
    - apply (IH s Hfind); lia.
  Qed.

  Fixpoint respond (fuel : nat) (s : profile) : profile :=
    match fuel with
    | 0 => s
    | S remaining =>
        match find_move s N with
        | None => s
        | Some (i, bi) => respond remaining (upd s i bi)
        end
    end.

  Theorem respond_correct fuel : forall s,
    Phi s <= fuel ->
    exists k,
      k <= fuel /\ steps k s (respond fuel s) /\
      PNE (respond fuel s).
  Proof.
    induction fuel as [|fuel IH]; intros s Hfuel.
    - assert (Hnone : find_move s N = None).
      { destruct (find_move s N) as [[i bi]|] eqn:Hfind; [|reflexivity].
        destruct (find_move_sound N s i bi Hfind) as [Hi Hcost].
        assert (Hstep : step s (upd s i bi)).
        { constructor. split; assumption. }
        pose proof (step_decreases_Phi _ _ Hstep). lia. }
      exists 0. simpl. split; [lia|]. split; [constructor|].
      exact (find_move_none N s Hnone).
    - simpl. destruct (find_move s N) as [[i bi]|] eqn:Hfind.
      + destruct (find_move_sound N s i bi Hfind) as [Hi Hcost].
        assert (Hstep : step s (upd s i bi)).
        { constructor. split; assumption. }
        pose proof (step_decreases_Phi _ _ Hstep) as Hdrop.
        destruct (IH (upd s i bi) ltac:(lia)) as [k [Hk [Hsteps Hpne]]].
        exists (S k). split; [lia|]. split; [|exact Hpne].
        eapply steps_cons; eauto.
      + exists 0. split; [lia|]. split; [constructor|].
        exact (find_move_none N s Hfind).
  Qed.

  Definition select_profile (s : profile) : profile := respond (Phi s) s.

  Theorem select_profile_correct s :
    exists k,
      k <= Phi s /\ steps k s (select_profile s) /\
      PNE (select_profile s).
  Proof. apply respond_correct. reflexivity. Qed.

  Corollary select_profile_PNE s : PNE (select_profile s).
  Proof. destruct (select_profile_correct s) as [k [_ [_ H]]]. exact H. Qed.

  (** Existential interfaces are corollaries of the executable search. *)
  Lemma PNE_or_improving_prefix s n :
    (forall i bi, i < n -> pcost s i <= pcost (upd s i bi) i) \/
    (exists i bi, i < n /\ pcost (upd s i bi) i < pcost s i).
  Proof.
    destruct (find_move s n) as [[i bi]|] eqn:Hfind.
    - right. exists i, bi. exact (find_move_sound n s i bi Hfind).
    - left. exact (find_move_none n s Hfind).
  Qed.

  Lemma PNE_or_improving s :
    PNE s \/ exists i bi, improving s i bi.
  Proof. exact (PNE_or_improving_prefix s N). Qed.

  Lemma steps_clos_refl_trans k s s' :
    steps k s s' -> clos_refl_trans profile step s s'.
  Proof.
    induction 1.
    - apply rt_refl.
    - eapply rt_trans.
      + apply rt_step; exact H.
      + exact IHsteps.
  Qed.

  Theorem convergence_bounded_fuel :
    forall fuel s,
      Phi s <= fuel ->
      exists k s', k <= fuel /\ steps k s s' /\ PNE s'.
  Proof.
    intros fuel s Hfuel.
    destruct (respond_correct fuel s Hfuel) as [k Hcorrect].
    exists k, (respond fuel s). exact Hcorrect.
  Qed.

  Theorem convergence_bounded :
    forall s,
      exists k s',
        k <= Phi s /\ steps k s s' /\ PNE s'.
  Proof.
    intros s.
    apply convergence_bounded_fuel.
    reflexivity.
  Qed.

  Theorem remaining_convergence_after_steps :
    forall k s s',
      steps k s s' ->
      exists k_rem s_star,
        k + k_rem <= Phi s /\ steps k_rem s' s_star /\ PNE s_star.
  Proof.
    intros k s s' Hsteps.
    destruct (convergence_bounded s') as
      (k_rem & s_star & Hk_rem & Htail & Hpne).
    pose proof (steps_decrease_Phi_by_length k s s' Hsteps) as Hdrop.
    exists k_rem, s_star.
    split; [lia|].
    split; assumption.
  Qed.

  Theorem convergence_bounded_by_params :
    forall s,
      exists k s',
        k <= PhiBound /\ steps k s s' /\ PNE s'.
  Proof.
    intros s.
    apply convergence_bounded_fuel.
    apply Phi_bounded.
  Qed.

  Theorem convergence_bounded_by_global_params A B :
    (forall r, r < E -> a r <= A) ->
    (forall r, r < E -> b r <= B) ->
    forall s,
      exists k s',
        k <= E * (A * N * N + B * N) /\ steps k s s' /\ PNE s'.
  Proof.
    intros Ha Hb s.
    pose proof (Phi_bounded s) as Hphi.
    pose proof (PhiBound_global A B Ha Hb) as Hglobal.
    apply convergence_bounded_fuel.
    lia.
  Qed.

  Theorem convergence :
    forall s, exists s', clos_refl_trans profile step s s' /\ PNE s'.
  Proof.
    intros s.
    destruct (convergence_bounded s) as (k & s' & _ & Hsteps & Hpne).
    exists s'.
    split; [|exact Hpne].
    apply steps_clos_refl_trans with (k := k).
    exact Hsteps.
  Qed.

  Corollary exists_PNE : exists s, PNE s.
  Proof.
    destruct (convergence (fun _ => false)) as (s & _ & Hpne).
    exists s; exact Hpne.
  Qed.

  (** price of anarchy 5/2 *)

  Theorem price_of_anarchy s p :
    PNE s -> 2 * SocialCost s <= 5 * SocialCost p.
  Proof.
    intros Hpne.
    set (Dev := fun r => load p r * rcost r (S (load s r))).
    pose proof (nash_deviation_bound s p Hpne) as Hdev.
    fold Dev in Hdev.
    assert (Hsmooth :
              3 * Sum E Dev <= 5 * SocialCost p + SocialCost s).
    { rewrite <- (Sum_scal E 3 Dev).
      eapply Nat.le_trans.
      - apply Sum_le; intros r Hr.
        unfold Dev.
        apply resource_smoothness.
      - unfold Dev.
        rewrite Sum_split.
        rewrite Sum_scal.
        rewrite <- (SocialCost_eq p).
        rewrite <- (SocialCost_eq s).
        reflexivity.
    }
    assert (Hdev3 : 3 * SocialCost s <= 3 * Sum E Dev) by lia.
    assert (Hchain : 3 * SocialCost s <= 5 * SocialCost p + SocialCost s)
      by lia.
    lia.
  Qed.

End CongestionGame.
