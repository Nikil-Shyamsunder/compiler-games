From VerifPerf Require Import Syntax Semantics Inlining InliningProof BackwardSim.
From Stdlib Require Import List Lia.
Import ListNotations.

Inductive star {A : Type} (step : A -> A -> Prop) : A -> A -> Prop :=
| star_refl : forall s, star step s s
| star_step : forall s1 s2 s3,
    step s1 s2 -> star step s2 s3 -> star step s1 s3.

Definition reachable (p : program) (s0 s : state) : Prop :=
  star (step p) s0 s.

Definition wf_entrypoints (p : program) : Prop :=
  forall fi f, nth_error p fi = Some f -> pc_valid f 0.

Lemma star_trans : forall {A} (R : A -> A -> Prop) s1 s2 s3,
  star R s1 s2 -> star R s2 s3 -> star R s1 s3.
Proof.
  intros A R s1 s2 s3 H12 H23.
  induction H12.
  - exact H23.
  - eapply star_step; eauto.
Qed.

Lemma plus_to_star : forall {A} (R : A -> A -> Prop) s1 s2,
  plus R s1 s2 -> star R s1 s2.
Proof.
  intros A R s1 s2 Hplus.
  induction Hplus.
  - eapply star_step; [eassumption | constructor].
  - eapply star_step; eauto.
Qed.

Lemma initial_state_valid : forall p s,
  wf_entrypoints p ->
  initial_state p s ->
  state_valid p s.
Proof.
  intros p s Hentry [f [Hf ->]].
  simpl. split.
  - eapply Hentry. exact Hf.
  - split.
    + exists 0. exact Hf.
    + constructor.
Qed.

Lemma state_valid_step : forall p s s',
  wf_program p ->
  state_valid p s ->
  step p s s' ->
  state_valid p s'.
Proof.
  intros p s s' Hwf Hvalid Hstep.
  inversion Hstep; subst; simpl in *.
  - destruct Hvalid as [_ [[fi Hfi] Hstk]].
    match goal with
    | [ Hcode : nth_error (fn_code f) pc = Some (Inop pc') |- _ ] =>
        destruct (Hwf fi f pc (Inop pc') Hfi Hcode) as [Hsucc _]
    end.
    split; [apply Hsucc; simpl; auto | split; [exists fi; exact Hfi | exact Hstk]].
  - destruct Hvalid as [_ [[fi Hfi] Hstk]].
    match goal with
    | [ Hcode : nth_error (fn_code f) pc = Some (Iop op args dst pc') |- _ ] =>
        destruct (Hwf fi f pc (Iop op args dst pc') Hfi Hcode) as [Hsucc _]
    end.
    split; [apply Hsucc; simpl; auto | split; [exists fi; exact Hfi | exact Hstk]].
  - destruct Hvalid as [_ [[fi Hfi] Hstk]].
    match goal with
    | [ Hcode : nth_error (fn_code f) pc = Some (Icond cond ifso ifnot) |- _ ] =>
        destruct (Hwf fi f pc (Icond cond ifso ifnot) Hfi Hcode) as [Hsucc _]
    end.
    split; [apply Hsucc; simpl; auto | split; [exists fi; exact Hfi | exact Hstk]].
  - destruct Hvalid as [_ [[fi Hfi] Hstk]].
    match goal with
    | [ Hcode : nth_error (fn_code f) pc = Some (Icond cond ifso ifnot) |- _ ] =>
        destruct (Hwf fi f pc (Icond cond ifso ifnot) Hfi Hcode) as [Hsucc _]
    end.
    split; [apply Hsucc; simpl; auto | split; [exists fi; exact Hfi | exact Hstk]].
  - destruct Hvalid as [_ [[fi Hfi] Hstk]].
    match goal with
    | [ Hcode : nth_error (fn_code f) pc = Some (Icall target args dst pc'),
        Hfd : nth_error p target = Some fd |- _ ] =>
        destruct (Hwf fi f pc (Icall target args dst pc') Hfi Hcode)
          as [Hsucc [fd0 [Hfd0 Hentry]]];
        assert (fd0 = fd) by congruence; subst fd0;
        split;
        [ exact Hentry
        | split;
          [ exists target; exact Hfd
          | constructor;
            [ split; [apply Hsucc; simpl; auto | exists fi; exact Hfi]
            | exact Hstk ] ] ]
    end.
  - destruct Hvalid as [_ [_ Hstk]].
    inversion Hstk as [|sf stk Hhead Htail]; subst.
    destruct Hhead as [Hret_valid Hcaller_in_p].
    split; [exact Hret_valid | split; [exact Hcaller_in_p | exact Htail]].
Qed.

Lemma state_valid_star : forall p s s',
  wf_program p ->
  state_valid p s ->
  star (step p) s s' ->
  state_valid p s'.
Proof.
  intros p s s' Hwf Hvalid Hstar.
  induction Hstar.
  - exact Hvalid.
  - apply IHHstar. eapply state_valid_step; eauto.
Qed.

Theorem inlining_forward_reachable :
  forall p cs p' s0 s0' s,
    inline p cs = Some p' ->
    match_states p cs p' s0 s0' ->
    reachable p s0 s ->
    exists s', reachable p' s0' s' /\ match_states p cs p' s s'.
Proof.
  intros p cs p' s0 s0' s Hinline Hmatch Hreach.
  unfold reachable in *.
  revert s0' Hmatch.
  induction Hreach; intros s0' Hmatch.
  - exists s0'. split; [constructor | exact Hmatch].
  - destruct (step_simulation p cs p' Hinline s1 s2 s0' Hmatch H)
      as [s2' [Hplus Hmatch']].
    destruct (IHHreach s2' Hmatch') as [sf [Hstar Hmatchf]].
    exists sf. split.
    + eapply star_trans; [apply plus_to_star; exact Hplus | exact Hstar].
    + exact Hmatchf.
Qed.

Lemma inlining_backward_reachable_from_bmatch :
  forall p cs p' s0 s s' t',
    inline p cs = Some p' ->
    wf_program p ->
    state_valid p s ->
    reachable p s0 s ->
    (exists m, bmatch (step p') (match_states p cs p') s s' m) ->
    star (step p') s' t' ->
    exists sf mf,
      reachable p s0 sf /\
      bmatch (step p') (match_states p cs p') sf t' mf.
Proof.
  intros p cs p' s0 s s' t' Hinline Hwf Hvalid Hsrc_reach Hbmatch Htgt_reach.
  unfold reachable in *.
  revert s Hvalid Hsrc_reach Hbmatch.
  induction Htgt_reach; intros src Hvalid Hsrc_reach [m Hbmatch].
  - exists src, m. split; assumption.
  - destruct (inlining_backward_simulation p cs p' Hinline Hwf
                src s1 m Hvalid Hbmatch s2 H)
      as [[s_next [m_next [Hplus Hbmatch_next]]]
         | [m_next [Hbmatch_next _]]].
    + pose proof (plus_to_star (step p) _ _ Hplus) as Hsrc_steps.
      assert (Hvalid_next : state_valid p s_next).
      { eapply state_valid_star; eauto. }
      assert (Hsrc_reach_next : star (step p) s0 s_next).
      { eapply star_trans; eauto. }
      eapply IHHtgt_reach; eauto.
    + eapply IHHtgt_reach; eauto.
Qed.

Theorem inlining_backward_reachable :
  forall p cs p' s0 s0' s',
    inline p cs = Some p' ->
    wf_program p ->
    wf_entrypoints p ->
    initial_state p s0 ->
    initial_state p' s0' ->
    match_states p cs p' s0 s0' ->
    reachable p' s0' s' ->
    exists s m,
      reachable p s0 s /\
      bmatch (step p') (match_states p cs p') s s' m.
Proof.
  intros p cs p' s0 s0' s' Hinline Hwf Hentry Hinit_src _ Hmatch Hreach_tgt.
  pose proof (initial_state_valid p s0 Hentry Hinit_src) as Hvalid0.
  eapply inlining_backward_reachable_from_bmatch; eauto.
  - constructor.
  - exists 0. exists s0'. split; [constructor | exact Hmatch].
Qed.

Theorem inlining_reached_forward_step :
  forall p cs p' s0 s0' s s' s1,
    inline p cs = Some p' ->
    initial_state p s0 ->
    initial_state p' s0' ->
    reachable p s0 s ->
    reachable p' s0' s' ->
    match_states p cs p' s s' ->
    step p s s1 ->
    exists s1',
      plus (step p') s' s1' /\
      match_states p cs p' s1 s1'.
Proof.
  intros p cs p' s0 s0' s s' s1 Hinline _ _ _ _ Hmatch Hstep.
  eapply step_simulation; eauto.
Qed.

Theorem inlining_reached_backward_step :
  forall p cs p' s0 s0' s s' s1',
    inline p cs = Some p' ->
    wf_program p ->
    wf_entrypoints p ->
    initial_state p s0 ->
    initial_state p' s0' ->
    reachable p s0 s ->
    reachable p' s0' s' ->
    match_states p cs p' s s' ->
    step p' s' s1' ->
    exists s1 m,
      step p s s1 /\
      bmatch (step p') (match_states p cs p') s1 s1' m.
Proof.
  intros p cs p' s0 s0' s s' s1' Hinline Hwf Hentry Hinit_src _ Hreach_src _ Hmatch Hstep.
  pose proof (initial_state_valid p s0 Hentry Hinit_src) as Hvalid0.
  pose proof (state_valid_star p s0 s Hwf Hvalid0 Hreach_src) as Hvalid.
  destruct (match_states_progress_wf p cs p' Hinline Hwf
              s s' Hmatch Hvalid (ex_intro _ _ Hstep)) as [s1 Hstep_src].
  destruct (step_simulation p cs p' Hinline s s1 s' Hmatch Hstep_src)
    as [sf [Hplus Hmatchf]].
  apply plus_starN in Hplus. destruct Hplus as [m HstarN].
  apply starN_inv_S in HstarN. destruct HstarN as [smid [Hfirst Hrest]].
  assert (smid = s1') by (eapply step_deterministic; eauto). subst smid.
  exists s1, m. split; [exact Hstep_src |].
  exists sf. split; [exact Hrest | exact Hmatchf].
Qed.

Theorem inlining_reachable_simulations :
  forall p cs p' s0 s0' s s',
    inline p cs = Some p' ->
    wf_program p ->
    wf_entrypoints p ->
    initial_state p s0 ->
    initial_state p' s0' ->
    match_states p cs p' s0 s0' ->
    reachable p s0 s ->
    reachable p' s0' s' ->
    (exists st, reachable p' s0' st /\ match_states p cs p' s st) /\
    (exists ss m,
      reachable p s0 ss /\
      bmatch (step p') (match_states p cs p') ss s' m).
Proof.
  intros p cs p' s0 s0' s s' Hinline Hwf Hentry Hinit_src Hinit_tgt Hmatch Hreach_src Hreach_tgt.
  split.
  - eapply inlining_forward_reachable; eauto.
  - eapply inlining_backward_reachable; eauto.
Qed.
