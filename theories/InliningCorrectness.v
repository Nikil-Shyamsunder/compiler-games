(** Reachability results for a single inline operation. *)
From VerifPerf Require Import Syntax Semantics Inlining InliningProof BackwardSim InliningWellformed.
From Stdlib Require Import List Arith Lia.
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

Lemma starN_to_star : forall {A} (R : A -> A -> Prop) n s1 s2,
  starN R n s1 s2 -> star R s1 s2.
Proof.
  intros A R n s1 s2 Hsteps. induction Hsteps.
  - constructor.
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

Lemma inline_initial_match p cs q x :
  inline p cs = Some q -> initial_state p x ->
  exists y, initial_state q y /\ match_states p cs q x y.
Proof.
  intros Hinline [f [Hf ->]].
  assert (Hf' : exists f', nth_error q 0 = Some f').
  { destruct (Nat.eq_dec 0 (cs_caller cs)) as [Heq|Hne].
    - rewrite Heq. eapply caller_in_p'; exact Hinline.
    - exists f. eapply other_func_preserved; eauto.
      apply nth_error_Some. rewrite Hf. discriminate. }
  destruct Hf' as [f' Hf'].
  pose proof (inline_preserves_params p cs q Hinline 0 f f' Hf Hf') as Hparams.
  exists (State [] f' 0 (init_regs [] (fn_params f'))).
  split.
  - exists f'. split; [assumption|reflexivity].
  - rewrite <- Hparams. eapply match_normal with (fi := 0).
    + constructor.
    + intros; reflexivity.
    + unfold regs_agree; intros; reflexivity.
    + exact Hf.
    + exact Hf'.
Qed.

Lemma inline_preserves_entrypoints p cs q :
  inline p cs = Some q -> wf_entrypoints p -> wf_entrypoints q.
Proof.
  intros Hinline Hentry fi f' Hf'.
  destruct (inline_lookup_source p cs q fi f' Hinline Hf') as [f [Hf Hlength]].
  apply pc_valid_iff. specialize (Hentry fi f Hf).
  apply pc_valid_iff in Hentry. lia.
Qed.

Lemma initial_state_unique p x y :
  initial_state p x -> initial_state p y -> x = y.
Proof. intros [f [Hf ->]] [g [Hg ->]]. assert (f = g) by congruence. congruence. Qed.

Lemma inline_source_initial p cs q :
  inline p cs = Some q -> exists x, initial_state p x.
Proof.
  intros Hinline. destruct p as [|f rest].
  - unfold inline in Hinline. rewrite nth_error_nil in Hinline. discriminate.
  - exists (State [] f 0 (init_regs [] (fn_params f))).
    exists f. auto.
Qed.

Lemma final_no_step p x v :
  final_state x v -> forall y, ~ step p x y.
Proof.
  intros (f & pc & rs & ret & -> & Hret & Hv) y Hstep.
  inversion Hstep; subst; congruence.
Qed.

Lemma final_starN p x y v n :
  final_state x v -> starN (step p) n x y -> x = y.
Proof.
  intros Hfinal Hsteps. inversion Hsteps; subst; [reflexivity|].
  exfalso. eapply final_no_step; eauto.
Qed.

Lemma match_final_forward p cs q x y v :
  inline p cs = Some q -> match_states p cs q x y ->
  final_state x v -> final_state y v.
Proof.
  intros Hinline Hmatch Hfinal.
  destruct Hmatch as
    [stk stk' fi f f' pc rs rs' Hstacks Hother Hregs Hf Hf'|
     stk stk' dst retpc rsc rsc' pc rscallee rs' caller'
       Hstacks Hregs Hcaller Hcall Hregs' Hcallee Hcaller'].
  - destruct Hfinal as (f0 & pc0 & rs0 & ret & Hstate & Hret & Hv).
    inversion Hstate; subst. inversion Hstacks; subst.
    assert (Hdistinct : fi <> cs_caller cs \/ pc0 <> cs_pc cs).
    { eapply pc_ne_cs_pc; eauto; discriminate. }
    assert (Hret' : nth_error (fn_code f') pc0 = Some (Iret ret)).
    { eapply code_at_pc_preserved; eauto. }
    exists f', pc0, rs', ret. split; [reflexivity|]. split; [assumption|].
    destruct (Nat.eq_dec fi (cs_caller cs)) as [Heq|Hne].
    + eapply regs_agree_on_instr; [apply Hregs; exact Heq| |exact Hret|simpl; auto].
      rewrite <- Heq. exact Hf.
    + rewrite <- (Hother Hne). reflexivity.
  - destruct Hfinal as (f0 & pc0 & rs0 & ret & Hstate & _).
    discriminate Hstate.
Qed.

Lemma match_final_backward p cs q x y v :
  inline p cs = Some q -> match_states p cs q x y -> state_valid p x ->
  final_state y v -> final_state x v.
Proof.
  intros Hinline Hmatch Hvalid Hfinal.
  destruct Hmatch as
    [stk stk' fi f f' pc rs rs' Hstacks Hother Hregs Hf Hf'|
     stk stk' dst retpc rsc rsc' pc rscallee rs' caller'
       Hstacks Hregs Hcaller Hcall Hregs' Hcallee Hcaller'].
  - destruct Hfinal as (f0 & pc0 & rs0 & ret & Hstate & Hret & Hv).
    inversion Hstate; subst. inversion Hstacks; subst.
    simpl in Hvalid. destruct Hvalid as [[instr Hcode] _].
    assert (Hdistinct : fi <> cs_caller cs \/ pc0 <> cs_pc cs).
    { destruct (Nat.eq_dec fi (cs_caller cs)) as [Heq|Hne]; [|auto].
      right. intros Hpc. subst fi pc0.
      pose proof (cs_pc_in_p' p cs q Hinline f0 Hf') as Hnop. congruence. }
    pose proof (code_at_pc_preserved p cs q Hinline fi f f0 pc0 instr
      Hf Hf' Hdistinct Hcode) as Hcode'.
    assert (instr = Iret ret) by congruence. subst instr.
    exists f, pc0, rs, ret. split; [reflexivity|]. split; [assumption|].
    symmetry.
    destruct (Nat.eq_dec fi (cs_caller cs)) as [Heq|Hne].
    + eapply regs_agree_on_instr; [apply Hregs; exact Heq| |exact Hcode|simpl; auto].
      rewrite <- Heq. exact Hf.
    + rewrite <- (Hother Hne). reflexivity.
  - destruct Hfinal as (f0 & pc0 & rs0 & ret & Hstate & Hret & Hv).
    inversion Hstate; subst.
    simpl in Hvalid. destruct Hvalid as [[instr Hcode] _].
    destruct (inlined_body_at p cs q Hinline pc instr Hcode)
      as [f' [Hf' Hcode']].
    assert (f' = f0) by congruence. subst f'.
    destruct instr; simpl in Hcode'; congruence.
Qed.

Lemma bmatch_final_backward p cs q x y v m :
  inline p cs = Some q ->
  bmatch (step q) (match_states p cs q) x y m -> state_valid p x ->
  final_state y v -> final_state x v.
Proof.
  intros Hinline [endstate [Hsteps Hmatch]] Hvalid Hfinal.
  assert (y = endstate) by (eapply final_starN; eauto). subst endstate.
  eapply match_final_backward; eauto.
Qed.

Lemma match_stacks_valid p cs q stk stk' :
  inline p cs = Some q -> match_stacks p cs q stk stk' ->
  stack_valid p stk -> stack_valid q stk'.
Proof.
  intros Hinline Hmatch. induction Hmatch; intros Hvalid; [constructor|].
  inversion Hvalid as [|? ? Hhead Htail]; subst.
  destruct Hhead as [Hpc _]. constructor.
  - split.
    + eapply inline_pc_valid; eauto.
    + eexists; eassumption.
  - apply IHHmatch. exact Htail.
Qed.

Lemma match_states_valid p cs q x y :
  inline p cs = Some q -> match_states p cs q x y ->
  state_valid p x -> state_valid q y.
Proof.
  intros Hinline Hmatch Hvalid.
  destruct Hmatch as
    [stk stk' fi f f' pc rs rs' Hstacks Hother Hregs Hf Hf'|
     stk stk' dst retpc rsc rsc' pc rscallee rs' caller'
       Hstacks Hregs Hcaller Hcall Hregs' Hcallee Hcaller'].
  - simpl in *. destruct Hvalid as [Hpc [_ Hstack]].
    split; [eapply inline_pc_valid; eauto|].
    split; [eauto|]. eapply match_stacks_valid; eauto.
  - simpl in *. destruct Hvalid as [[instr Hcode] [_ Hstack]].
    destruct (inlined_body_at p cs q Hinline pc instr Hcode)
      as [f' [Hf' Hcode']].
    assert (f' = caller') by congruence. subst f'.
    split; [eexists; exact Hcode'|]. split; [eauto|].
    inversion Hstack as [|? ? Hhead Htail]; subst.
    eapply match_stacks_valid; eauto.
Qed.
