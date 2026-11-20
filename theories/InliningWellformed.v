(** Control-flow well-formedness is preserved by each actual inline pass.
    This lets the backward simulation compose without assuming that every
    intermediate program is well formed. *)
From Stdlib Require Import List Arith Lia.
From VerifPerf Require Import Syntax Inlining InliningProof.
Import ListNotations.

Definition code_bounded (bound : nat) (c : code) : Prop :=
  forall instr, In instr c -> forall next,
    In next (instr_successors instr) -> next < bound.

Lemma in_firstn {A} (x : A) n l : In x (firstn n l) -> In x l.
Proof.
  intros H. rewrite <- (firstn_skipn n l). apply in_or_app. left; exact H.
Qed.

Lemma in_skipn {A} (x : A) n l : In x (skipn n l) -> In x l.
Proof.
  intros H. rewrite <- (firstn_skipn n l). apply in_or_app. right; exact H.
Qed.

Lemma pc_valid_iff f pc : pc_valid f pc <-> pc < length (fn_code f).
Proof.
  unfold pc_valid. split.
  - intros [instr H]. apply nth_error_Some. congruence.
  - intros H. destruct (nth_error (fn_code f) pc) eqn:E; eauto.
    apply nth_error_None in E. lia.
Qed.

Lemma wf_function_bounded p fi f :
  wf_program p -> nth_error p fi = Some f ->
  code_bounded (length (fn_code f)) (fn_code f).
Proof.
  intros Hwf Hf instr Hin next Hnext.
  apply In_nth_error in Hin. destruct Hin as [pc Hpc].
  destruct (Hwf fi f pc instr Hf Hpc) as [Hsucc _].
  apply pc_valid_iff. apply Hsucc. exact Hnext.
Qed.

Lemma zero_regs_bounded count ro start bound :
  start + count < bound -> code_bounded bound (zero_regs count ro start).
Proof.
  revert start. induction count as [|count IH]; intros start Hbound instr Hin;
    simpl in Hin; [contradiction|].
  destruct Hin as [<-|Hin].
  - simpl. intros next [<-|[]]. lia.
  - eapply (IH (start + 1)); [lia|exact Hin].
Qed.

Lemma bind_params_bounded args params ro start bound :
  start + length (bind_params args params ro start) < bound ->
  code_bounded bound (bind_params args params ro start).
Proof.
  revert params start. induction args as [|arg args IH];
    intros [|param params] start Hbound instr Hin; simpl in *;
    try contradiction.
  destruct Hin as [<-|Hin].
  - simpl. intros next [<-|[]]. lia.
  - eapply (IH params (start + 1)); [lia|exact Hin].
Qed.

Lemma transformed_body_bounded body ro offset dst succ bound :
  code_bounded (length body) body ->
  offset + length body <= bound -> succ < bound ->
  code_bounded bound (transform_callee_body body ro offset dst succ).
Proof.
  intros Hbody Hlength Hsucc instr Hin next Hnext.
  apply in_map_iff in Hin. destruct Hin as [original [<- Hin]].
  specialize (Hbody original Hin).
  destruct original; simpl in *;
    repeat match goal with
    | H : _ \/ _ |- _ => destruct H as [H|H]; [subst|]
    end; try contradiction;
    first [exact Hsucc | specialize (Hbody _ (or_introl eq_refl)); lia |
      specialize (Hbody _ (or_intror (or_introl eq_refl))); lia].
Qed.

Lemma inline_code_length caller callee pc args dst succ :
  pc < length (fn_code caller) ->
  length (inline_call_site caller callee pc args dst succ) =
    length (fn_code caller) + S (max_reg_func callee) +
    length (bind_params args (fn_params callee) (max_reg_func caller + 1)
      (length (fn_code caller) + S (max_reg_func callee))) +
    length (fn_code callee).
Proof.
  intros Hpc. unfold inline_call_site.
  rewrite !length_app, length_firstn. simpl length.
  rewrite length_skipn, length_zero_regs. unfold transform_callee_body.
  rewrite length_map, Nat.min_l by lia. lia.
Qed.

Lemma inline_code_bounded caller callee pc target args dst succ :
  nth_error (fn_code caller) pc = Some (Icall target args dst succ) ->
  code_bounded (length (fn_code caller)) (fn_code caller) ->
  code_bounded (length (fn_code callee)) (fn_code callee) ->
  0 < length (fn_code callee) ->
  code_bounded (length (inline_call_site caller callee pc args dst succ))
    (inline_call_site caller callee pc args dst succ).
Proof.
  intros Hcall Hcaller Hcallee Hnonempty.
  assert (Hpc : pc < length (fn_code caller)).
  { apply nth_error_Some. congruence. }
  assert (Hsucc : succ < length (fn_code caller)).
  { eapply Hcaller; [eapply nth_error_In; exact Hcall|simpl; auto]. }
  rewrite inline_code_length by assumption.
  unfold inline_call_site. rewrite length_zero_regs.
  set (ro := max_reg_func caller + 1).
  set (start := length (fn_code caller)).
  set (count := S (max_reg_func callee)).
  set (binds := bind_params args (fn_params callee) ro (start + count)).
  set (bound := start + count + length binds + length (fn_code callee)).
  intros instr Hin next Hnext.
  repeat rewrite in_app_iff in Hin.
  destruct Hin as [[[Hin|Hin]|[Hin|Hin]]|Hin].
  - assert (Horiginal : In instr (fn_code caller))
      by (eapply in_firstn; exact Hin).
    specialize (Hcaller instr Horiginal next Hnext). unfold bound, start; lia.
  - destruct Hin as [<-|Hin].
    + simpl in Hnext. destruct Hnext as [<-|[]]. unfold bound, count; lia.
    + assert (Horiginal : In instr (fn_code caller))
        by (eapply in_skipn; exact Hin).
      specialize (Hcaller instr Horiginal next Hnext). unfold bound, start; lia.
  - eapply (zero_regs_bounded count ro start bound);
      [unfold bound; lia|exact Hin|exact Hnext].
  - eapply (bind_params_bounded args (fn_params callee) ro (start + count) bound);
      [unfold bound, binds; lia|exact Hin|exact Hnext].
  - eapply (transformed_body_bounded (fn_code callee) ro
      (start + count + length binds) dst succ bound);
      [exact Hcallee|unfold bound; lia|unfold bound, start; lia|exact Hin|exact Hnext].
Qed.

Lemma zero_regs_no_call count ro start target args dst succ :
  ~ In (Icall target args dst succ) (zero_regs count ro start).
Proof.
  revert start. induction count; intros start; simpl; [tauto|].
  intros [H|H]; [discriminate|]. eapply IHcount; exact H.
Qed.

Lemma bind_params_no_call al params ro start target args dst succ :
  ~ In (Icall target args dst succ) (bind_params al params ro start).
Proof.
  revert params start. induction al; intros [|param params] start;
    simpl; try tauto.
  intros [H|H]; [discriminate|]. eapply IHal; exact H.
Qed.

Lemma inline_code_calls caller callee pc al d s target args dst succ :
  isLeafb callee = true ->
  In (Icall target args dst succ) (inline_call_site caller callee pc al d s) ->
  In (Icall target args dst succ) (fn_code caller).
Proof.
  intros Hleaf Hin. unfold inline_call_site in Hin.
  repeat rewrite in_app_iff in Hin.
  destruct Hin as [[[Hin|Hin]|[Hin|Hin]]|Hin].
  - eapply in_firstn; exact Hin.
  - destruct Hin as [H|Hin]; [discriminate|]. eapply in_skipn; exact Hin.
  - exfalso. eapply zero_regs_no_call; exact Hin.
  - exfalso. eapply bind_params_no_call; exact Hin.
  - apply in_map_iff in Hin. destruct Hin as [instr [Heq Hin]].
    destruct instr; simpl in Heq; try discriminate.
    unfold isLeafb in Hleaf. rewrite forallb_forall in Hleaf.
    specialize (Hleaf _ Hin). discriminate.
Qed.

Lemma inline_shape p cs q : inline p cs = Some q ->
  exists caller target args dst succ callee,
    nth_error p (cs_caller cs) = Some caller /\
    nth_error (fn_code caller) (cs_pc cs) = Some (Icall target args dst succ) /\
    nth_error p target = Some callee /\ isLeafb callee = true /\
    q = firstn (cs_caller cs) p ++
      mk_function (fn_params caller)
        (inline_call_site caller callee (cs_pc cs) args dst succ) ::
      skipn (cs_caller cs + 1) p.
Proof.
  intros H. unfold inline in H.
  destruct (nth_error p (cs_caller cs)) as [caller|] eqn:Hcaller; try discriminate.
  destruct (nth_error (fn_code caller) (cs_pc cs)) as [instr|] eqn:Hcall;
    try discriminate.
  destruct instr; try discriminate.
  destruct (nth_error p target_func) as [callee|] eqn:Hcallee; try discriminate.
  destruct (isLeafb callee) eqn:Hleaf; try discriminate.
  unfold inline_in_func in H. rewrite Hcall in H. inversion H; subst q.
  exists caller, target_func, args, dst, succ, callee. repeat split; auto.
Qed.

Lemma inline_lookup_source p cs q fi f' :
  inline p cs = Some q -> nth_error q fi = Some f' ->
  exists f, nth_error p fi = Some f /\
    length (fn_code f) <= length (fn_code f').
Proof.
  intros Hinline Hf'.
  destruct (inline_shape p cs q Hinline) as
    (caller & target & args & dst & succ & callee & Hcaller & Hcall & Hcallee & Hleaf & ->).
  assert (Hcaller_lt : cs_caller cs < length p).
  { apply nth_error_Some. congruence. }
  destruct (Nat.eq_dec fi (cs_caller cs)) as [->|Hne].
  - rewrite nth_error_replace_same in Hf' by assumption. inversion Hf'; subst f'.
    exists caller. split; [assumption|]. simpl.
    rewrite inline_code_length; [lia|]. apply nth_error_Some. congruence.
  - assert (Hlen : length (firstn (cs_caller cs) p ++
        mk_function (fn_params caller)
          (inline_call_site caller callee (cs_pc cs) args dst succ) ::
        skipn (cs_caller cs + 1) p) = length p).
    { apply length_replace_nth. assumption. }
    rewrite nth_error_replace_other in Hf'.
    + exists f'. split; [assumption|lia].
    + assumption.
    + rewrite <- Hlen. apply nth_error_Some. congruence.
Qed.

Lemma inline_pc_valid p cs q fi f f' pc :
  inline p cs = Some q -> nth_error p fi = Some f ->
  nth_error q fi = Some f' -> pc_valid f pc -> pc_valid f' pc.
Proof.
  intros Hinline Hf Hf' Hpc.
  destruct (inline_lookup_source p cs q fi f' Hinline Hf') as [f0 [Hf0 Hlen]].
  assert (f0 = f) by congruence. subst f0.
  apply pc_valid_iff in Hpc. apply pc_valid_iff. lia.
Qed.

Theorem inline_preserves_wf p cs q :
  inline p cs = Some q -> wf_program p -> wf_program q.
Proof.
  intros Hinline Hwf fi f' pc instr Hf' Hcode.
  destruct (inline_lookup_source p cs q fi f' Hinline Hf') as [f [Hf Hlength]].
  assert (Hbounded : code_bounded (length (fn_code f')) (fn_code f')).
  { destruct (Nat.eq_dec fi (cs_caller cs)) as [Heq|Hne].
    - subst fi.
      destruct (inline_shape p cs q Hinline) as
        (caller & target & args & dst & succ & callee & Hcaller & Hcall & Hcallee & Hleaf & Hshape).
      rewrite Hshape, nth_error_replace_same in Hf'
        by (apply nth_error_Some; congruence).
      inversion Hf'; subst f'. simpl.
      destruct (Hwf _ _ _ _ Hcaller Hcall) as [_ [fd [Hfd Hentry]]].
      assert (fd = callee) by congruence. subst fd.
      eapply inline_code_bounded; eauto using wf_function_bounded.
      apply pc_valid_iff in Hentry. exact Hentry.
    - assert (Hsame : nth_error q fi = Some f).
      { eapply other_func_preserved; eauto. apply nth_error_Some. congruence. }
      assert (f' = f) by congruence. subst f'. eapply wf_function_bounded; eauto. }
  split.
  - intros next Hnext. apply pc_valid_iff.
    eapply Hbounded; [eapply nth_error_In; exact Hcode|exact Hnext].
  - destruct instr; try exact I.
    assert (Horiginal : In (Icall target_func args dst succ) (fn_code f)).
    { destruct (Nat.eq_dec fi (cs_caller cs)) as [Heq|Hne].
      - subst fi.
        destruct (inline_shape p cs q Hinline) as
          (caller & target & al & d & s & callee & Hcaller & Hcall & Hcallee & Hleaf & Hshape).
        assert (f = caller) by congruence. subst f.
        rewrite Hshape, nth_error_replace_same in Hf'
          by (apply nth_error_Some; congruence).
        inversion Hf'; subst f'. eapply inline_code_calls; [exact Hleaf|].
        eapply nth_error_In; exact Hcode.
      - assert (Hsame : nth_error q fi = Some f).
        { eapply other_func_preserved; eauto. apply nth_error_Some. congruence. }
        assert (f' = f) by congruence. subst f'. eapply nth_error_In; exact Hcode. }
    apply In_nth_error in Horiginal. destruct Horiginal as [oldpc Hold].
    destruct (Hwf _ _ _ _ Hf Hold) as [_ [fd [Hfd Hentry]]].
    destruct (find_func_preserved p cs q Hinline target_func fd Hfd)
      as [Hfd'|[_ [fd' Hfd']]].
    + exists fd. auto.
    + exists fd'. split; [assumption|]. eapply inline_pc_valid; eauto.
Qed.
