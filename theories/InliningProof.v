From VerifPerf Require Import Syntax Semantics Inlining.
From Stdlib Require Import List Nat Bool Relations Arith Lia PeanoNat.
Import ListNotations.

Section INLINING_PROOF.

Variable p : program.
Variable cs : callsite.
Variable p' : program.
Hypothesis Hinline : inline p cs = Some p'.

Let callee := match nth_error p (cs_target cs) with
              | Some f => f
              | None => mk_function [] [] 0
              end.

Let caller := match nth_error p (cs_caller cs) with
              | Some f => f
              | None => mk_function [] [] 0
              end.

Let reg_offset := max_reg_func caller + 1.

Let call_args := match nth_error (fn_code caller) (cs_pc cs) with
                 | Some (Icall _ args _ _) => args
                 | _ => []
                 end.

Let node_offset := length (fn_code caller) +
                   length (bind_params call_args (fn_params callee)
                             reg_offset (length (fn_code caller))).

Definition regs_agree (rs_src rs_tgt : regset) : Prop :=
  forall r, r <= max_reg_func caller -> rs_src r = rs_tgt r.

Inductive match_stacks : list stackframe -> list stackframe -> Prop :=
  | match_stacks_nil :
      match_stacks nil nil
  | match_stacks_cons : forall dst f pc rs_src rs_tgt s_src s_tgt,
      regs_agree rs_src rs_tgt ->
      match_stacks s_src s_tgt ->
      match_stacks (Stackframe dst f pc rs_src :: s_src)
                   (Stackframe dst f pc rs_tgt :: s_tgt).

Inductive match_states : state -> state -> Prop :=
  | match_normal : forall s_src s_tgt fi f_src f_tgt pc rs_src rs_tgt,
      match_stacks s_src s_tgt ->
      regs_agree rs_src rs_tgt ->
      nth_error p fi = Some f_src ->
      nth_error p' fi = Some f_tgt ->
      match_states (State s_src f_src pc rs_src)
                   (State s_tgt f_tgt pc rs_tgt)
  | match_inlined : forall s_src s_tgt
      (dst : reg) (ret_pc : node) (rs_caller_src rs_caller_tgt : regset)
      (pc_callee : node) (rs_callee_src rs_tgt : regset),
      match_stacks s_src s_tgt ->
      regs_agree rs_caller_src rs_caller_tgt ->
      (forall r, rs_callee_src r = rs_tgt (r + reg_offset)) ->
      match_states
        (State ((Stackframe dst caller ret_pc rs_caller_src) :: s_src)
               callee pc_callee rs_callee_src)
        (State s_tgt caller (pc_callee + node_offset) rs_tgt)
  | match_callstate : forall s_src s_tgt f args,
      match_stacks s_src s_tgt ->
      match_states (Callstate s_src f args)
                   (Callstate s_tgt f args)
  | match_returnstate : forall s_src s_tgt v,
      match_stacks s_src s_tgt ->
      match_states (Returnstate s_src v)
                   (Returnstate s_tgt v).

(** * Tactics *)

Ltac inv H := inversion H; subst; clear H.

Ltac unpack_inline :=
  let H := fresh "Hinl" in
  pose proof Hinline as H;
  unfold inline in H;
  destruct (nth_error p (cs_target cs)) as [callee_f|] eqn:Htarget; [|discriminate];
  destruct (isLeafb callee_f) eqn:Hleaf; [|discriminate];
  destruct (nth_error p (cs_caller cs)) as [caller_f|] eqn:Hcaller_lookup; [|discriminate];
  destruct (inline_in_func caller_f callee_f (cs_pc cs)) as [caller_f'|] eqn:Hinl_func; [|discriminate];
  assert (Hp' : p' = firstn (cs_caller cs) p ++ caller_f' :: skipn (cs_caller cs + 1) p)
    by (change (caller_f' :: skipn (cs_caller cs + 1) p)
          with ([caller_f'] ++ skipn (cs_caller cs + 1) p); congruence);
  clear H.

Ltac nth_error_some_lt :=
  match goal with
  | [ H : nth_error ?l ?n = Some _ |- ?n < length ?l ] =>
      apply nth_error_Some; congruence
  | [ H : nth_error ?l ?n = Some _ |- _ < length ?l ] =>
      apply nth_error_Some; congruence
  end.


(** * Preservation lemmas *)

Inductive plus (step : state -> state -> Prop) : state -> state -> Prop :=
  | plus_one : forall s1 s2, step s1 s2 -> plus step s1 s2
  | plus_step : forall s1 s2 s3, step s1 s2 -> plus step s2 s3 -> plus step s1 s3.

Lemma other_func_preserved : forall i f,
  i <> cs_caller cs ->
  i < length p ->
  nth_error p i = Some f ->
  nth_error p' i = Some f.
Proof.
  intros i f hNotCS hLen hf. unpack_inline. rewrite Hp'.
  rewrite nth_error_replace_other; assumption.
Qed.

Lemma caller_in_p' : exists caller',
  nth_error p' (cs_caller cs) = Some caller'.
Proof.
  unpack_inline. rewrite Hp'. eexists.
  apply nth_error_replace_same. nth_error_some_lt.
Qed.

Lemma other_pc_preserved : forall pc i,
  pc <> cs_pc cs ->
  nth_error (fn_code caller) pc = Some i ->
  exists caller', nth_error p' (cs_caller cs) = Some caller' /\
                  nth_error (fn_code caller') pc = Some i.
Proof.
  intros pc i Hpc Hi. unpack_inline.
  unfold inline_in_func in Hinl_func.
  change (fn_code caller) with (fn_code caller_f) in Hi.
  destruct (nth_error (fn_code caller_f) (cs_pc cs)) as [[]|] eqn:Hcall;
    try discriminate.
  injection Hinl_func as Hcf'.
  rewrite Hp'. eexists. split.
  - apply nth_error_replace_same. apply nth_error_Some. congruence.
  - rewrite <- Hcf'. simpl. unfold inline_call_site.
    assert (Hpc_bound : pc < length (fn_code caller_f))
      by (apply nth_error_Some; congruence).
    assert (Hcs_bound : cs_pc cs < length (fn_code caller_f))
      by (apply nth_error_Some; congruence).
    assert (Hpatch_len :
      length (firstn (cs_pc cs) (fn_code caller_f) ++
              Inop (length (fn_code caller_f)) ::
              skipn (cs_pc cs + 1) (fn_code caller_f)) =
      length (fn_code caller_f)).
    { rewrite length_app. simpl. rewrite length_skipn, length_firstn. lia. }
    rewrite nth_error_app1 by lia.
    rewrite nth_error_replace_other; auto.
Qed.

Lemma find_func_preserved : forall target fd,
  nth_error p target = Some fd ->
  nth_error p' target = Some fd \/
  (target = cs_caller cs /\ exists fd', nth_error p' target = Some fd').
Proof.
  intros target fd Hlookup.
  destruct (Nat.eq_dec target (cs_caller cs)) as [Heq | Hneq].
  - right. split; auto. destruct caller_in_p' as [c' Hc']. rewrite Heq. eauto.
  - left. apply other_func_preserved; auto. nth_error_some_lt.
Qed.

Lemma code_at_pc_preserved : forall fi f_src f_tgt pc instr,
  nth_error p fi = Some f_src ->
  nth_error p' fi = Some f_tgt ->
  (fi <> cs_caller cs \/ pc <> cs_pc cs) ->
  nth_error (fn_code f_src) pc = Some instr ->
  nth_error (fn_code f_tgt) pc = Some instr.
Proof.
  intros fi f_src f_tgt pc instr Hsrc Htgt Hdisj Hcode.
  destruct (Nat.eq_dec fi (cs_caller cs)) as [Heq | Hneq].
  - assert (Hpc : pc <> cs_pc cs) by (destruct Hdisj; congruence).
    subst fi.
    destruct (other_pc_preserved pc instr Hpc) as [c' [Hc' Hinstr]].
    + unfold caller. rewrite Hsrc. exact Hcode.
    + congruence.
  - replace f_tgt with f_src by
      (assert (nth_error p' fi = Some f_src) by
        (apply other_func_preserved; auto; nth_error_some_lt);
       congruence).
    exact Hcode.
Qed.

(** * Forward simulation *)

Theorem step_simulation:
  forall s1 s1' s2,
    match_states s1 s2 ->
    step p s1 s1' ->
    exists s2', plus (step p') s2 s2' /\ match_states s1' s2'.
Proof.
  intros s1 s1' s2 Hmatch Hstep.
  inv Hmatch; inv Hstep; try (eexists; split;
    [ apply plus_one; econstructor; eauto
    | econstructor; eauto ]; fail).

  - (* exec_Icall at normal *)
    destruct (Nat.eq_dec pc (cs_pc cs)) as [Hinl | Hnotinl].
    + (* inlined call site *) admit.
    + (* different call site *) 
      eexists. split; 
      try (apply plus_one; econstructor; eauto). 
      apply (code_at_pc_preserved fi f_src _ _ ((Inop pc'))); try assumption.
      right. assumption. apply (match_normal _ _ fi _ _ _ _ _); assumption.
 
  - (* exec_Iret at normal *) admit.

  - (* exec_return at match_returnstate *) admit.
  - (* exec_Inop inside inlined body *) admit.
  - (* exec_Iop inside inlined body *) admit.
  - (* exec_Icond_true inside inlined body *) admit.
  - (* exec_Icond_false inside inlined body *) admit.
  - (* exec_Icall inside inlined body: impossible *) exfalso. admit.
  - (* exec_Iret inside inlined body *) admit.
Admitted.

End INLINING_PROOF.
