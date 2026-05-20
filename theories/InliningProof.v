From VerifPerf Require Import Syntax Semantics Inlining.
From Stdlib Require Import List Nat Bool Relations Arith Lia.
From Stdlib Require Import PeanoNat.
Import ListNotations.

Section INLINING_PROOF.

Variable p : program.
Variable cs : callsite.
Variable p' : program.
Hypothesis Hinline : inline p cs = Some p'.

(* The callee function that was inlined *)
Let callee := match nth_error p (cs_target cs) with
              | Some f => f
              | None => mk_function [] [] 0
              end.

Let caller := match nth_error p (cs_caller cs) with
              | Some f => f
              | None => mk_function [] [] 0
              end.

Let reg_offset := max_reg_func caller + 1.

(* Node offset: where the callee body starts in the inlined code *)
Let call_args := match nth_error (fn_code caller) (cs_pc cs) with
                 | Some (Icall _ args _ _) => args
                 | _ => []
                 end.

Let node_offset := length (fn_code caller) +
                   length (bind_params call_args (fn_params callee)
                             reg_offset (length (fn_code caller))).

(* Register agreement: source and target registers agree on the caller's registers.
   The inlined code uses registers above reg_offset, which the caller never touches. *)
Definition regs_agree (rs_src rs_tgt : regset) : Prop :=
  forall r, r <= max_reg_func caller -> rs_src r = rs_tgt r.

(* Stack matching: relates source stack (which has a frame for the inlined call)
   to target stack (which does not). *)
Inductive match_stacks : list stackframe -> list stackframe -> Prop :=
  | match_stacks_nil :
      match_stacks nil nil
  | match_stacks_cons : forall dst f pc rs_src rs_tgt s_src s_tgt,
      regs_agree rs_src rs_tgt ->
      match_stacks s_src s_tgt ->
      match_stacks (Stackframe dst f pc rs_src :: s_src)
                   (Stackframe dst f pc rs_tgt :: s_tgt)
.

(* match_states relates a source state (executing p) to a target state (executing p').
   Two cases:
   1. Normal: both programs are at corresponding points
   2. Inside inlined code: source has pushed a frame and is inside the callee,
      while target is still in the caller executing the spliced-in code *)
Inductive match_states : state -> state -> Prop :=
  (* Both executing the same function at the same pc *)
  | match_normal : forall s_src s_tgt fi f_src f_tgt pc rs_src rs_tgt,
      match_stacks s_src s_tgt ->
      regs_agree rs_src rs_tgt ->
      
      (* funcs may be different (due to inlining of a callsite),
        but the indices are equal *)
      nth_error p fi = Some f_src ->
      nth_error p' fi = Some f_tgt ->

      match_states (State s_src f_src (* same pc *) pc rs_src)
                   (State s_tgt f_tgt (* same pc *) pc rs_tgt)

  (* Source is inside the callee (has pushed a stack frame),
     target is executing the inlined body within the caller *)
  | match_inlined : forall s_src s_tgt
      (dst : reg) (ret_pc : node) (rs_caller_src rs_caller_tgt : regset)
      (pc_callee : node) (rs_callee_src rs_tgt : regset),
      (* Stacks below the inlined frame correspond *)
      match_stacks s_src s_tgt ->
      (* Caller registers agreed before the call *)
      regs_agree rs_caller_src rs_caller_tgt ->
      (* Target registers agree with callee's on the remapped registers *)
      (forall r, rs_callee_src r = rs_tgt (r + reg_offset)) ->
      (* Target is at the corresponding inlined node *)
      match_states
        (* the source is executing inside the callee at
           node pc_callee *)
        (State ((Stackframe dst caller ret_pc rs_caller_src) :: s_src)
               callee pc_callee rs_callee_src)

        (* the target is executing in the caller at the
           corresponding inlined node *)
        (State s_tgt caller (pc_callee + node_offset) rs_tgt)

  (* Both in a callstate (for calls other than the inlined one) *)
  | match_callstate : forall s_src s_tgt f args,
      match_stacks s_src s_tgt ->
      match_states (Callstate s_src f args)
                   (Callstate s_tgt f args)

  (* Both in a returnstate (for returns other than from the inlined callee) *)
  | match_returnstate : forall s_src s_tgt v,
      match_stacks s_src s_tgt ->
      match_states (Returnstate s_src v)
                   (Returnstate s_tgt v)
.

Ltac inv H := inversion H; subst; clear H.

Inductive plus (step : state -> state -> Prop) : state -> state -> Prop :=
   | plus_one : forall s1 s2,
      step s1 s2 -> plus step s1 s2
   | plus_step : forall s1 s2 s3,
      step s1 s2 -> plus step s2 s3 -> plus step s1 s3.

(* Tactic to unpack the inline hypothesis without destroying it.
   Introduces: Htarget, Hleaf, Hcaller_lookup, Hinl_func, Hp' *)
Ltac unpack_inline :=
  let H := fresh "Hinl" in
  pose proof Hinline as H;
  unfold inline in H;
  destruct (nth_error p (cs_target cs)) as [callee_f|] eqn:Htarget; [|discriminate];
  destruct (isLeafb callee_f) eqn:Hleaf; [|discriminate];
  destruct (nth_error p (cs_caller cs)) as [caller_f|] eqn:Hcaller_lookup; [|discriminate];
  destruct (inline_in_func caller_f callee_f (cs_pc cs)) as [caller_f'|] eqn:Hinl_func; [|discriminate];
  assert (Hp' : p' = firstn (cs_caller cs) p ++ [caller_f'] ++ skipn (cs_caller cs + 1) p)
    by congruence;
  clear H.

(* Functions not at cs_caller are identical in p and p' *)
Lemma other_func_preserved : forall i f,
  i <> cs_caller cs ->
  i < length p ->
  nth_error p i = Some f ->
  nth_error p' i = Some f.
Proof.
  intros i f hNotCS hLen hf.
  unpack_inline. rewrite Hp'.
  replace (caller_f' :: skipn (cs_caller cs + 1) p)
    with ([caller_f'] ++ skipn (cs_caller cs + 1) p) by reflexivity.
  rewrite nth_error_replace_other; assumption.
Qed.

(* The modified caller exists in p' *)
Lemma caller_in_p' : exists caller',
  nth_error p' (cs_caller cs) = Some caller'.
Proof.
  unpack_inline. rewrite Hp'.
  eexists.
  replace (caller_f' :: skipn (cs_caller cs + 1) p)
    with ([caller_f'] ++ skipn (cs_caller cs + 1) p) by reflexivity.
  apply nth_error_replace_same.
  apply nth_error_Some. congruence.
Qed.

(* Instructions in the caller at PCs other than cs_pc are preserved *)
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
  assert (Hpc_bound : pc < length (fn_code caller_f))
    by (apply nth_error_Some; congruence).
  assert (Hcs_bound : cs_pc cs < length (fn_code caller_f))
    by (apply nth_error_Some; congruence).
  rewrite Hp'.
  eexists. split.
  - change (?x :: ?rest) with ([x] ++ rest).
    apply nth_error_replace_same. apply nth_error_Some. congruence.
  - rewrite <- Hcf'. simpl. unfold inline_call_site.
    rewrite nth_error_app1.
    + rewrite nth_error_replace_other; auto.
    + assert (length (firstn (cs_pc cs) (fn_code caller_f) ++
              [Inop (length (fn_code caller_f))] ++
              skipn (cs_pc cs + 1) (fn_code caller_f)) = length (fn_code caller_f)).
      { rewrite !length_app, length_firstn, length_skipn. simpl. lia. }
      lia.
Qed.

(* The inlined program preserves function lookup for non-inlined calls *)
Lemma find_func_preserved : forall target fd,
  nth_error p target = Some fd ->
  nth_error p' target = Some fd \/
  (target = cs_caller cs /\ exists fd', nth_error p' target = Some fd').
Proof.
  intros target fd Hlookup.
  destruct (Nat.eq_dec target (cs_caller cs)) as [Heq | Hneq].
  - right. split; auto. destruct caller_in_p' as [c' Hc']. rewrite Heq. eauto.
  - left. eapply other_func_preserved; eauto. apply nth_error_Some. congruence.
Qed.

(* Code at a pc is preserved if it's not the inlined site in the caller *)
Lemma code_at_pc_preserved : forall fi f_src f_tgt pc instr,
  nth_error p fi = Some f_src ->
  nth_error p' fi = Some f_tgt ->
  (fi <> cs_caller cs \/ pc <> cs_pc cs) ->
  nth_error (fn_code f_src) pc = Some instr ->
  nth_error (fn_code f_tgt) pc = Some instr.
Proof.
  intros fi f_src f_tgt pc instr Hsrc Htgt Hdisj Hcode.
  destruct (Nat.eq_dec fi (cs_caller cs)) as [Heq | Hneq].
  - (* fi = cs_caller cs: must have pc <> cs_pc cs *)
    assert (Hpc : pc <> cs_pc cs) by (destruct Hdisj; congruence).
    subst fi.
    destruct (other_pc_preserved pc instr Hpc) as [c' [Hc' Hinstr]].
    + unfold caller. rewrite Hsrc. exact Hcode.
    + congruence.
  - (* fi <> cs_caller cs: whole function unchanged *)
    replace f_tgt with f_src by
      (assert (nth_error p' fi = Some f_src) by
        (apply other_func_preserved; auto; apply nth_error_Some; congruence);
       congruence).
    exact Hcode.
Qed.

(* The main (forward) simulation theorem: If source steps and states match,
   then target steps (possibly multiple) and the resulting states match. *)
Theorem step_simulation:
   forall s1 s1' s2,
   match_states s1 s2 ->
   step p s1 s1' ->
   exists s2', plus (step p') s2 s2' /\ match_states s1' s2'.
Proof.
  (* dispatch the easy cases - normal state + one step *)
  intros s1 s1' s2 Hmatch Hstep.
  inv Hmatch; inv Hstep; try (eexists; split;
    [ apply plus_one; econstructor; eauto
    | econstructor; eauto ]; fail).

  - (* exec_Icall at normal : case split on whether this is the inlined site *)
    destruct (Nat.eq_dec pc (cs_pc cs)) as [Hinl | Hnotinl].
    + (* This IS the inlined call site *)
      admit.
    + (* This is a different call site -- target takes the same Icall step *)
      admit.

  - (* exec_Iret at normal *)
    admit.

  - (* exec_return at match_returnstate *)
    admit.

  - (* exec_Inop inside inlined body *)
    admit.

  - (* exec_Iop inside inlined body *)
    admit.

  - (* exec_Icond_true inside inlined body *)
    admit.

  - (* exec_Icond_false inside inlined body *)
    admit.

  - (* exec_Icall inside inlined body : impossible, callee is leaf *)
    exfalso. admit.

  - (* exec_Iret inside inlined body : return from inlined callee *)
    admit.
Admitted.

End INLINING_PROOF.
