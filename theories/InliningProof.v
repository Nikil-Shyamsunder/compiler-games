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
  | match_stacks_cons : forall dst fi f_src f_tgt pc rs_src rs_tgt s_src s_tgt,
      regs_agree rs_src rs_tgt ->
      nth_error p fi = Some f_src ->
      nth_error p' fi = Some f_tgt ->
      match_stacks s_src s_tgt ->
      match_stacks (Stackframe dst f_src pc rs_src :: s_src)
                   (Stackframe dst f_tgt pc rs_tgt :: s_tgt).

Inductive match_states : state -> state -> Prop :=
  (* TODO: potentially needs strengthening?
  for fi <> cs_caller cs, rs_src = rs_tgt strictly
  for fi = cs_caller cs, regs_agree rs_src rs_tgt 
  *)
  | match_normal : forall s_src s_tgt fi f_src f_tgt pc rs_src rs_tgt,
      match_stacks s_src s_tgt ->
      (fi <> cs_caller cs -> rs_src = rs_tgt) ->
      (fi = cs_caller cs -> regs_agree rs_src rs_tgt) ->
      nth_error p fi = Some f_src ->
      nth_error p' fi = Some f_tgt ->
      match_states (State s_src f_src pc rs_src)
                   (State s_tgt f_tgt pc rs_tgt)
  | match_inlined : forall s_src s_tgt
      (dst : reg) (ret_pc : node) (rs_caller_src rs_caller_tgt : regset)
      (pc_callee : node) (rs_callee_src rs_tgt : regset) caller_tgt,
      match_stacks s_src s_tgt ->
      regs_agree rs_caller_src rs_caller_tgt ->
      (forall r, rs_callee_src r = rs_tgt (r + reg_offset)) ->
      nth_error p' (cs_caller cs) = Some caller_tgt ->
      match_states
        (State ((Stackframe dst caller ret_pc rs_caller_src) :: s_src)
               callee pc_callee rs_callee_src)
        (State s_tgt caller_tgt (pc_callee + node_offset) rs_tgt)
  | match_callstate : forall s_src s_tgt fi f_src f_tgt args,
      match_stacks s_src s_tgt ->
      nth_error p fi = Some f_src ->
      nth_error p' fi = Some f_tgt ->
      match_states (Callstate s_src f_src args)
                   (Callstate s_tgt f_tgt args)
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

(* The instruction at cs_pc is always an Icall *)
Lemma cs_pc_is_call : forall f_src,
  nth_error p (cs_caller cs) = Some f_src ->
  exists target args dst succ,
    nth_error (fn_code f_src) (cs_pc cs) = Some (Icall target args dst succ).
Proof.
  intros f_src Hf. unpack_inline.
  unfold inline_in_func in Hinl_func.
  replace f_src with caller_f by congruence.
  destruct (nth_error (fn_code caller_f) (cs_pc cs)) as [[]|] eqn:E;
    try discriminate.
  eauto.
Qed.

(* Non-Icall instructions can't be at cs_pc in the caller *)
Lemma pc_ne_cs_pc : forall fi f_src pc instr,
  nth_error p fi = Some f_src ->
  nth_error (fn_code f_src) pc = Some instr ->
  (forall t a d s, instr <> Icall t a d s) ->
  fi <> cs_caller cs \/ pc <> cs_pc cs.
Proof.
  intros fi f_src pc instr Hfi Hpc Hnot_call.
  destruct (Nat.eq_dec fi (cs_caller cs)) as [Heq | Hneq]; [|left; auto].
  right. subst fi.
  destruct (cs_pc_is_call f_src Hfi) as [t [a [d [s Hcall]]]].
  intro Heq. subst pc. rewrite Hpc in Hcall.
  injection Hcall. intros. subst. eapply Hnot_call. reflexivity.
Qed.

(* common tacttic for both entrypoint and params
preservation (handles any field). TODO:
is there a cleaner way to do this? *)
Ltac solve_inline_preserves_field :=
  intros fi f_src f_tgt hFsrc hFtgt;
  destruct (Nat.eq_dec fi (cs_caller cs)) as [Heq | Hneq];
  [ subst fi; unpack_inline;
    match goal with
    | [ Hcl : nth_error p (cs_caller cs) = Some ?cf,
        Hinl : inline_in_func ?cf _ _ = Some ?cf' |- _ ] =>
        replace f_src with cf by congruence;
        unfold inline_in_func in Hinl;
        destruct (nth_error (fn_code cf) (cs_pc cs)) as [instr|] eqn:hInstr; try discriminate;
        destruct instr; try discriminate;
        injection Hinl as Hinl;
        replace f_tgt with cf';
        [ rewrite <- Hinl; reflexivity
        | match goal with
          | [ Hp : p' = firstn _ _ ++ ?cf' :: _ |- _ ] =>
              assert (nth_error p' (cs_caller cs) = Some cf') by
                (rewrite Hp; apply nth_error_replace_same, nth_error_Some; congruence);
              congruence
          end ]
    end
  | replace f_tgt with f_src by
      (assert (nth_error p' fi = Some f_src) by
        (apply other_func_preserved; auto; apply nth_error_Some; congruence);
        congruence);
    reflexivity ].

Lemma inline_preserves_entrypoint : forall fi f_src f_tgt,
  nth_error p fi = Some f_src ->
  nth_error p' fi = Some f_tgt ->
  fn_entrypoint f_src = fn_entrypoint f_tgt.
Proof. solve_inline_preserves_field. Qed.

Lemma inline_preserves_params : forall fi f_src f_tgt,
  nth_error p fi = Some f_src ->
  nth_error p' fi = Some f_tgt ->
  fn_params f_src = fn_params f_tgt.
Proof. solve_inline_preserves_field. Qed.

(* TODO: this proof is so ugly. *)
Lemma inlined_body_at : forall pc_callee instr,
  nth_error (fn_code callee) pc_callee = Some instr ->
  exists caller_f' dst succ,
    nth_error p' (cs_caller cs) = Some caller_f' /\
    nth_error (fn_code caller_f') (pc_callee + node_offset) =
      Some (replace_ret (remap_nodes node_offset (remap_regs reg_offset instr))
                        reg_offset dst succ).
Proof.
  intros pc_callee instr Hinstr.
  unpack_inline.
  unfold inline_in_func in Hinl_func.
  destruct (nth_error (fn_code caller_f) (cs_pc cs)) as [ci|] eqn:Hci;
    try discriminate.
  destruct ci as [| | | ? cargs cdst csucc | ]; try discriminate.
  injection Hinl_func as Hcf'.
  assert (Hcaller_f' : nth_error p' (cs_caller cs) = Some caller_f').
  { rewrite Hp'. apply nth_error_replace_same. nth_error_some_lt. }
  exists caller_f', cdst, csucc. split; [exact Hcaller_f' |].
  rewrite <- Hcf'. simpl.
  unfold inline_call_site.
  set (ro := max_reg_func caller_f + 1).
  set (no := length (fn_code caller_f)).
  set (pb := bind_params cargs (fn_params callee_f) ro no).
  set (cb := transform_callee_body (fn_code callee_f) ro (no + length pb) cdst csucc).
  set (pc := firstn (cs_pc cs) (fn_code caller_f)
             ++ Inop no :: skipn (cs_pc cs + 1) (fn_code caller_f)).
  assert (Hcs_bound : cs_pc cs < length (fn_code caller_f))
    by (apply nth_error_Some; congruence).
  assert (Hpc_len : length pc = length (fn_code caller_f)).
  { unfold pc. rewrite length_app. simpl. rewrite length_skipn, length_firstn. lia. }
  change (fn_code callee) with (fn_code callee_f) in Hinstr.
  change reg_offset with ro.
  assert (Hca : call_args = cargs).
  { unfold call_args. change (fn_code caller) with (fn_code caller_f).
    rewrite Hci. reflexivity. }
  assert (Hno : node_offset = no + length pb).
  { unfold node_offset.
    change (fn_code caller) with (fn_code caller_f).
    change (fn_params callee) with (fn_params callee_f).
    rewrite Hca. reflexivity. }
  rewrite Hno.
  rewrite app_assoc.
  rewrite nth_error_app2.
  2: { rewrite length_app, Hpc_len. unfold no. lia. }
  rewrite length_app, Hpc_len.
  replace (pc_callee + (no + length pb) - (length (fn_code caller_f) + length pb))
    with pc_callee by (unfold no; lia).
  unfold cb, transform_callee_body.
  rewrite nth_error_map.
  rewrite Hinstr. simpl.
  unfold no. reflexivity.
Qed.

Ltac solve_code_preserved :=
  eapply code_at_pc_preserved; eauto;
  eapply pc_ne_cs_pc; eauto; intros; discriminate.

(* When regs_agree and we're in the caller, registers used in an instruction agree *)
Lemma regs_agree_on_instr : forall rs_src rs_tgt f pc instr r,
  regs_agree rs_src rs_tgt ->
  nth_error p (cs_caller cs) = Some f ->
  nth_error (fn_code f) pc = Some instr ->
  In r (used_regs instr) ->
  rs_src r = rs_tgt r.
Proof.
  intros rs_src rs_tgt f pc instr r Hagree Hf Hpc Hin.
  apply Hagree.
  assert (r <= max_reg_func f) by (eapply instr_regs_bounded; eauto).
  unfold caller. rewrite Hf. exact H.
Qed.

Lemma regs_agree_update : forall rs_src rs_tgt dst v,
  regs_agree rs_src rs_tgt ->
  regs_agree (update rs_src dst v) (update rs_tgt dst v).
Proof.
  unfold regs_agree, update. intros.
  destruct (Nat.eqb r dst); auto.
Qed.

Lemma map_regs_agree : forall rs_src rs_tgt f pc instr args,
  regs_agree rs_src rs_tgt ->
  nth_error p (cs_caller cs) = Some f ->
  nth_error (fn_code f) pc = Some instr ->
  (forall r, In r args -> In r (used_regs instr)) ->
  map_regs rs_src args = map_regs rs_tgt args.
Proof.
  intros. unfold map_regs. apply map_ext_in. intros r Hr.
  eapply regs_agree_on_instr; eauto.
Qed.

(* For non-caller functions, rs_src = rs_tgt *)
Ltac solve_rs_eq :=
  match goal with
  | [ H : ?fi <> cs_caller cs -> ?rs_src = ?rs_tgt,
      Hneq : ?fi <> cs_caller cs |- _ ] =>
      let Hrs := fresh "Hrs" in
      assert (Hrs : rs_src = rs_tgt) by auto; subst rs_tgt
  end.

(** * Forward simulation *)

Theorem step_simulation:
  forall s1 s1' s2,
    match_states s1 s2 ->
    step p s1 s1' ->
    exists s2', plus (step p') s2 s2' /\ match_states s1' s2'.
Proof.
  intros s1 s1' s2 Hmatch Hstep.
  inv Hmatch; inv Hstep.

  (* Dispatch non-caller cases for non-Icall match_normal *)
  all: try match goal with
  | [ H1 : (?fi <> cs_caller cs -> ?rs_src = ?rs_tgt),
      H2 : nth_error p ?fi = Some ?f_src,
      H3 : nth_error p' ?fi = Some ?f_tgt,
      H8 : nth_error (fn_code ?f_src) ?pc = Some ?instr |- _ ] =>
      destruct (Nat.eq_dec fi (cs_caller cs)) as [Hcaller | Hother];
      [ (* caller case: leave for manual proof with Hcaller in scope *)
        idtac
      | (* non-caller case: rs equality, done *)
        assert (rs_src = rs_tgt) by auto; subst rs_tgt;
        eexists; split;
        [ apply plus_one; econstructor; [solve_code_preserved | eauto ..]
        | econstructor; eauto; try tauto ]
      ]
  end.
  (* === match_normal, caller cases (fi = cs_caller cs) === *)

  - (* exec_Inop, caller *) 
    exists (State s_tgt f_tgt pc' rs_tgt). split.
    apply plus_one. apply exec_Inop. apply (code_at_pc_preserved fi f_src); try assumption. 
    apply (pc_ne_cs_pc _ f_src _ (Inop pc')); try assumption. discriminate.
    apply (match_normal _ _ fi); try assumption.

  - (* exec_Iop, caller *)
    exists (State s_tgt f_tgt pc' (update rs_tgt dst v)). split.

    (* step reaches new state *)
    apply plus_one. 
    apply (exec_Iop _ _ _ _ _ op args). apply (code_at_pc_preserved fi f_src); try assumption.
    apply (pc_ne_cs_pc _ f_src _ (Iop op args dst pc')); try assumption. discriminate.
    specialize (H1 Hcaller) as Hagree.
    replace (map_regs rs_tgt args) with (map_regs rs_src args). exact H10.
    apply (map_regs_agree _ _ f_src pc (Iop op args dst pc')); auto.
    rewrite <- Hcaller. assumption. intros. simpl. right. assumption.

    (* match states *)
    apply (match_normal _ _ fi); try assumption; intros.
    contradiction. 
    apply regs_agree_update, H1, Hcaller.

    (* FIXME: duplicate code. we can probably use `e`- tactics to remove specific names and 
    generalize it? *)
  - (* exec_Icond_true, caller *) 
    exists (State s_tgt f_tgt ifso rs_tgt). split.
    apply plus_one. apply (exec_Icond_true _ _ _ _ _ cond _ ifnot).
    apply (code_at_pc_preserved fi f_src); try assumption.
    apply (pc_ne_cs_pc _ f_src _ (Icond cond ifso ifnot)); try assumption. discriminate.
    replace (rs_tgt cond) with (rs_src cond). exact H10.
    unfold regs_agree in H1.
    apply H1. assumption. 
    apply (max_reg_func_bound _ (Icond cond ifso ifnot) pc). 
    unfold caller. rewrite <- Hcaller. rewrite H2. exact H9.

    (* match states *)
    apply (match_normal _ _ fi); assumption.

  - (* exec_Icond_false, caller *)
    exists (State s_tgt f_tgt ifnot rs_tgt). split.
    apply plus_one. apply (exec_Icond_false _ _ _ _ _ cond ifso).
    apply (code_at_pc_preserved fi f_src); try assumption.
    apply (pc_ne_cs_pc _ f_src _ (Icond cond ifso ifnot)); try assumption. discriminate.
    replace (rs_tgt cond) with (rs_src cond). 
    unfold regs_agree in H1.
    assumption.
    apply H1. apply Hcaller.
    apply (max_reg_func_bound _ (Icond cond ifso ifnot) pc). 
    unfold caller. rewrite <- Hcaller. rewrite H2. exact H9.

    (* match states *)
    apply (match_normal _ _ fi); assumption.

  - (* exec_Icall, normal *)
    destruct (Nat.eq_dec pc (cs_pc cs)) as [Hinl | Hnotinl].
    + (* inlined call site *) admit.
    + (* different call site *)
      (* Get the target function in p' *)
      assert (Htgt_in_p' : exists fd_tgt, nth_error p' target = Some fd_tgt).
      { destruct (find_func_preserved _ _ H10) as [Hfd | [_ [fd' Hfd']]];
        eauto. }
      destruct Htgt_in_p' as [fd_tgt Hfd_tgt].
      (* Registers agree on args *)
      assert (Hmap : map_regs rs_src args = map_regs rs_tgt args).
      { destruct (Nat.eq_dec fi (cs_caller cs)) as [Hcaller | Hother].
        - eapply (map_regs_agree _ _ f_src pc (Icall target args dst pc'));
          auto. rewrite <- Hcaller. assumption. intros. simpl. right. assumption.
        - assert (rs_src = rs_tgt) by auto. subst. reflexivity. }
      (* Construct the step and match *)
      assert (Hcode_tgt : nth_error (fn_code f_tgt) pc = Some (Icall target args dst pc')).
      { apply (code_at_pc_preserved fi f_src f_tgt pc _ H2 H3 (or_intror Hnotinl) H9). }
      eexists. split.
      * apply plus_one. eapply exec_Icall; eauto.
      * rewrite <- Hmap.
        eapply (match_callstate _ _ target); eauto.
        eapply match_stacks_cons; eauto.
        destruct (Nat.eq_dec fi (cs_caller cs)); auto.
        unfold regs_agree. intros.
        assert (rs_src = rs_tgt) by auto. subst. reflexivity.
  
  - (* exec_Iret, caller *)
  exists (Returnstate s_tgt (rs_tgt src)). split.
  apply plus_one. apply exec_Iret. apply (code_at_pc_preserved fi f_src); try assumption. 
  apply (pc_ne_cs_pc fi f_src _ (Iret src)); try assumption. discriminate.
  
  (* match states *)
  replace (rs_src src) with (rs_tgt src).
  apply (match_returnstate); assumption.
  unfold regs_agree in H1. symmetry.
  apply H1. assumption. apply (max_reg_func_bound _ (Iret src) pc).
  unfold caller. rewrite <- Hcaller. rewrite H2. exact H9. 

    (* === match_inlined cases === *)
  - (* exec_Inop inside inlined body *)
    exists (State s_tgt caller_tgt (pc' + node_offset) rs_tgt).
    split.
    + apply plus_one. constructor.
      destruct (inlined_body_at pc_callee (Inop pc') H8) as [cf' [d [s [Hcf' Hcode]]]].
      simpl in Hcode. replace cf' with caller_tgt in Hcode by congruence.
      exact Hcode.
    + eapply match_inlined; eauto.
    
  - (* exec_Iop inside inlined body *) admit.
  - (* exec_Icond_true inside inlined body *) admit.
  - (* exec_Icond_false inside inlined body *) admit.
  - (* exec_Icall inside inlined body: impossible *) exfalso. admit.
  - (* exec_Iret inside inlined body *) admit.

  (* === match_callstate === *)
  - (* exec_function_entry *) 
  
  exists (State s_tgt f_tgt (fn_entrypoint f_tgt) (init_regs args (fn_params f_tgt))). split.
    + 
      apply plus_one. apply exec_function_entry.
    +
    rewrite (inline_preserves_entrypoint fi f_src f_tgt H0 H1).
    rewrite (inline_preserves_params fi f_src f_tgt H0 H1).

    (* TODO: is there a cleaner way to write the tactic combinator here that conveys what dispatches each case? *)
    apply (match_normal _ _ fi); try assumption; try unfold regs_agree; try reflexivity.

  (* === match_returnstate === *)
  - (* exec_return *) 
  admit.


Admitted.

End INLINING_PROOF.
