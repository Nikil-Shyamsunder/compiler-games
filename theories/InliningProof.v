From VerifPerf Require Import Syntax Semantics Inlining.
From Stdlib Require Import List Nat Bool Relations Arith Lia PeanoNat.
Import ListNotations.

Section INLINING_PROOF.

Variable p : program.
Variable cs : callsite.
Variable p' : program.
Hypothesis Hinline : inline p cs = Some p'.

Let caller := match nth_error p (cs_caller cs) with
              | Some f => f
              | None => mk_function [] [] 0
              end.

Let call_target := match nth_error (fn_code caller) (cs_pc cs) with
                   | Some (Icall t _ _ _) => t
                   | _ => 0
                   end.

Let callee := match nth_error p (cs_caller cs) with
              | Some caller_f =>
                  match nth_error (fn_code caller_f) (cs_pc cs) with
                  | Some (Icall t _ _ _) =>
                      match nth_error p t with
                      | Some f => f
                      | None => mk_function [] [] 0
                      end
                  | _ => mk_function [] [] 0
                  end
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
  destruct (nth_error p (cs_caller cs)) as [the_caller|] eqn:Hcaller_lookup; [|discriminate];
  destruct (nth_error (fn_code the_caller) (cs_pc cs)) as [[ | | | ?call_tgt ?call_al ?call_d ?call_s | ]|] eqn:Hcall_instr; try discriminate;
  destruct (nth_error p call_tgt) as [callee_f|] eqn:Htarget; [|discriminate];
  destruct (isLeafb callee_f) eqn:Hleaf; [|discriminate];
  destruct (inline_in_func the_caller callee_f (cs_pc cs)) as [caller_f'|] eqn:Hinl_func; [|discriminate];
  assert (Hp' : p' = firstn (cs_caller cs) p ++ caller_f' :: skipn (cs_caller cs + 1) p)
    by (change (caller_f' :: skipn (cs_caller cs + 1) p)
          with ([caller_f'] ++ skipn (cs_caller cs + 1) p); congruence);
  assert (Hcaller_eq : caller = the_caller) by reflexivity;
  assert (Hcallee_eq : callee = callee_f) by reflexivity;
  assert (Hcall_args_eq : call_args = call_al)
    by (change call_args with
          (match nth_error (fn_code caller) (cs_pc cs) with
           | Some (Icall _ args _ _) => args | _ => [] end);
        rewrite Hcaller_eq, Hcall_instr; reflexivity);
  clear H.

Ltac nth_error_some_lt :=
  match goal with
  | [ H : nth_error ?l ?n = Some _ |- ?n < length ?l ] =>
      apply nth_error_Some; congruence
  | [ H : nth_error ?l ?n = Some _ |- _ < length ?l ] =>
      apply nth_error_Some; congruence
  end.


Lemma callee_is_leaf : isLeafb callee = true.
Proof.
  unpack_inline. rewrite Hcallee_eq. exact Hleaf.
Qed.

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
  rewrite Hcaller_eq in Hi.
  destruct (nth_error (fn_code the_caller) (cs_pc cs)) as [[]|] eqn:Hcall;
    try discriminate.
  injection Hinl_func as Hcf'.
  rewrite Hp'. eexists. split.
  - apply nth_error_replace_same. apply nth_error_Some. congruence.
  - rewrite <- Hcf'. simpl. unfold inline_call_site.
    assert (Hpc_bound : pc < length (fn_code the_caller))
      by (apply nth_error_Some; congruence).
    assert (Hcs_bound : cs_pc cs < length (fn_code the_caller))
      by (apply nth_error_Some; congruence).
    assert (Hpatch_len :
      length (firstn (cs_pc cs) (fn_code the_caller) ++
              Inop (length (fn_code the_caller)) ::
              skipn (cs_pc cs + 1) (fn_code the_caller)) =
      length (fn_code the_caller)).
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
  replace f_src with the_caller by congruence.
  destruct (nth_error (fn_code the_caller) (cs_pc cs)) as [[]|] eqn:E;
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
  rewrite Hcall_instr in Hinl_func.
  injection Hinl_func as Hcf'.
  assert (Hcaller_f' : nth_error p' (cs_caller cs) = Some caller_f').
  { rewrite Hp'. apply nth_error_replace_same. nth_error_some_lt. }
  exists caller_f', call_d, call_s. split; [exact Hcaller_f' |].
  rewrite <- Hcf'. simpl.
  unfold inline_call_site.
  set (ro := max_reg_func the_caller + 1).
  set (no := length (fn_code the_caller)).
  set (pb := bind_params call_al (fn_params callee_f) ro no).
  set (cb := transform_callee_body (fn_code callee_f) ro (no + length pb) call_d call_s).
  set (pc := firstn (cs_pc cs) (fn_code the_caller)
             ++ Inop no :: skipn (cs_pc cs + 1) (fn_code the_caller)).
  assert (Hcs_bound : cs_pc cs < length (fn_code the_caller))
    by (apply nth_error_Some; congruence).
  assert (Hpc_len : length pc = length (fn_code the_caller)).
  { unfold pc. rewrite length_app. simpl. rewrite length_skipn, length_firstn. lia. }
  rewrite Hcallee_eq in Hinstr.
  assert (Hro_eq : reg_offset = ro) by (unfold reg_offset; rewrite Hcaller_eq; reflexivity).
  assert (Hno_eq : node_offset = no + length pb).
  { unfold node_offset. rewrite Hcaller_eq, Hcallee_eq, Hcall_args_eq. reflexivity. }
  rewrite Hro_eq, Hno_eq.
  rewrite app_assoc.
  rewrite nth_error_app2.
  2: { rewrite length_app, Hpc_len. unfold no. lia. }
  rewrite length_app, Hpc_len.
  replace (pc_callee + (no + length pb) - (length (fn_code the_caller) + length pb))
    with pc_callee by (unfold no; lia).
  unfold cb, transform_callee_body.
  rewrite nth_error_map.
  rewrite Hinstr. simpl.
  unfold no. reflexivity.
Qed.

(* Instruction at position (length (fn_code caller) + i) in modified caller
   is the i-th param bind instruction *)
Lemma param_bind_at : forall f_tgt i instr,
  nth_error p' (cs_caller cs) = Some f_tgt ->
  nth_error (bind_params call_args (fn_params callee) reg_offset
               (length (fn_code caller))) i = Some instr ->
  nth_error (fn_code f_tgt) (length (fn_code caller) + i) = Some instr.
Proof.
  intros f_tgt i instr Hf_tgt Hbind. unpack_inline.
  unfold inline_in_func in Hinl_func.
  rewrite Hcall_instr in Hinl_func.
  injection Hinl_func as Hcf'.
  replace f_tgt with caller_f'.
  2: { assert (nth_error p' (cs_caller cs) = Some caller_f').
       { rewrite Hp'. apply nth_error_replace_same. nth_error_some_lt. }
       congruence. }
  rewrite <- Hcf'. simpl. unfold inline_call_site.
  assert (Hcs_bound : cs_pc cs < length (fn_code the_caller))
    by (apply nth_error_Some; congruence).
  set (pc := firstn (cs_pc cs) (fn_code the_caller)
             ++ Inop (length (fn_code the_caller))
             :: skipn (cs_pc cs + 1) (fn_code the_caller)).
  assert (Hpc_len : length pc = length (fn_code the_caller)).
  { unfold pc. rewrite length_app. simpl. rewrite length_skipn, length_firstn. lia. }
  rewrite nth_error_app2.
  2: { rewrite Hpc_len. apply Nat.le_add_r. }
  rewrite Hpc_len.
  replace (length (fn_code caller) + i - length (fn_code the_caller))
    with i by (rewrite Hcaller_eq; lia).
  assert (Hro : reg_offset = max_reg_func the_caller + 1)
    by (unfold reg_offset; rewrite Hcaller_eq; reflexivity).
  rewrite Hcaller_eq, Hcallee_eq, Hcall_args_eq, Hro in Hbind.
  rewrite nth_error_app1.
  - exact Hbind.
  - apply nth_error_Some. congruence.
Qed.

(* The instruction at cs_pc in the modified caller is Inop jumping to param binds *)
Lemma cs_pc_in_p' : forall f_tgt,
  nth_error p' (cs_caller cs) = Some f_tgt ->
  nth_error (fn_code f_tgt) (cs_pc cs) = Some (Inop (length (fn_code caller))).
Proof.
  intros f_tgt Hf_tgt. unpack_inline.
  unfold inline_in_func in Hinl_func.
  rewrite Hcall_instr in Hinl_func.
  injection Hinl_func as Hcf'.
  replace f_tgt with caller_f'.
  2: { assert (nth_error p' (cs_caller cs) = Some caller_f').
       { rewrite Hp'. apply nth_error_replace_same. nth_error_some_lt. }
       congruence. }
  rewrite <- Hcf'. simpl. unfold inline_call_site.
  assert (Hcs_bound : cs_pc cs < length (fn_code the_caller))
    by (apply nth_error_Some; congruence).
  rewrite nth_error_app1.
  2: { rewrite length_app. simpl. rewrite length_skipn, length_firstn. lia. }
  apply nth_error_replace_same. lia.
Qed.

(* The call at cs_pc has target = call_target *)
Lemma cs_pc_call_target : forall f_src,
  nth_error p (cs_caller cs) = Some f_src ->
  exists args dst succ,
    nth_error (fn_code f_src) (cs_pc cs) = Some (Icall call_target args dst succ).
Proof.
  intros f_src Hf. unpack_inline.
  unfold inline_in_func in Hinl_func.
  replace f_src with the_caller by congruence.
  rewrite Hcall_instr.
  assert (Hct : call_target = call_tgt).
  { change call_target with (match nth_error (fn_code caller) (cs_pc cs) with
      | Some (Icall t _ _ _) => t | _ => 0 end).
    rewrite Hcaller_eq, Hcall_instr. reflexivity. }
  rewrite Hct. eauto.
Qed.

(* The target of the inlined call is callee *)
Lemma call_target_is_callee :
  nth_error p call_target = Some callee.
Proof.
  unpack_inline.
  assert (Hct : call_target = call_tgt).
  { change call_target with (match nth_error (fn_code caller) (cs_pc cs) with
      | Some (Icall t _ _ _) => t | _ => 0 end).
    rewrite Hcaller_eq, Hcall_instr. reflexivity. }
  rewrite Hct, Hcallee_eq. exact Htarget.
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
    (* Carve out the inlined call site case *)
    destruct (Nat.eq_dec fi (cs_caller cs)) as [Hcaller | Hother];
      [destruct (Nat.eq_dec pc (cs_pc cs)) as [Hinl | Hnotinl] |].
    + (* inlined call site: fi = cs_caller, pc = cs_pc *)

      (* FIXME: this specialize rewrite situation is very ugly. *)
      specialize (H1 Hcaller) as Hregsagree. clear H0 H1.
      rewrite Hcaller in *. clear fi Hcaller.
      specialize (cs_pc_in_p' f_tgt H3) as HInop.
      destruct (cs_pc_call_target f_src H2) as [args' [dst' [succ' Hcall]]].
      rewrite Hinl in H9. rewrite H9 in Hcall; injection Hcall. intros. 
      rewrite H0 in *. rewrite H1 in *. rewrite H4 in *. rewrite H5 in *. rewrite Hinl in *.
      clear H0 H1 H4 H5 Hcall pc Hinl. 

      eexists. split.
      (* step through the no-op and the call arg movements *)
      * admit.

      (* match states *)
      * admit.


      (* TODO: following two cases are esentially the same, we ought to merge them into
      one proof hopefully. *)
    + (* different call site: not the inlined callsite, but fi = cs_caller *)
      assert (Hdisj : fi <> cs_caller cs \/ pc <> cs_pc cs) by auto.
      assert (Hcode_tgt : nth_error (fn_code f_tgt) pc = Some (Icall target args dst pc'))
        by (apply (code_at_pc_preserved _ _ _ _ _ H2 H3 Hdisj H9)).
      assert (Htgt_in_p' : exists fd_tgt, nth_error p' target = Some fd_tgt)
        by (destruct (find_func_preserved _ _ H10) as [? | [_ ?]]; eauto).
      destruct Htgt_in_p' as [fd_tgt Hfd_tgt].
      assert (Hmap : map_regs rs_src args = map_regs rs_tgt args).
      { eapply (map_regs_agree _ _ f_src pc (Icall target args dst pc'));
        auto. rewrite <- Hcaller. assumption. intros. simpl. right. assumption. }
      pose proof (inline_preserves_entrypoint target fd fd_tgt H10 Hfd_tgt) as Hentry.
      pose proof (inline_preserves_params target fd fd_tgt H10 Hfd_tgt) as Hparams.
      eexists. split.
      * apply plus_one. eapply exec_Icall; [exact Hcode_tgt | exact Hfd_tgt].
      * rewrite Hentry, Hparams, <- Hmap.
        eapply match_normal.
        -- eapply match_stacks_cons; eauto.
        -- intros _. reflexivity.
        -- unfold regs_agree. intros. reflexivity.
        -- exact H10.
        -- exact Hfd_tgt.
    + (* different call site: fi <> cs_caller *)
      assert (Hdisj : fi <> cs_caller cs \/ pc <> cs_pc cs) by auto.
      assert (rs_src = rs_tgt) by auto. subst rs_tgt.
      assert (Hcode_tgt : nth_error (fn_code f_tgt) pc = Some (Icall target args dst pc'))
        by (apply (code_at_pc_preserved _ _ _ _ _ H2 H3 Hdisj H9)).
      assert (Htgt_in_p' : exists fd_tgt, nth_error p' target = Some fd_tgt)
        by (destruct (find_func_preserved _ _ H10) as [? | [_ ?]]; eauto).
      destruct Htgt_in_p' as [fd_tgt Hfd_tgt].
      pose proof (inline_preserves_entrypoint target fd fd_tgt H10 Hfd_tgt) as Hentry.
      pose proof (inline_preserves_params target fd fd_tgt H10 Hfd_tgt) as Hparams.
      eexists. split.
      * apply plus_one. eapply exec_Icall; [exact Hcode_tgt | exact Hfd_tgt].
      * rewrite Hentry, Hparams.
        eapply match_normal.
        -- eapply match_stacks_cons; eauto.
           unfold regs_agree; intros; reflexivity.
        -- intros _. reflexivity.
        -- unfold regs_agree. intros. reflexivity.
        -- exact H10.
        -- exact Hfd_tgt.
  
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
    
  - (* exec_Iop inside inlined body *)
    exists (State s_tgt caller_tgt (pc' + node_offset) (update rs_tgt (dst0 + reg_offset) v)).
    split.
    + apply plus_one.
      destruct (inlined_body_at pc_callee (Iop op args dst0 pc') H8) as [cf' [d [s [Hcf' Hcode]]]].
      simpl in Hcode. replace cf' with caller_tgt in Hcode by congruence.
      eapply exec_Iop; [exact Hcode |].
      unfold map_regs in *. rewrite map_map.
      replace (map (fun x => rs_tgt (x + reg_offset)) args) with (map rs_callee_src args).
      * exact H9.
      * apply map_ext_in. intros a _. exact (H1 a).
    + eapply match_inlined; eauto.
      intros r. unfold update.
      destruct (Nat.eqb (r + reg_offset) (dst0 + reg_offset)) eqn:Heq.
      * apply Nat.eqb_eq in Heq. assert (r = dst0) by lia. subst.
        rewrite Nat.eqb_refl. reflexivity.
      * apply Nat.eqb_neq in Heq. assert (r <> dst0) by lia.
        rewrite <- H1.
        destruct (Nat.eqb r dst0) eqn:Heq2; [apply Nat.eqb_eq in Heq2; lia | reflexivity].

  - (* exec_Icond_true inside inlined body *)
    exists (State s_tgt caller_tgt (ifso + node_offset) rs_tgt).
    split.
    + apply plus_one.
      destruct (inlined_body_at pc_callee (Icond cond ifso ifnot) H8) as [cf' [d [s [Hcf' Hcode]]]].
      simpl in Hcode. replace cf' with caller_tgt in Hcode by congruence.
      eapply exec_Icond_true; [exact Hcode |].
      rewrite <- H1. exact H9.
    + eapply match_inlined; eauto.

  - (* exec_Icond_false inside inlined body *)
    exists (State s_tgt caller_tgt (ifnot + node_offset) rs_tgt).
    split.
    + apply plus_one.
      destruct (inlined_body_at pc_callee (Icond cond ifso ifnot) H8) as [cf' [d [s [Hcf' Hcode]]]].
      simpl in Hcode. replace cf' with caller_tgt in Hcode by congruence.
      eapply exec_Icond_false; [exact Hcode |].
      rewrite <- H1. exact H9.
    + eapply match_inlined; eauto.

  - (* exec_Icall inside inlined body: impossible *)
    exfalso.
    assert (Hleafb : isLeafb callee = true) by exact callee_is_leaf.
    assert (Hleaf' : isLeaf callee).
    { unfold isLeaf, isLeafb in *.
      rewrite forallb_forall in Hleafb.
      apply Forall_forall. intros x Hx.
      specialize (Hleafb x Hx). destruct x; try exact I. discriminate. }
    unfold isLeaf in Hleaf'.
    rewrite Forall_forall in Hleaf'.
    specialize (Hleaf' _ (nth_error_In _ _ H8)). simpl in Hleaf'. exact Hleaf'.

  - (* exec_Iret inside inlined body *) admit.

  (* === match_returnstate === *)
  - (* exec_return *) 
  admit.


Admitted.

End INLINING_PROOF.
