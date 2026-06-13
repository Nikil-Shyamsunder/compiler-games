From VerifPerf Require Import Syntax Semantics Inlining.
From Stdlib Require Import List Nat Bool Relations Arith Lia PeanoNat.
Import ListNotations.

Inductive plus {A : Type} (step : A -> A -> Prop) : A -> A -> Prop :=
  | plus_one : forall s1 s2, step s1 s2 -> plus step s1 s2
  | plus_step : forall s1 s2 s3, step s1 s2 -> plus step s2 s3 -> plus step s1 s3.

Fixpoint apply_param_binds (rs : regset) (args params : list reg) (ro : nat) : regset :=
  match args, params with
  | a :: args', p :: params' =>
      apply_param_binds (update rs (p + ro) (rs a)) args' params' ro
  | _, _ => rs
  end.

Lemma bind_params_nil_apply_param_binds :
  forall rs args params ro start,
    bind_params args params ro start = [] ->
    apply_param_binds rs args params ro = rs.
Proof.
  intros rs args params ro start Hnil.
  destruct args as [|a args]; destruct params as [|param params]; simpl in *; auto; discriminate.
Qed.

Section BIND_PARAMS_EXEC.

Variable prog : program.

Lemma exec_bind_params :
  forall f_tgt s rs args params ro start,
    (forall i instr,
      nth_error (bind_params args params ro start) i = Some instr ->
      nth_error (fn_code f_tgt) (start + i) = Some instr) ->
    bind_params args params ro start <> [] ->
    plus (step prog)
      (State s f_tgt start rs)
      (State s f_tgt (start + length (bind_params args params ro start))
         (apply_param_binds rs args params ro)).
Proof.
  intros f_tgt s rs args.
  revert rs.
  induction args as [|a args IH]; intros rs params ro start Hcode Hnonempty.
  - destruct params; simpl in Hnonempty; contradiction.
  - destruct params as [|param params].
    + simpl in Hnonempty. contradiction.
    + simpl.
      assert (Hhead :
        nth_error (fn_code f_tgt) start =
        Some (Iop Oid [a] (param + ro) (start + 1))).
      { assert (Hnth0 :
          nth_error (bind_params (a :: args) (param :: params) ro start) 0 =
          Some (Iop Oid [a] (param + ro) (start + 1))).
        { simpl. reflexivity. }
        specialize (Hcode 0 _ Hnth0).
        replace (start + 0) with start in Hcode by lia.
        exact Hcode. }
      destruct (bind_params args params ro (start + 1)) eqn:Htail.
      * apply plus_one.
        simpl.
        rewrite (bind_params_nil_apply_param_binds
                   (update rs (param + ro) (rs a)) args params ro (start + 1) Htail).
        eapply exec_Iop; [exact Hhead | simpl; reflexivity].
      * replace (start + S (length (i :: l))) with (start + 1 + length (i :: l)) by lia.
        eapply plus_step.
        -- eapply exec_Iop; [exact Hhead | simpl; reflexivity].
        -- rewrite <- Htail.
           eapply IH.
           ++ intros i0 instr Hnth.
              pose proof (Hcode (S i0) instr) as Hcode'.
              simpl in Hcode'.
              specialize (Hcode' Hnth).
              replace (start + S i0) with (start + 1 + i0) in Hcode' by lia.
              exact Hcode'.
           ++ rewrite Htail. discriminate.
Qed.

End BIND_PARAMS_EXEC.

Section INLINING_PROOF.

Variable p : program.
Variable cs : callsite.
Variable p' : program.
Hypothesis Hinline : inline p cs = Some p'.

Let caller := match nth_error p (cs_caller cs) with
              | Some f => f
              | None => mk_function [] []
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
                      | None => mk_function [] []
                      end
                  | _ => mk_function [] []
                  end
              | None => mk_function [] []
              end.

Let reg_offset := max_reg_func caller + 1.

Let call_args := match nth_error (fn_code caller) (cs_pc cs) with
                 | Some (Icall _ args _ _) => args
                 | _ => []
                 end.

Let call_dst := match nth_error (fn_code caller) (cs_pc cs) with
                | Some (Icall _ _ dst _) => dst
                | _ => 0
                end.

Let call_succ := match nth_error (fn_code caller) (cs_pc cs) with
                 | Some (Icall _ _ _ succ) => succ
                 | _ => 0
                 end.

Let node_offset := length (fn_code caller) +
                   length (bind_params call_args (fn_params callee)
                             reg_offset (length (fn_code caller))).

Definition regs_agree (rs_src rs_tgt : regset) : Prop :=
  forall r, r <= max_reg_func caller -> rs_src r = rs_tgt r.

Definition high_regs_zero (rs : regset) : Prop :=
  forall r, max_reg_func caller < r -> rs r = 0.

Definition frame_regs_rel (fi dst : nat) (rs_src rs_tgt : regset) : Prop :=
  (fi <> cs_caller cs -> rs_src = rs_tgt) /\
  (fi = cs_caller cs -> regs_agree rs_src rs_tgt).

Lemma high_regs_zero_update : forall rs dst v,
  high_regs_zero rs ->
  dst <= max_reg_func caller ->
  high_regs_zero (update rs dst v).
Proof.
  unfold high_regs_zero, update. intros rs dst v Hzero Hdst r Hr.
  destruct (Nat.eqb r dst) eqn:Heq.
  - apply Nat.eqb_eq in Heq. subst r. lia.
  - apply Hzero. lia.
Qed.

Lemma init_regs_zero_above : forall vals params m,
  (forall r, In r params -> r <= m) ->
  forall r, m < r -> init_regs vals params r = 0.
Proof.
  assert (Hacc : forall rs vals params m,
    (forall r, In r params -> r <= m) ->
    (forall r, m < r -> rs r = 0) ->
    forall r, m < r -> init_regs_acc rs vals params r = 0).
  { intros rs vals params.
    revert rs vals.
    induction params as [|param ps IH]; intros rs vals m Hbound Hrs0 r Hr; simpl.
    - destruct vals; apply Hrs0; exact Hr.
    - destruct vals as [|v vs].
      + apply Hrs0; exact Hr.
      + apply IH with (m := m).
        * intros x Hx. apply Hbound. simpl. right. exact Hx.
        * intros x Hx. unfold update.
          destruct (Nat.eqb x param) eqn:Heq.
          -- apply Nat.eqb_eq in Heq. subst x.
             assert (Hle : param <= m) by (apply Hbound; simpl; left; reflexivity).
             lia.
          -- apply Hrs0. exact Hx.
        * exact Hr. }
  intros vals params m Hbound r Hr.
  unfold init_regs.
  eapply Hacc.
  - exact Hbound.
  - intros x Hx. reflexivity.
  - exact Hr.
Qed.

Inductive match_stacks : list stackframe -> list stackframe -> Prop :=
  | match_stacks_nil :
      match_stacks nil nil
  | match_stacks_cons : forall dst fi f_src f_tgt pc rs_src rs_tgt s_src s_tgt,
      frame_regs_rel fi dst rs_src rs_tgt ->
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
      nth_error p (cs_caller cs) = Some caller ->
      nth_error (fn_code caller) (cs_pc cs) = Some (Icall call_target call_args dst ret_pc) ->
      regs_agree rs_caller_src rs_tgt ->
      (forall r, rs_callee_src r = rs_tgt (r + reg_offset)) ->
      nth_error p' (cs_caller cs) = Some caller_tgt ->
      match_states
        (State ((Stackframe dst caller ret_pc rs_caller_src) :: s_src)
               callee pc_callee rs_callee_src)
        (State s_tgt caller_tgt (pc_callee + node_offset) rs_tgt)
  .

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

(* common tacttic for field preservation
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

Lemma inline_preserves_params : forall fi f_src f_tgt,
  nth_error p fi = Some f_src ->
  nth_error p' fi = Some f_tgt ->
  fn_params f_src = fn_params f_tgt.
Proof. solve_inline_preserves_field. Qed.

Lemma inlined_body_at : forall pc_callee instr,
  nth_error (fn_code callee) pc_callee = Some instr ->
  exists caller_f',
    nth_error p' (cs_caller cs) = Some caller_f' /\
    nth_error (fn_code caller_f') (pc_callee + node_offset) =
      Some (replace_ret (remap_nodes node_offset (remap_regs reg_offset instr))
                        reg_offset call_dst call_succ).
Proof.
  intros pc_callee instr Hinstr.
  unpack_inline.
  unfold inline_in_func in Hinl_func.
  rewrite Hcall_instr in Hinl_func.
  injection Hinl_func as Hcf'.
  assert (Hcaller_f' : nth_error p' (cs_caller cs) = Some caller_f').
  { rewrite Hp'. apply nth_error_replace_same. nth_error_some_lt. }
  exists caller_f'. split; [exact Hcaller_f' |].
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
  assert (Hdst_eq : call_dst = call_d).
  { unfold call_dst.
    rewrite Hcaller_eq, Hcall_instr. reflexivity. }
  assert (Hsucc_eq : call_succ = call_s).
  { unfold call_succ.
    rewrite Hcaller_eq, Hcall_instr. reflexivity. }
  assert (Hno_eq : node_offset = no + length pb).
  { unfold node_offset. rewrite Hcaller_eq, Hcallee_eq, Hcall_args_eq. reflexivity. }
  rewrite Hro_eq, Hno_eq, Hdst_eq, Hsucc_eq.
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

Lemma regs_agree_update_high : forall rs_src rs_tgt dst v,
  regs_agree rs_src rs_tgt ->
  max_reg_func caller < dst ->
  regs_agree rs_src (update rs_tgt dst v).
Proof.
  unfold regs_agree, update. intros rs_src rs_tgt dst v Hagree Hhigh r Hr.
  destruct (Nat.eqb r dst) eqn:Heq.
  - apply Nat.eqb_eq in Heq. subst r. lia.
  - apply Hagree. exact Hr.
Qed.

Lemma regs_agree_apply_param_binds : forall rs_src rs_tgt args params,
  regs_agree rs_src rs_tgt ->
  regs_agree rs_src (apply_param_binds rs_tgt args params reg_offset).
Proof.
  intros rs_src rs_tgt args.
  revert rs_tgt.
  induction args as [|a args IH]; intros rs_tgt params Hagree.
  - destruct params; simpl; exact Hagree.
  - destruct params as [|param params]; simpl.
    + exact Hagree.
    + apply IH.
      apply regs_agree_update_high; [exact Hagree|].
      unfold reg_offset. lia.
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

Lemma low_regs_unchanged_by_param_bind : forall rs param v a,
  a <= max_reg_func caller ->
  update rs (param + reg_offset) v a = rs a.
Proof.
  intros rs param v a Ha.
  unfold update, reg_offset.
  destruct (Nat.eqb a (param + (max_reg_func caller + 1))) eqn:Heq.
  - apply Nat.eqb_eq in Heq. lia.
  - reflexivity.
Qed.

Lemma init_regs_acc_apply_param_binds :
  forall rs0 rs args params,
    (forall x, rs0 x = rs (x + reg_offset)) ->
    (forall a, In a args -> a <= max_reg_func caller) ->
    forall r,
      init_regs_acc rs0 (map_regs rs args) params r =
      apply_param_binds rs args params reg_offset (r + reg_offset).
Proof.
  intros rs0 rs args.
  revert rs0 rs.
  induction args as [|a args IH]; intros rs0 rs params Hshift Hargs r.
  - destruct params; simpl; apply Hshift.
  - destruct params as [|param params].
    + simpl. apply Hshift.
    + simpl.
      set (rs' := update rs (param + reg_offset) (rs a)).
      assert (Hmap :
        map_regs rs' args = map_regs rs args).
      { unfold map_regs. apply map_ext_in. intros x Hx.
        unfold rs'. apply low_regs_unchanged_by_param_bind.
        apply Hargs. simpl. right. exact Hx. }
      rewrite <- Hmap.
      apply IH.
      * intros x. unfold rs', update.
        destruct (Nat.eqb x param) eqn:Heq.
        -- apply Nat.eqb_eq in Heq. subst x.
           rewrite Nat.eqb_refl. reflexivity.
        -- apply Nat.eqb_neq in Heq.
           assert (x + reg_offset <> param + reg_offset) by lia.
           apply Nat.eqb_neq in H.
           rewrite H. apply Hshift.
      * intros x Hx. apply Hargs. simpl. right. exact Hx.
Qed.

Lemma init_regs_apply_param_binds :
  forall rs args params,
    high_regs_zero rs ->
    (forall a, In a args -> a <= max_reg_func caller) ->
    forall r,
      init_regs (map_regs rs args) params r =
      apply_param_binds rs args params reg_offset (r + reg_offset).
Proof.
  intros rs args params Hzero Hargs r.
  unfold init_regs.
  eapply init_regs_acc_apply_param_binds.
  - intros x. symmetry. apply Hzero. unfold reg_offset. lia.
  - exact Hargs.
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
    eapply match_normal.
    + exact H.
    + exact H0.
    + exact H1.
    + exact H2.
    + exact H3.

  - (* exec_Iop, caller *)
    exists (State s_tgt f_tgt pc' (update rs_tgt dst v)). split.

    (* step reaches new state *)
    apply plus_one. 
    apply (exec_Iop _ _ _ _ _ op args). apply (code_at_pc_preserved fi f_src); try assumption.
    apply (pc_ne_cs_pc _ f_src _ (Iop op args dst pc')); try assumption. discriminate.
    specialize (H1 Hcaller) as Hagree.
    replace (map_regs rs_tgt args) with (map_regs rs_src args).
    2:{ apply (map_regs_agree _ _ f_src pc (Iop op args dst pc')); auto.
        rewrite <- Hcaller. assumption. intros. simpl. right. assumption. }
    match goal with
    | [ Heval : eval_op op (map_regs rs_src args) = Some v |- _ ] => exact Heval
    end.

    (* match states *)
    apply (match_normal s_src s_tgt fi f_src f_tgt pc'
             (update rs_src dst v) (update rs_tgt dst v)).
    + exact H.
    + intros Hneq.
      assert (rs_src = rs_tgt) by auto.
      subst rs_tgt. reflexivity.
    + intro Hignore. apply regs_agree_update, H1, Hcaller.
    + exact H2.
    + exact H3.

    (* FIXME: duplicate code. we can probably use `e`- tactics to remove specific names and 
    generalize it? *)
  - (* exec_Icond_true, caller *) 
    exists (State s_tgt f_tgt ifso rs_tgt). split.
    apply plus_one. apply (exec_Icond_true _ _ _ _ _ cond _ ifnot).
    apply (code_at_pc_preserved fi f_src); try assumption.
    apply (pc_ne_cs_pc _ f_src _ (Icond cond ifso ifnot)); try assumption. discriminate.
    replace (rs_tgt cond) with (rs_src cond).
    2:{ unfold regs_agree in H1.
        apply H1. assumption.
        apply (max_reg_func_bound _ (Icond cond ifso ifnot) pc).
        unfold caller. rewrite <- Hcaller. rewrite H2. exact H9. }
    match goal with
    | [ Hcond : rs_src cond <> 0 |- _ ] => exact Hcond
    end.

    (* match states *)
    eapply match_normal.
    + exact H.
    + exact H0.
    + exact H1.
    + exact H2.
    + exact H3.

  - (* exec_Icond_false, caller *)
    exists (State s_tgt f_tgt ifnot rs_tgt). split.
    apply plus_one. apply (exec_Icond_false _ _ _ _ _ cond ifso).
    apply (code_at_pc_preserved fi f_src); try assumption.
    apply (pc_ne_cs_pc _ f_src _ (Icond cond ifso ifnot)); try assumption. discriminate.
    replace (rs_tgt cond) with (rs_src cond).
    2:{ unfold regs_agree in H1.
        apply H1. apply Hcaller.
        apply (max_reg_func_bound _ (Icond cond ifso ifnot) pc).
        unfold caller. rewrite <- Hcaller. rewrite H2. exact H9. }
    match goal with
    | [ Hcond : rs_src cond = 0 |- _ ] => exact Hcond
    end.

    (* match states *)
    eapply match_normal; eauto.

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
	      match goal with
	      | [ Hcode : nth_error (fn_code f_src) pc = Some (Icall _ _ _ _ ) |- _ ] =>
	          rewrite Hinl in Hcode; rewrite Hcode in Hcall
	      end.
	      injection Hcall. intros. subst.
      clear Hcall.

      exists (State s_tgt f_tgt node_offset
                (apply_param_binds rs_tgt call_args (fn_params callee) reg_offset)).
      split.
      (* step through the no-op and the call arg movements *)
      * destruct (bind_params call_args (fn_params callee) reg_offset
                    (length (fn_code caller))) eqn:Hbinds.
        -- unfold node_offset. simpl.
           replace (apply_param_binds rs_tgt call_args (fn_params callee) reg_offset)
             with rs_tgt.
           2:{ symmetry. eapply bind_params_nil_apply_param_binds. exact Hbinds. }
           replace (length (fn_code caller) + 0) with (length (fn_code caller)) by lia.
           apply plus_one. apply exec_Inop. exact HInop.
        -- eapply plus_step.
           ++ apply exec_Inop. exact HInop.
           ++ unfold node_offset. simpl.
              replace (length (fn_code caller) + S (length l))
                with (length (fn_code caller) +
                      length (bind_params call_args (fn_params callee) reg_offset
                                (length (fn_code caller)))) by
                  (rewrite Hbinds; simpl; lia).
	              eapply (exec_bind_params p' f_tgt s_tgt rs_tgt call_args
	                        (fn_params callee) reg_offset (length (fn_code caller))).
	              ** intros j instr Hnth.
	                 eapply param_bind_at; eauto.
	              ** rewrite Hbinds. discriminate.

	      (* match states *)
	      * assert (Hcall_args : call_args = args').
	        { unfold call_args, caller. rewrite H2.
	          match goal with
	          | [ Hcode : nth_error (fn_code f_src) (cs_pc cs) = Some (Icall _ _ _ _) |- _ ] =>
	              rewrite Hcode; reflexivity
	          end. }
	        admit.
	      
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
	      pose proof (inline_preserves_params target fd fd_tgt H10 Hfd_tgt) as Hparams.
	      eexists. split.
	      * apply plus_one. eapply exec_Icall; [exact Hcode_tgt | exact Hfd_tgt].
	      * rewrite Hparams, <- Hmap.
	        eapply match_normal.
	        -- eapply match_stacks_cons; eauto.
	           split.
	           ++ intros Hneq. contradiction.
	           ++ intros _. apply H1. exact Hcaller.
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
	      pose proof (inline_preserves_params target fd fd_tgt H10 Hfd_tgt) as Hparams.
	      eexists. split.
	      * apply plus_one. eapply exec_Icall; [exact Hcode_tgt | exact Hfd_tgt].
	      * rewrite Hparams.
	        eapply match_normal with (fi := target) (f_src := fd) (f_tgt := fd_tgt).
	        -- eapply match_stacks_cons; eauto.
	           split.
	           ++ exact H0.
	           ++ exact H1.
	        -- intros _. reflexivity.
	        -- unfold regs_agree. intros. reflexivity.
	        -- exact H10.
	        -- exact Hfd_tgt.
  
  - (* exec_Iret, caller *)
  inversion H as
      [| dst0 fi0 f_src0 f_tgt0 ret_pc0 rs_caller_src rs_caller_tgt s_src0 s_tgt0
          Hrel Hsrcf Htgtf Htail];
    subst; clear H.
  destruct Hrel as [Hframe_eq Hframe_agree].
  assert (Hsrc_eq : rs_src src = rs_tgt src).
  { destruct (Nat.eq_dec fi (cs_caller cs)) as [Hcur | Hcur].
    - unfold regs_agree in H1.
      apply H1; [exact Hcur|].
      apply (max_reg_func_bound _ (Iret src) pc).
      unfold caller. rewrite <- Hcur. rewrite H2. exact H9.
    - assert (rs_src = rs_tgt) by auto. subst rs_tgt. reflexivity. }
  eexists. split.
  * apply plus_one. eapply exec_Iret.
    eapply (code_at_pc_preserved fi f_src f_tgt pc (Iret src)).
    -- exact H2.
    -- exact H3.
    -- eapply pc_ne_cs_pc; eauto. discriminate.
    -- exact H9.
  * eapply match_normal with (fi := fi0) (f_src := f_caller) (f_tgt := f_tgt0).
    -- exact Htail.
    -- intros Hneq. specialize (Hframe_eq Hneq). subst rs_caller_tgt.
       rewrite Hsrc_eq. reflexivity.
    -- intros Hfi. rewrite Hsrc_eq. apply regs_agree_update. apply Hframe_agree. exact Hfi.
    -- exact Hsrcf.
    -- exact Htgtf.

    (* === match_inlined cases === *)
  - (* exec_Inop inside inlined body *)
    exists (State s_tgt caller_tgt (pc' + node_offset) rs_tgt).
    split.
    + apply plus_one. constructor.
      match goal with
      | [ Hinstr : nth_error (fn_code callee) pc_callee = Some (Inop pc') |- _ ] =>
          destruct (inlined_body_at pc_callee (Inop pc') Hinstr) as [cf' [Hcf' Hcode]]
      end.
      simpl in Hcode. replace cf' with caller_tgt in Hcode by congruence.
      exact Hcode.
	    + eapply match_inlined; [exact H | exact H0 | exact H1 | exact H2 | exact H3 | exact H4 | exact H5].
	    
  - (* exec_Iop inside inlined body *)
    exists (State s_tgt caller_tgt (pc' + node_offset) (update rs_tgt (dst0 + reg_offset) v)).
    split.
    + apply plus_one.
      match goal with
      | [ Hinstr : nth_error (fn_code callee) pc_callee = Some (Iop op args dst0 pc') |- _ ] =>
          destruct (inlined_body_at pc_callee (Iop op args dst0 pc') Hinstr) as [cf' [Hcf' Hcode]]
      end.
      simpl in Hcode. replace cf' with caller_tgt in Hcode by congruence.
      eapply exec_Iop; [exact Hcode |].
      unfold map_regs in *. rewrite map_map.
      replace (map (fun x => rs_tgt (x + reg_offset)) args) with (map rs_callee_src args).
      * match goal with
        | [ Heval : eval_op _ _ = Some _ |- _ ] =>
            exact Heval
        end.
      * match goal with
        | [ Hshift : forall r, rs_callee_src r = _ |- _ ] =>
            apply map_ext_in; intros a _; exact (Hshift a)
        end.
    + eapply match_inlined.
      * exact H.
      * exact H0.
      * exact H1.
      * exact H2.
      * apply regs_agree_update_high; [exact H3|].
        unfold reg_offset. lia.
      * intros r. unfold update.
        destruct (Nat.eqb (r + reg_offset) (dst0 + reg_offset)) eqn:Heq.
        -- apply Nat.eqb_eq in Heq. assert (r = dst0) by lia. subst.
           rewrite Nat.eqb_refl. reflexivity.
        -- apply Nat.eqb_neq in Heq. assert (r <> dst0) by lia.
           match goal with
           | [ Hshift : forall r, rs_callee_src r = _ |- _ ] =>
               rewrite <- Hshift
           end.
           destruct (Nat.eqb r dst0) eqn:Heq2; [apply Nat.eqb_eq in Heq2; lia | reflexivity].
      * exact H5.

  - (* exec_Icond_true inside inlined body *)
    exists (State s_tgt caller_tgt (ifso + node_offset) rs_tgt).
    split.
    + apply plus_one.
      match goal with
      | [ Hinstr : nth_error (fn_code callee) pc_callee = Some (Icond cond ifso ifnot) |- _ ] =>
          destruct (inlined_body_at pc_callee (Icond cond ifso ifnot) Hinstr) as [cf' [Hcf' Hcode]]
      end.
      simpl in Hcode. replace cf' with caller_tgt in Hcode by congruence.
      eapply exec_Icond_true; [exact Hcode |].
      match goal with
      | [ Hshift : forall r, rs_callee_src r = _,
          Hcond : rs_callee_src cond <> 0 |- _ ] =>
          rewrite <- Hshift; exact Hcond
      end.
	    + eapply match_inlined; [exact H | exact H0 | exact H1 | exact H2 | exact H3 | exact H4 | exact H5].

  - (* exec_Icond_false inside inlined body *)
    exists (State s_tgt caller_tgt (ifnot + node_offset) rs_tgt).
    split.
    + apply plus_one.
      match goal with
      | [ Hinstr : nth_error (fn_code callee) pc_callee = Some (Icond cond ifso ifnot) |- _ ] =>
          destruct (inlined_body_at pc_callee (Icond cond ifso ifnot) Hinstr) as [cf' [Hcf' Hcode]]
      end.
      simpl in Hcode. replace cf' with caller_tgt in Hcode by congruence.
      eapply exec_Icond_false; [exact Hcode |].
      match goal with
      | [ Hshift : forall r, rs_callee_src r = _,
          Hcond : rs_callee_src cond = 0 |- _ ] =>
          rewrite <- Hshift; exact Hcond
      end.
	    + eapply match_inlined; [exact H | exact H0 | exact H1 | exact H2 | exact H3 | exact H4 | exact H5].

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
    match goal with
    | [ Hinstr : nth_error (fn_code callee) pc_callee = Some _ |- _ ] =>
        specialize (Hleaf' _ (nth_error_In _ _ Hinstr)); simpl in Hleaf'; exact Hleaf'
    end.

  - (* exec_Iret inside inlined body *)
    match goal with
    | [ Hinstr : nth_error (fn_code callee) pc_callee = Some (Iret src) |- _ ] =>
        destruct (inlined_body_at pc_callee (Iret src) Hinstr) as [cf' [Hcf' Hcode]]
    end.
    simpl in Hcode. replace cf' with caller_tgt in Hcode by congruence.
    assert (Hcall_dst : call_dst = dst).
    { unfold call_dst. rewrite H2. reflexivity. }
    assert (Hcall_succ : call_succ = ret_pc).
    { unfold call_succ. rewrite H2. reflexivity. }
    rewrite Hcall_dst, Hcall_succ in Hcode.
    exists (State s_tgt caller_tgt ret_pc (update rs_tgt dst (rs_callee_src src))).
    split.
    + apply plus_one.
      eapply exec_Iop.
      * exact Hcode.
      * simpl. rewrite <- H4. reflexivity.
    + eapply match_normal with
          (fi := cs_caller cs)
          (f_src := caller)
          (f_tgt := caller_tgt).
      * exact H.
      * intros Hneq. contradiction.
      * intros _. apply regs_agree_update. exact H3.
      * exact H1.
      * exact H5.


Admitted.

End INLINING_PROOF.
