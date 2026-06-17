From VerifPerf Require Import Syntax Semantics Inlining.
From Stdlib Require Import List Nat Bool Relations Arith Lia PeanoNat.
Import ListNotations.

Inductive plus {A : Type} (step : A -> A -> Prop) : A -> A -> Prop :=
  | plus_one : forall s1 s2, step s1 s2 -> plus step s1 s2
  | plus_step : forall s1 s2 s3, step s1 s2 -> plus step s2 s3 -> plus step s1 s3.

Lemma plus_trans : forall (A : Type) (step : A -> A -> Prop) s1 s2 s3,
  plus step s1 s2 ->
  plus step s2 s3 ->
  plus step s1 s3.
Proof.
  intros A step s1 s2 s3 H12 H23.
  induction H12.
  - eapply plus_step; eauto.
  - eapply plus_step; eauto.
Qed.

Fixpoint apply_param_binds (rs : regset) (args params : list reg) (ro : nat) : regset :=
  match args, params with
  | a :: args', p :: params' =>
      apply_param_binds (update rs (p + ro) (rs a)) args' params' ro
  | _, _ => rs
  end.

Fixpoint zero_regs_acc (rs : regset) (count reg_offset : nat) : regset :=
  match count with
  | 0 => rs
  | S count' => zero_regs_acc (update rs (reg_offset + count') 0) count' reg_offset
  end.

Lemma length_zero_regs :
  forall count reg_offset start_node,
    length (zero_regs count reg_offset start_node) = count.
Proof.
  induction count as [|count IH]; intros; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

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

Section ZERO_REGS_EXEC.

Variable prog : program.

Lemma exec_zero_regs :
  forall f_tgt s rs count reg_offset start,
    (forall i instr,
      nth_error (zero_regs count reg_offset start) i = Some instr ->
      nth_error (fn_code f_tgt) (start + i) = Some instr) ->
    zero_regs count reg_offset start <> [] ->
    plus (step prog)
      (State s f_tgt start rs)
      (State s f_tgt (start + length (zero_regs count reg_offset start))
         (zero_regs_acc rs count reg_offset)).
Proof.
  intros f_tgt s rs count.
  revert rs.
  induction count as [|count IH]; intros rs reg_offset start Hcode Hnonempty.
  - contradiction.
  - simpl in Hnonempty.
    assert (Hhead :
      nth_error (fn_code f_tgt) start =
      Some (Iop (Oconst 0) [] (reg_offset + count) (start + 1))).
    { specialize (Hcode 0 (Iop (Oconst 0) [] (reg_offset + count) (start + 1))).
      simpl in Hcode.
      replace (start + 0) with start in Hcode by lia.
      apply Hcode. reflexivity. }
    destruct (zero_regs count reg_offset (start + 1)) as [|i l] eqn:Htail.
    + apply plus_one.
      assert (Hcount0 : count = 0).
      { apply (f_equal (@length instruction)) in Htail.
        rewrite length_zero_regs in Htail.
        simpl in Htail. lia. }
      subst count.
      simpl.
      eapply exec_Iop; [exact Hhead | reflexivity].
    + eapply plus_step.
      * eapply exec_Iop; [exact Hhead | reflexivity].
      * assert (Hcode' : forall i0 instr,
            nth_error (zero_regs count reg_offset (start + 1)) i0 = Some instr ->
            nth_error (fn_code f_tgt) (start + 1 + i0) = Some instr).
        { intros i0 instr Hnth.
          specialize (Hcode (S i0) instr).
          simpl in Hcode.
          replace (start + S i0) with (start + 1 + i0) in Hcode by lia.
          apply Hcode. exact Hnth. }
        replace (start + length (zero_regs (S count) reg_offset start))
          with (start + 1 + length (zero_regs count reg_offset (start + 1))) by
          (simpl; rewrite Htail; simpl; lia).
        replace (zero_regs_acc rs (S count) reg_offset)
          with (zero_regs_acc (update rs (reg_offset + count) 0) count reg_offset)
          by reflexivity.
        eapply IH.
        -- exact Hcode'.
        -- intro Habs. rewrite Habs in Htail. discriminate.
Qed.

End ZERO_REGS_EXEC.

Lemma nth_error_app_offset :
  forall (A : Type) (l1 l2 : list A) i,
    nth_error (l1 ++ l2) (length l1 + i) = nth_error l2 i.
Proof.
  intros A l1 l2 i.
  rewrite nth_error_app2.
  - rewrite Nat.add_sub_swap by lia.
    rewrite Nat.sub_diag. reflexivity.
  - lia.
Qed.

Lemma nth_error_app_assoc_offset :
  forall (A : Type) (l1 l2 l3 : list A) i,
    nth_error ((l1 ++ l2) ++ l3) (length l1 + i) = nth_error (l2 ++ l3) i.
Proof.
  intros A l1 l2 l3 i.
  rewrite <- app_assoc.
  rewrite nth_error_app_offset.
  reflexivity.
Qed.

Lemma nth_error_app3 :
  forall (A : Type) (l1 l2 l3 : list A) i,
    nth_error (l1 ++ l2 ++ l3) (length l1 + (length l2 + i)) =
    nth_error l3 i.
Proof.
  intros A l1 l2 l3 i.
  rewrite nth_error_app2 by lia.
  replace (length l1 + (length l2 + i) - length l1) with (length l2 + i) by lia.
  rewrite nth_error_app2 by lia.
  replace (length l2 + i - length l2) with i by lia.
  reflexivity.
Qed.

Lemma nth_error_app4 :
  forall (A : Type) (l1 l2 l3 l4 : list A) i,
    nth_error (l1 ++ l2 ++ l3 ++ l4)
      (length l1 + (length l2 + (length l3 + i))) =
    nth_error l4 i.
Proof.
  intros A l1 l2 l3 l4 i.
  rewrite nth_error_app2 by (repeat rewrite app_length; lia).
  replace (length l1 + (length l2 + (length l3 + i)) - length l1)
    with (length l2 + (length l3 + i)) by lia.
  rewrite nth_error_app2 by (repeat rewrite app_length; lia).
  replace (length l2 + (length l3 + i) - length l2)
    with (length l3 + i) by lia.
  rewrite nth_error_app2 by (repeat rewrite app_length; lia).
  replace (length l3 + i - length l3) with i by lia.
  reflexivity.
Qed.

Lemma nth_error_app_skip :
  forall (A : Type) (l1 l2 : list A) i,
    i < length l2 ->
    nth_error (l1 ++ l2) (length l1 + i) = nth_error l2 i.
Proof.
  intros. apply nth_error_app_offset.
Qed.

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

Let zero_len := S (max_reg_func callee).

Let zero_offset := length (fn_code caller) +
                   length (zero_regs zero_len reg_offset (length (fn_code caller))).

Let node_offset := zero_offset +
                   length (bind_params call_args (fn_params callee)
                             reg_offset zero_offset).

Definition regs_agree (rs_src rs_tgt : regset) : Prop :=
  forall r, r <= max_reg_func caller -> rs_src r = rs_tgt r.

Definition callee_regs_agree (rs_src rs_tgt : regset) : Prop :=
  forall r, r <= max_reg_func callee -> rs_src r = rs_tgt (r + reg_offset).

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
      callee_regs_agree rs_callee_src rs_tgt ->
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

Lemma nth_error_map_some :
  forall (A B : Type) (f : A -> B) l n x,
    nth_error l n = Some x ->
    nth_error (map f l) n = Some (f x).
Proof.
  intros A B f l n x Hnth.
  rewrite nth_error_map. rewrite Hnth. reflexivity.
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
Admitted.

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

(* TODO: This proof is very ugly *)
Lemma inlined_body_at : forall pc_callee instr,
  nth_error (fn_code callee) pc_callee = Some instr ->
  exists caller_f',
    nth_error p' (cs_caller cs) = Some caller_f' /\
    nth_error (fn_code caller_f') (pc_callee + node_offset) =
      Some (replace_ret (remap_nodes node_offset (remap_regs reg_offset instr))
                        reg_offset call_dst call_succ).
Proof.
Admitted.

(* Instruction at position (length (fn_code caller) + i) in modified caller
   is the i-th zero-init instruction *)
Lemma zero_regs_at : forall f_tgt i instr,
  nth_error p' (cs_caller cs) = Some f_tgt ->
  nth_error (zero_regs zero_len reg_offset (length (fn_code caller))) i = Some instr ->
  nth_error (fn_code f_tgt) (length (fn_code caller) + i) = Some instr.
Proof.
Admitted.

(* Instruction at position (length (fn_code caller) + length zero_init + i) in modified caller
   is the i-th param bind instruction *)
Lemma param_bind_at : forall f_tgt i instr,
  nth_error p' (cs_caller cs) = Some f_tgt ->
  nth_error (bind_params call_args (fn_params callee) reg_offset
               (length (fn_code caller) + zero_len)) i = Some instr ->
  nth_error (fn_code f_tgt) (length (fn_code caller) + zero_len + i) = Some instr.
Admitted.

(* The instruction at cs_pc in the modified caller is Inop jumping to param binds *)
Lemma cs_pc_in_p' : forall f_tgt,
  nth_error p' (cs_caller cs) = Some f_tgt ->
  nth_error (fn_code f_tgt) (cs_pc cs) = Some (Inop (length (fn_code caller))).
Proof.
Admitted.

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

(* When registers agree and we're in the caller, registers used in an instruction agree *)
Lemma regs_agree_on_instr : forall rs_src rs_tgt f pc instr r,
  regs_agree rs_src rs_tgt ->
  nth_error p (cs_caller cs) = Some f ->
  nth_error (fn_code f) pc = Some instr ->
  In r (used_regs instr) ->
  rs_src r = rs_tgt r.
Proof.
  intros rs_src rs_tgt f pc instr r Hagree Hf Hpc Hin.
  assert (r <= max_reg_func caller) by (
    unfold caller in *; rewrite Hf; eapply instr_regs_bounded; eauto).
  exact (Hagree r H).
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

Lemma zero_regs_acc_preserve_above :
  forall rs count x,
    reg_offset + count <= x ->
    zero_regs_acc rs count reg_offset x = rs x.
Proof.
  intros rs count.
  revert rs.
  induction count as [|count IH]; intros rs x Hx; simpl.
  - reflexivity.
  - rewrite (IH (update rs (reg_offset + count) 0) x) by lia.
    unfold update.
    destruct (Nat.eqb x (reg_offset + count)) eqn:Heq.
    + apply Nat.eqb_eq in Heq. lia.
    + reflexivity.
Qed.

Lemma zero_regs_acc_fresh_zero :
  forall rs count r,
    r < count ->
    zero_regs_acc rs count reg_offset (reg_offset + r) = 0.
Proof.
  intros rs count.
  revert rs.
  induction count as [|count IH]; intros rs r Hr.
  - lia.
  - simpl.
    destruct (Nat.eq_dec r count) as [->|Hneq].
    + rewrite zero_regs_acc_preserve_above by lia.
      unfold update. rewrite Nat.eqb_refl. reflexivity.
    + assert (Hr' : r < count) by lia.
      apply IH.
      exact Hr'.
Qed.

Lemma zero_regs_acc_preserve_low : forall rs count r,
  r <= max_reg_func caller ->
  zero_regs_acc rs count reg_offset r = rs r.
Proof.
  intros rs count.
  revert rs.
  induction count as [|count IH]; intros rs r Hr; simpl.
  - reflexivity.
  - rewrite IH by lia.
    unfold update.
    destruct (Nat.eqb r (reg_offset + count)) eqn:Heq.
    + apply Nat.eqb_eq in Heq. lia.
    + reflexivity.
Qed.

Lemma regs_agree_zero_regs_acc : forall rs_src rs_tgt count,
  regs_agree rs_src rs_tgt ->
  regs_agree rs_src (zero_regs_acc rs_tgt count reg_offset).
Proof.
  intros rs_src rs_tgt count Hagree r Hr.
  rewrite zero_regs_acc_preserve_low by exact Hr.
  apply Hagree; exact Hr.
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

Lemma update_shift_rel : forall rs0 rs prm v,
  (forall x, rs0 x = rs (x + reg_offset)) ->
  forall x,
    update rs0 prm v x = update rs (prm + reg_offset) v (x + reg_offset).
Proof.
  intros rs0 rs prm v Hrel x.
  unfold update.
  destruct (Nat.eqb x prm) eqn:Hx.
  - apply Nat.eqb_eq in Hx. subst x.
    rewrite Nat.eqb_refl. reflexivity.
  - apply Nat.eqb_neq in Hx.
    assert (Heq : (x + reg_offset =? prm + reg_offset) = false)
      by (apply Nat.eqb_neq; lia).
    rewrite Heq.
    rewrite Hrel. reflexivity.
Qed.

Lemma init_regs_acc_apply_param_binds :
  forall rs0 rs args params,
    (forall x, x <= max_reg_func callee -> rs0 x = rs (x + reg_offset)) ->
    (forall a, In a args -> a <= max_reg_func caller) ->
    forall r,
      r <= max_reg_func callee ->
      init_regs_acc rs0 (map_regs rs args) params r =
      apply_param_binds rs args params reg_offset (r + reg_offset).
Proof.
  intros rs0 rs args.
  revert rs0 rs.
  induction args as [|a args IH]; intros rs0 rs params Hrel Hargs r Hr; simpl.
  - destruct params; simpl; apply Hrel; exact Hr.
  - destruct params as [|param params]; simpl.
    + apply Hrel; exact Hr.
    + assert (Hmap : map_regs rs args =
                     map_regs (update rs (param + reg_offset) (rs a)) args).
      { unfold map_regs. apply map_ext_in. intros b Hb.
        symmetry. apply low_regs_unchanged_by_param_bind.
        apply Hargs. simpl. right. exact Hb. }
      rewrite Hmap.
      eapply (IH (update rs0 param (rs a))
                 (update rs (param + reg_offset) (rs a))
                 params).
      * intros x Hx.
        unfold update.
        destruct (Nat.eqb x param) eqn:Heq.
        { apply Nat.eqb_eq in Heq. subst x.
          rewrite Nat.eqb_refl. reflexivity. }
        { apply Nat.eqb_neq in Heq.
          assert (Hneq : (x + reg_offset =? param + reg_offset) = false)
            by (apply Nat.eqb_neq; lia).
          rewrite Hneq.
          apply Hrel. exact Hx. }
      * intros b Hb. apply Hargs. simpl. right. exact Hb.
      * exact Hr.
Qed.

Lemma init_regs_apply_param_binds :
  forall rs args params,
    (forall r, r <= max_reg_func callee -> rs (r + reg_offset) = 0) ->
    (forall a, In a args -> a <= max_reg_func caller) ->
    forall r,
      r <= max_reg_func callee ->
      init_regs (map_regs rs args) params r =
      apply_param_binds rs args params reg_offset (r + reg_offset).
Proof.
  intros rs args params Hzero Hargs r Hr.
  unfold init_regs.
  eapply init_regs_acc_apply_param_binds.
  - intros x Hx. simpl. symmetry. apply Hzero. exact Hx.
  - exact Hargs.
  - exact Hr.
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
Proof. (* temporarily commented out while the call-site proof is refactored *)
  (*
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
    2:{ eapply map_regs_agree.
        - exact Hagree.
        - rewrite Hcaller in H2. exact H2.
        - exact H9.
        - intros r Hr. simpl. right. exact Hr. }
    exact H10.

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
      2:{ assert (Hf : f_src = caller).
        { unfold caller. rewrite <- Hcaller. rewrite H2. reflexivity. }
        subst f_src.
        unfold regs_agree in H1.
        apply H1. exact Hcaller.
        apply (max_reg_func_bound _ (Icond cond ifso ifnot) pc).
        exact H9. }
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
      2:{ assert (Hf : f_src = caller).
        { unfold caller. rewrite <- Hcaller. rewrite H2. reflexivity. }
        subst f_src.
        unfold regs_agree in H1.
        apply H1. exact Hcaller.
        apply (max_reg_func_bound _ (Icond cond ifso ifnot) pc).
        exact H9. }
    match goal with
    | [ Hcond : rs_src cond = 0 |- _ ] => exact Hcond
    end.

    (* match states *)
    eapply match_normal.
    + exact H.
    + exact H0.
    + exact H1.
    + exact H2.
    + exact H3.

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
                (apply_param_binds
                   (zero_regs_acc rs_tgt zero_len reg_offset)
                   call_args (fn_params callee) reg_offset)).
      split.
      (* step through the no-op, zeroing prefix, and the call arg movements *)
      * destruct (bind_params call_args (fn_params callee) reg_offset zero_offset) eqn:Hbinds.
        -- replace (apply_param_binds
                      (zero_regs_acc rs_tgt zero_len reg_offset)
                      call_args (fn_params callee) reg_offset)
             with (zero_regs_acc rs_tgt zero_len reg_offset).
           ++ replace node_offset with zero_offset
                by (unfold node_offset; rewrite Hbinds; simpl; lia).
              eapply plus_step.
              ** apply exec_Inop. exact HInop.
              ** eapply (exec_zero_regs p' f_tgt s_tgt rs_tgt zero_len reg_offset
                           (length (fn_code caller))).
                 --- intros j instr Hnth.
                     eapply zero_regs_at; eauto.
                 --- intro Hnil.
                     apply (f_equal (@length instruction)) in Hnil.
                     rewrite length_zero_regs in Hnil. simpl in Hnil. lia.
           ++ symmetry. eapply bind_params_nil_apply_param_binds. exact Hbinds.
        -- eapply plus_trans.
           ++ eapply plus_step.
              ** apply exec_Inop. exact HInop.
              ** eapply (exec_zero_regs p' f_tgt s_tgt rs_tgt zero_len reg_offset
                           (length (fn_code caller))).
                 --- intros j instr Hnth.
                     eapply zero_regs_at; eauto.
                 --- intro Hnil.
                     apply (f_equal (@length instruction)) in Hnil.
                     rewrite length_zero_regs in Hnil. simpl in Hnil. lia.
           ++ replace (node_offset)
                with (zero_offset +
                      length (bind_params call_args (fn_params callee) reg_offset zero_offset))
                by (unfold node_offset; reflexivity).
              eapply (exec_bind_params p' f_tgt s_tgt
                        (zero_regs_acc rs_tgt zero_len reg_offset)
                        call_args (fn_params callee) reg_offset zero_offset).
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
	        assert (Hargs_bound : forall a, In a call_args -> a <= max_reg_func caller).
	        { intros a Ha.
	          rewrite Hcall_args in Ha.
	          assert (Hcf : f_src = caller) by (unfold caller; rewrite H2; reflexivity).
	          rewrite <- Hcf.
	          eapply (instr_regs_bounded f_src (cs_pc cs)
	                   (Icall call_target args' dst' succ') a).
	          - exact H9.
	          - simpl. right. exact Ha. }
	        assert (Hmap : map_regs rs_src call_args = map_regs rs_tgt call_args).
	        { rewrite Hcall_args.
	          eapply map_regs_agree.
	          - exact Hregsagree.
	          - exact H2.
	          - exact H9.
	          - intros r Hr. simpl. right. exact Hr. }
	        assert (Hcaller_eq : f_src = caller).
	        { unfold caller. rewrite H2. reflexivity. }
	        assert (Hcallee_eq : fd = callee).
	        { pose proof call_target_is_callee as Hct.
	          congruence. }
	        subst f_src fd.
        eapply match_inlined with (dst := dst') (ret_pc := succ') (pc_callee := 0).
        -- exact H.
        -- exact Hregsagree.
        -- exact H2.
        -- rewrite Hcall_args. exact H9.
        -- apply regs_agree_apply_param_binds. exact Hregsagree.
		        -- intros r.
		           rewrite <- Hcall_args.
		           rewrite Hmap.
		           apply init_regs_apply_param_binds.
		           ++ apply H2. reflexivity.
		           ++ exact Hargs_bound.
		        -- exact H3.
	      
	      (* TODO: following two cases are esentially the same, we ought to merge them into
	      one proof hopefully. *)
	    + (* different call site: not the inlined callsite, but fi = cs_caller *)
	      assert (Hdisj : fi <> cs_caller cs \/ pc <> cs_pc cs) by auto.
	      assert (Hcode_tgt : nth_error (fn_code f_tgt) pc = Some (Icall target args dst pc'))
	        by (apply (code_at_pc_preserved _ _ _ _ _ H3 H4 Hdisj H10)).
	      assert (Htgt_in_p' : exists fd_tgt, nth_error p' target = Some fd_tgt)
	        by (destruct (find_func_preserved _ _ H11) as [? | [_ ?]]; eauto).
	      destruct Htgt_in_p' as [fd_tgt Hfd_tgt].
	      assert (Hmap : map_regs rs_src args = map_regs rs_tgt args).
	      { eapply (map_regs_agree _ _ f_src pc (Icall target args dst pc'));
	        auto. rewrite <- Hcaller. assumption. intros. simpl. right. assumption. }
		      pose proof (inline_preserves_params target fd fd_tgt H11 Hfd_tgt) as Hparams.
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
    assert (Hsrc_bound : src <= max_reg_func caller).
    { eapply (instr_regs_bounded callee pc_callee (Iret src) src).
      - exact Hinstr.
      - simpl. left. reflexivity. }
    assert (Hret_val : rs_tgt (src + reg_offset) = rs_callee_src src).
    { symmetry. apply H5. exact Hsrc_bound. }
    rewrite Hcall_dst, Hcall_succ in Hcode.
    exists (State s_tgt caller_tgt ret_pc (update rs_tgt dst (rs_callee_src src))).
    split.
    + apply plus_one.
      eapply exec_Iop.
      * exact Hcode.
      * simpl. rewrite Hret_val. reflexivity.
    + eapply match_normal with
          (fi := cs_caller cs)
          (f_src := caller)
          (f_tgt := caller_tgt).
      * exact H.
      * intros Hneq. contradiction.
      * intros _. apply regs_agree_update. exact H3.
      * exact H1.
      * exact H5.
  *)
Admitted.

End INLINING_PROOF.
