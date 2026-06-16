From VerifPerf Require Import Syntax.
From Stdlib Require Import List Nat Bool Lia.
Import ListNotations.

(* Maximum register used in an instruction *)
Definition max_reg_instr (i : instruction) : nat :=
  match i with
  | Inop _ => 0
  | Iop _ args dst _ => fold_left max args dst
  | Icond cond _ _ => cond
  | Icall _ args dst _ => fold_left max args dst
  | Iret src => src
  end.

(* Maximum register used in a function *)
Definition max_reg_func (f : function) : nat :=
  max (fold_left (fun acc i => max acc (max_reg_instr i)) (fn_code f) 0)
      (fold_left max (fn_params f) 0).

(* Offset all registers in an instruction *)
Definition remap_regs (offset : nat) (i : instruction) : instruction :=
  match i with
  | Inop s => Inop s
  | Iop op args dst s => Iop op (map (fun r => r + offset) args) (dst + offset) s
  | Icond cond ifso ifnot => Icond (cond + offset) ifso ifnot
  | Icall target args dst s => Icall target (map (fun r => r + offset) args) (dst + offset) s
  | Iret src => Iret (src + offset)
  end.

(* Offset all node references in an instruction *)
Definition remap_nodes (offset : nat) (i : instruction) : instruction :=
  match i with
  | Inop s => Inop (s + offset)
  | Iop op args dst s => Iop op args dst (s + offset)
  | Icond cond ifso ifnot => Icond cond (ifso + offset) (ifnot + offset)
  | Icall target args dst s => Icall target args dst (s + offset)
  | Iret src => Iret src
  end.

(* Build parameter-binding moves: Iop Oid [arg_i] (param_i + reg_offset) next_node *)
Fixpoint bind_params (args : list reg) (params : list reg) (reg_offset : nat)
    (start_node : nat) : list instruction :=
  (* TODO: if they aren't the same length, some registers will fail to get initialized. This
  will cause silent errors. as of now. *)
  match args, params with
  | a :: args_rest, p :: params_rest =>
      Iop Oid [a] (p + reg_offset) (start_node + 1) ::
      bind_params args_rest params_rest reg_offset (start_node + 1)
  | _, _ => []
  end.

(* Replace Iret in the callee body with Iop Oid [src+offset] dst succ *)
Definition replace_ret (i : instruction) (reg_offset : nat) (dst : reg) (succ : node) : instruction :=
  match i with
  | Iret src => Iop Oid [src] dst succ
  | other => other
  end.

(* Transform callee body: remap registers, remap nodes, replace returns *)
Definition transform_callee_body (body : code) (reg_offset : nat)
    (node_offset : nat) (dst : reg) (succ : node) : code :=
  map (fun i => replace_ret (remap_nodes node_offset (remap_regs reg_offset i))
                            reg_offset dst succ) body.

(* Inline a single call site within a caller function.

   Layout:  [patched_caller (len=|caller|)] [param_binds] [callee_body]
   Indices:  0..call_pc..len-1               len..         len+|binds|..

   Execution: ... -> Inop@call_pc -> param_bind_0 -> ... -> callee_entry -> ...
*)
Definition inline_call_site (caller : function) (callee : function)
    (call_pc : nat) (args : list reg) (dst : reg) (succ : node) : code :=
  let reg_offset := max_reg_func caller + 1 in
  let node_offset := length (fn_code caller) in
  let param_binds := bind_params args (fn_params callee) reg_offset node_offset in
  let callee_body := transform_callee_body (fn_code callee) reg_offset
                       (node_offset + length param_binds) dst succ in
  let patched_caller := firstn call_pc (fn_code caller)
                        ++ Inop node_offset
                        :: skipn (call_pc + 1) (fn_code caller) in
  patched_caller ++ param_binds ++ callee_body.

(* Inline a specific call site (identified by pc) within a function.
   Returns None if the pc doesn't point to an Icall. *)
Definition inline_in_func (caller : function) (callee : function)
    (call_pc : nat) : option function :=
  match nth_error (fn_code caller) call_pc with
  | Some (Icall _ args dst succ) =>
      Some (mk_function
        (fn_params caller)
        (inline_call_site caller callee call_pc args dst succ))
  | _ => None
  end.

(* Decidable leaf check *)
Definition isLeafb (f : function) : bool :=
  forallb (fun i => match i with Icall _ _ _ _ => false | _ => true end)
          (fn_code f).

(* Top-level: inline a specific call site.
   Returns None if the callsite is invalid or the target isn't a leaf. *)
(* TODO: need a rust-like ? operator that makes this def a lot prettier. *)
Definition inline (p : program) (cs : callsite) : option program :=
  match nth_error p (cs_caller cs) with
  | None => None
  | Some caller =>
      match nth_error (fn_code caller) (cs_pc cs) with
      | Some (Icall target _ _ _) =>
          match nth_error p target with
          | None => None
          | Some callee =>
              if isLeafb callee then
                match inline_in_func caller callee (cs_pc cs) with
                | None => None
                | Some caller' =>
                    Some (firstn (cs_caller cs) p ++ [caller'] ++ skipn (cs_caller cs + 1) p)
                end
              else None
          end
      | _ => None
      end
  end.

 
(* replacing `list[n]` does not change `nth_error l i` if `i <> n` *)
Lemma nth_error_replace_other : forall (A : Type) (l : list A) (n i : nat) (x : A),
  i <> n ->
  i < length l ->
  nth_error (firstn n l ++ x :: skipn (n + 1) l) i = nth_error l i.
Proof.
    intros A l n i x hNeq hLt.
    (* FIXME: why are Nat lemmas only resolving with PeanoNat.{}? *)
    destruct (PeanoNat.Nat.lt_trichotomy i n) as [Hlt_n| [Heq | Hgt_n]].
    - (* i < n *)
      rewrite nth_error_app1.
      + rewrite nth_error_firstn. 
        apply PeanoNat.Nat.ltb_lt in Hlt_n. 
        rewrite Hlt_n.
        reflexivity.
      + rewrite length_firstn. lia.
    - (* i = n *) contradiction.
    - (* i > n *)
      rewrite nth_error_app2.       
      + simpl. rewrite length_firstn.
        assert (Hmin : Nat.min n (length l) = n) by lia.
        rewrite Hmin.
          assert (Hi : i - n = S (i - n - 1)) by lia. rewrite Hi. simpl.
          rewrite nth_error_skipn.
          f_equal. lia.
      + rewrite length_firstn. 
      apply PeanoNat.Nat.min_case_strong; lia.
Qed.

Lemma nth_error_replace_same : forall (A : Type) (l : list A) (n : nat) (x : A),
  n < length l ->
  nth_error (firstn n l ++ x :: skipn (n + 1) l) n = Some x.
Proof.
  intros A l n x Hlt.
  rewrite nth_error_app2.
  - rewrite length_firstn. rewrite PeanoNat.Nat.min_l by lia.
    rewrite PeanoNat.Nat.sub_diag. reflexivity.
  - rewrite length_firstn. lia.
Qed.

Definition used_regs (i : instruction) : list reg :=
  match i with
  | Inop _ => []
  | Iop _ args dst _ => dst :: args
  | Icond cond _ _ => [cond]
  | Icall _ args dst _ => dst :: args
  | Iret src => [src]
  end.

(* `fold_left` of `max` returns at least of the base value acc *)
Lemma fold_left_max_acc : forall l acc, acc <=
  fold_left max l acc.
  Proof.
    induction l; simpl; intros.
    - lia.
    - eapply PeanoNat.Nat.le_trans. 2: apply IHl.
  lia.
Qed.

(* `fold_left` of `max` returns something >= any value in the list *)
Lemma fold_left_max_in : forall l acc r,
  In r l -> r <= fold_left max l acc.
Proof.
  induction l. simpl; intros.
  - lia.
  - intros acc r h. destruct h.
    (* a = r *)
    + rewrite <- H. simpl. eapply PeanoNat.Nat.le_trans. 
      apply PeanoNat.Nat.le_max_r. apply fold_left_max_acc.
    (* In r l *)
    + apply IHl. assumption.
Qed.

Lemma max_reg_instr_args : forall instr r,
  In r (used_regs instr) -> r <= max_reg_instr instr.
Proof.
  intros instr r hIn.
  unfold max_reg_instr.
  destruct instr; simpl in hIn; try contradiction;
    destruct hIn;
    first [ subst; apply fold_left_max_acc
          | apply fold_left_max_in; assumption
          | lia
          | contradiction ].
Qed.

Lemma fold_left_max_fun_acc : forall (A : Type) (g : A -> nat) l acc,
  acc <= fold_left (fun a i => max a (g i)) l acc.
Proof.
  induction l; simpl; intros.
  - lia.
  - eapply PeanoNat.Nat.le_trans. 2: apply IHl. lia.
Qed.

Lemma fold_left_max_fun_in : forall (A : Type) (g : A -> nat) l acc x,
  In x l -> g x <= fold_left (fun a i => max a (g i)) l acc.
Proof.
  induction l; simpl; intros.
  - contradiction.
  - destruct H.
    + subst. eapply PeanoNat.Nat.le_trans.
      2: apply fold_left_max_fun_acc.
      lia.
    + apply IHl. assumption.
Qed.

Lemma max_reg_func_bound : forall f instr pc,
  nth_error (fn_code f) pc = Some instr ->
  max_reg_instr instr <= max_reg_func f.
Proof.
  intros f instr pc hInstr.
  unfold max_reg_func.
  eapply PeanoNat.Nat.le_trans.
  - apply fold_left_max_fun_in. eapply nth_error_In; eauto.
  - apply PeanoNat.Nat.le_max_l.
Qed.

Lemma instr_regs_bounded : forall f pc instr r,
  nth_error (fn_code f) pc = Some instr ->
  In r (used_regs instr) ->
  r <= max_reg_func f.
Proof.
  intros. eapply PeanoNat.Nat.le_trans.
  - eapply max_reg_instr_args; eauto.
  - eapply max_reg_func_bound; eauto.
Qed.

Lemma max_reg_func_param_bound : forall f r,
  In r (fn_params f) ->
  r <= max_reg_func f.
Proof.
  intros f r Hr.
  unfold max_reg_func.
  apply PeanoNat.Nat.le_trans with (m := fold_left max (fn_params f) 0).
  - apply fold_left_max_in. exact Hr.
  - apply PeanoNat.Nat.le_max_r.
Qed.
