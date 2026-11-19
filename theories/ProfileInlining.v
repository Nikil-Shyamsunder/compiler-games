(** Compile any profile of valid leaf-inlining decisions.

    This module proves totality and preservation of execution for every
    profile. It is independent of the selection policy and cost objective. *)
From Stdlib Require Import List Bool Arith Lia.
From VerifPerf Require Import Syntax Semantics Inlining InliningProof
  InliningCorrectness.
Import ListNotations.

Definition collect_callsites (p : program) : list callsite :=
  flat_map
    (fun cf =>
       let '(c, f) := cf in
       flat_map
         (fun pi =>
            let '(pc, instr) := pi in
            match instr with
            | Icall _ _ _ _ => [ mk_callsite c pc ]
            | _ => []
            end)
         (combine (seq 0 (length (fn_code f))) (fn_code f)))
    (combine (seq 0 (length p)) p).

(** Each successful invocation of the existing pass is recorded in a trace. *)
Inductive inline_trace : program -> program -> Prop :=
| trace_refl : forall p, inline_trace p p
| trace_cons : forall p cs q r,
    inline p cs = Some q -> inline_trace q r -> inline_trace p r.

Fixpoint compile_from (p : program) (sites : list callsite)
    (s : nat -> bool) (i : nat) : option program :=
  match sites with
  | [] => Some p
  | cs :: rest =>
      if s i then
        match inline p cs with
        | Some q => compile_from q rest s (S i)
        | None => None
        end
      else compile_from p rest s (S i)
  end.

Definition compile_profile p sites s := compile_from p sites s 0.

(** Valid leaf calls at distinct original addresses remain valid when another
    such call is inlined: existing caller addresses are preserved, and a leaf
    callee cannot itself be the caller of an inline operation. *)
Definition valid_site (p : program) (cs : callsite) : Prop :=
  exists caller target args dst succ callee,
    nth_error p (cs_caller cs) = Some caller /\
    nth_error (fn_code caller) (cs_pc cs) = Some (Icall target args dst succ) /\
    nth_error p target = Some callee /\ isLeafb callee = true.

Lemma leaf_has_no_call f pc target args dst succ :
  isLeafb f = true ->
  nth_error (fn_code f) pc = Some (Icall target args dst succ) -> False.
Proof.
  intros Hleaf Hcall. unfold isLeafb in Hleaf.
  apply forallb_forall with (x := Icall target args dst succ) in Hleaf.
  - discriminate.
  - eapply nth_error_In; exact Hcall.
Qed.

Lemma valid_site_inline p cs :
  valid_site p cs <-> exists q, inline p cs = Some q.
Proof.
  split.
  - intros (caller & target & args & dst & succ & callee &
             Hcaller & Hcall & Hcallee & Hleaf).
    unfold inline. rewrite Hcaller, Hcall, Hcallee, Hleaf.
    unfold inline_in_func. rewrite Hcall. eexists; reflexivity.
  - intros [q Hinline]. unfold inline in Hinline.
    destruct (nth_error p (cs_caller cs)) as [caller|] eqn:Hcaller;
      try discriminate.
    destruct (nth_error (fn_code caller) (cs_pc cs)) as [instr|] eqn:Hcall;
      try discriminate.
    destruct instr; try discriminate.
    destruct (nth_error p target_func) as [callee|] eqn:Hcallee;
      try discriminate.
    destruct (isLeafb callee) eqn:Hleaf; try discriminate.
    unfold valid_site. eexists; eexists; eexists; eexists; eexists; eexists.
    repeat split; eassumption.
Qed.

Lemma inline_preserves_leaf p done q target callee :
  inline p done = Some q ->
  nth_error p target = Some callee -> isLeafb callee = true ->
  nth_error q target = Some callee.
Proof.
  intros Hinline Hcallee Hleaf.
  assert (Hvalid : valid_site p done).
  { apply valid_site_inline. eauto. }
  destruct Hvalid as (caller & t & args & dst & succ & f &
                      Hcaller & Hcall & _).
  assert (Hne : target <> cs_caller done).
  { intros Heq. rewrite Heq in Hcallee.
    rewrite Hcaller in Hcallee. inversion Hcallee; subst caller.
    eapply leaf_has_no_call; eauto. }
  eapply other_func_preserved; eauto.
  apply nth_error_Some. rewrite Hcallee. discriminate.
Qed.

Lemma inline_preserves_valid_site p done q cs :
  inline p done = Some q -> cs <> done ->
  valid_site p cs -> valid_site q cs.
Proof.
  intros Hinline Hne
    (caller & target & args & dst & succ & callee &
     Hcaller & Hcall & Hcallee & Hleaf).
  assert (Hcallee' : nth_error q target = Some callee).
  { eapply inline_preserves_leaf; eauto. }
  assert (Hdistinct : cs_caller cs <> cs_caller done \/ cs_pc cs <> cs_pc done).
  { destruct (Nat.eq_dec (cs_caller cs) (cs_caller done)); [|auto].
    right. intros Hpc. apply Hne. destruct cs, done; simpl in *; congruence. }
  assert (Hcaller' : exists f, nth_error q (cs_caller cs) = Some f).
  { destruct (Nat.eq_dec (cs_caller cs) (cs_caller done)) as [Heq|Hneq].
    - rewrite Heq. eapply caller_in_p'; exact Hinline.
    - exists caller. eapply other_func_preserved; eauto.
      apply nth_error_Some. rewrite Hcaller. discriminate. }
  destruct Hcaller' as [caller' Hcaller'].
  exists caller', target, args, dst, succ, callee.
  repeat split; try assumption.
  exact (code_at_pc_preserved p done q Hinline (cs_caller cs) caller caller'
    (cs_pc cs) (Icall target args dst succ) Hcaller Hcaller' Hdistinct Hcall).
Qed.

Theorem compile_from_total sites :
  NoDup sites -> forall p s i,
    Forall (valid_site p) sites ->
    exists q, compile_from p sites s i = Some q.
Proof.
  intros Hnodup. induction Hnodup as [|cs rest Hnotin Hnodup IH];
    intros p s i Hvalid; simpl.
  - eexists; reflexivity.
  - inversion Hvalid as [|? ? Hsite Hrest]; subst.
    destruct (s i).
    + apply valid_site_inline in Hsite. destruct Hsite as [r Hinline].
      rewrite Hinline. apply IH.
      apply Forall_forall. intros cs' Hin.
      eapply inline_preserves_valid_site; [exact Hinline| |].
      * intros Heq; subst cs'. contradiction.
      * rewrite Forall_forall in Hrest. apply Hrest; assumption.
    + apply IH. exact Hrest.
Qed.

Definition callsite_eq_dec (x y : callsite) : {x = y} + {x <> y}.
Proof. decide equality; apply Nat.eq_dec. Defined.

(** Extract candidates using the actual pass's validity check. Deduplication
    ensures that a selected original call is never requested twice. *)
Definition candidate_sites (p : program) : list callsite :=
  nodup callsite_eq_dec
    (filter (fun cs => match inline p cs with Some _ => true | None => false end)
      (collect_callsites p)).

Theorem candidate_sites_valid p :
  NoDup (candidate_sites p) /\ Forall (valid_site p) (candidate_sites p).
Proof.
  split.
  - apply NoDup_nodup.
  - apply Forall_forall. intros cs Hin.
    unfold candidate_sites in Hin. apply nodup_In in Hin.
    apply filter_In in Hin. destruct Hin as [_ Hcheck].
    apply valid_site_inline.
    destruct (inline p cs) as [q|] eqn:Hinline; [eauto|discriminate].
Qed.

Corollary candidate_profiles_compile p s :
  exists q, compile_profile p (candidate_sites p) s = Some q.
Proof.
  destruct (candidate_sites_valid p) as [Hnodup Hvalid].
  apply compile_from_total; assumption.
Qed.

Lemma compile_from_trace sites : forall p s i q,
  compile_from p sites s i = Some q -> inline_trace p q.
Proof.
  induction sites as [|cs rest IH]; intros p s i q Hcompile; simpl in Hcompile.
  - inversion Hcompile; constructor.
  - destruct (s i).
    + destruct (inline p cs) as [r|] eqn:Hinline; try discriminate.
      eapply trace_cons; [exact Hinline|]. eapply IH; exact Hcompile.
    + eapply IH; exact Hcompile.
Qed.

(** Composition of the existing forward simulations. [trace_match] records
    the matching intermediate states needed by each single-pass theorem. *)
Inductive trace_match : program -> program -> state -> state -> Prop :=
| trace_match_refl : forall p x, trace_match p p x x
| trace_match_cons : forall p cs q r x y z,
    inline p cs = Some q ->
    match_states p cs q x y ->
    trace_match q r y z ->
    trace_match p r x z.

Theorem trace_forward_simulation : forall p q x y,
  trace_match p q x y ->
  forall x', reachable p x x' ->
    exists y', reachable q y y' /\ trace_match p q x' y'.
Proof.
  intros p q x y Hmatch.
  induction Hmatch as [p x|p cs q r x y z Hinline Hsingle Htail IH];
    intros x' Hreach.
  - exists x'. split; [exact Hreach|constructor].
  - destruct (inlining_forward_reachable p cs q x y x'
                Hinline Hsingle Hreach) as [y' [Hreach' Hsingle']].
    destruct (IH y' Hreach') as [z' [Hreach'' Htail']].
    exists z'. split; [exact Hreach''|].
    eapply trace_match_cons; eauto.
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

Lemma trace_initial_match p q :
  inline_trace p q -> forall x,
    initial_state p x ->
    exists y, initial_state q y /\ trace_match p q x y.
Proof.
  intros Htrace. induction Htrace as [p|p cs q r Hinline Htail IH];
    intros x Hinit.
  - exists x. split; [assumption|constructor].
  - destruct (inline_initial_match p cs q x Hinline Hinit)
      as [y [Hinity Hmatch]].
    destruct (IH y Hinity) as [z [Hinitz Hmatches]].
    exists z. split; [assumption|]. eapply trace_match_cons; eauto.
Qed.

Theorem inline_trace_forward p q :
  inline_trace p q -> forall x,
    initial_state p x ->
    exists y, initial_state q y /\
      forall x', reachable p x x' ->
        exists y', reachable q y y' /\ trace_match p q x' y'.
Proof.
  intros Htrace x Hinit.
  destruct (trace_initial_match p q Htrace x Hinit) as [y [Hinity Hmatch]].
  exists y. split; [assumption|].
  intros x' Hreach. eapply trace_forward_simulation; eauto.
Qed.

(** Every profile is safe, independently of how it was selected. *)
Definition preserves_execution (p q : program) : Prop :=
  forall x, initial_state p x ->
    exists y, initial_state q y /\
      forall x', reachable p x x' ->
        exists y', reachable q y y' /\ trace_match p q x' y'.

Theorem compile_profile_correct p s :
  exists q, compile_profile p (candidate_sites p) s = Some q /\
    preserves_execution p q.
Proof.
  destruct (candidate_profiles_compile p s) as [q Hcompile].
  exists q. split; [exact Hcompile|].
  assert (Htrace : inline_trace p q).
  { eapply compile_from_trace; exact Hcompile. }
  exact (inline_trace_forward p q Htrace).
Qed.
