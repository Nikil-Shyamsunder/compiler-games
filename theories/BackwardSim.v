From VerifPerf Require Import Syntax Semantics Inlining InliningProof.
From Stdlib Require Import List Nat Bool Arith Lia.
Import ListNotations.

(** ** Determinism of the operational semantics *)

Lemma step_deterministic : forall pr s s1 s2,
  step pr s s1 -> step pr s s2 -> s1 = s2.
Proof.
  intros pr s s1 s2 H1 H2.
  inversion H1; subst; inversion H2; subst; congruence.
Qed.

(** ** Counted multi-step relation (provides the stutter measure) *)

Inductive starN {C : Type} (R : C -> C -> Prop) : nat -> C -> C -> Prop :=
| starN_refl : forall c, starN R 0 c c
| starN_step : forall n c1 c2 c3,
    R c1 c2 -> starN R n c2 c3 -> starN R (S n) c1 c3.

Lemma starN_inv_O : forall {C} (R : C -> C -> Prop) c1 c2,
  starN R 0 c1 c2 -> c1 = c2.
Proof. intros C R c1 c2 H. inversion H. reflexivity. Qed.

Lemma starN_inv_S : forall {C} (R : C -> C -> Prop) n c1 c3,
  starN R (S n) c1 c3 -> exists c2, R c1 c2 /\ starN R n c2 c3.
Proof. intros C R n c1 c3 H. inversion H; subst. eauto. Qed.

Lemma plus_starN : forall {C} (R : C -> C -> Prop) c1 c2,
  plus R c1 c2 -> exists n, starN R (S n) c1 c2.
Proof.
  induction 1.
  - exists 0. eapply starN_step; [eassumption | constructor].
  - destruct IHplus as [n Hn]. exists (S n). eapply starN_step; eassumption.
Qed.

(** ** Backward match: source [a] matches a target state [b] that is exactly
       [m] target steps "behind" a synchronisation point [bend]. *)

Definition bmatch {A B : Type} (step2 : B -> B -> Prop)
    (match_st : A -> B -> Prop) (a : A) (b : B) (m : nat) : Prop :=
  exists bend, starN step2 m b bend /\ match_st a bend.

(** ** Meta-theorem: forward simulation + target determinism + source
       progress yields a backward simulation with a stuttering measure. *)

Theorem forward_det_to_backward :
  forall (A B : Type) (step1 : A -> A -> Prop) (step2 : B -> B -> Prop)
         (match_st : A -> B -> Prop),
  (* forward simulation (plus on the target) *)
  (forall a a' b, match_st a b -> step1 a a' ->
     exists b', plus step2 b b' /\ match_st a' b') ->
  (* the target is deterministic *)
  (forall b b1 b2, step2 b b1 -> step2 b b2 -> b1 = b2) ->
  (* source progress (unlabelled analogue of receptiveness) *)
  (forall a b, match_st a b -> (exists b', step2 b b') -> exists a', step1 a a') ->
  forall a b m, bmatch step2 match_st a b m ->
  forall b'', step2 b b'' ->
    (exists a' m', plus step1 a a' /\ bmatch step2 match_st a' b'' m')
    \/ (exists m', bmatch step2 match_st a b'' m' /\ m' < m).
Proof.
  intros A B step1 step2 match_st FS DET PROG a b m [bend [Hstar Hmatch]] b'' Hstep.
  destruct m as [|m].
  - (* synced: [b = bend], so the source must move (progress) *)
    apply starN_inv_O in Hstar. subst bend.
    destruct (PROG _ _ Hmatch (ex_intro _ _ Hstep)) as [a' Hstep1].
    destruct (FS _ _ _ Hmatch Hstep1) as [bf [Hplus Hmf]].
    apply plus_starN in Hplus. destruct Hplus as [n Hn].
    apply starN_inv_S in Hn. destruct Hn as [cmid [Hs1 Hrest]].
    assert (cmid = b'') by (eapply DET; eauto). subst cmid.
    left. exists a', n. split.
    + apply plus_one. exact Hstep1.
    + exists bf. split; [exact Hrest | exact Hmf].
  - (* stuttering: the target advances one step inside the current block *)
    apply starN_inv_S in Hstar. destruct Hstar as [cmid [Hs1 Hrest]].
    assert (cmid = b'') by (eapply DET; eauto). subst cmid.
    right. exists m. split.
    + exists bend. split; [exact Hrest | exact Hmatch].
    + lia.
Qed.

(** ** Instantiation to the inlining transformation *)

Section CONCRETE.

Variables (p : program) (cs : callsite) (p' : program).
Hypothesis Hinline : inline p cs = Some p'.

Theorem inlining_backward_simulation :
  wf_program p ->
  forall s1 s2 m, state_valid p s1 ->
  bmatch (step p') (match_states p cs p') s1 s2 m ->
  forall s2', step p' s2 s2' ->
    (exists s1' m', plus (step p) s1 s1'
                    /\ bmatch (step p') (match_states p cs p') s1' s2' m')
    \/ (exists m', bmatch (step p') (match_states p cs p') s1 s2' m' /\ m' < m).
Proof.
  intros Hwf s1 s2 m Hvalid [bend [Hstar Hmatch]] s2' Hstep.
  destruct m as [|m].
  - apply starN_inv_O in Hstar. subst bend.
    destruct (match_states_progress_wf p cs p' Hinline Hwf
                s1 s2 Hmatch Hvalid (ex_intro _ _ Hstep)) as [s1' Hstep1].
    destruct (step_simulation p cs p' Hinline s1 s1' s2 Hmatch Hstep1)
      as [sf [Hplus Hmf]].
    apply plus_starN in Hplus. destruct Hplus as [n Hn].
    apply starN_inv_S in Hn. destruct Hn as [smid [Hs1 Hrest]].
    assert (smid = s2') by (eapply step_deterministic; eauto). subst smid.
    left. exists s1', n. split.
    + apply plus_one. exact Hstep1.
    + exists sf. split; [exact Hrest | exact Hmf].
  - apply starN_inv_S in Hstar. destruct Hstar as [smid [Hs1 Hrest]].
    assert (smid = s2') by (eapply step_deterministic; eauto). subst smid.
    right. exists m. split.
    + exists bend. split; [exact Hrest | exact Hmatch].
    + lia.
Qed.

End CONCRETE.
