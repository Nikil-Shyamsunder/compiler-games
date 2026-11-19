(** * Verified inlining pass

    [SocialCost] is the objective we optimize. Its interpretation as the
    desired objective is part of the model, not a separate proof hypothesis.
    Compilation is correct for every profile; the policy chooses one with
    the required objective bound. *)
From VerifPerf Require Export ProfileInlining CongestionGame.
From VerifPerf Require Import Syntax.
From Stdlib Require Import List.

Section Pass.
  Variable source : program.
  Variable E : nat.
  Variable uses : nat -> bool -> nat -> bool.
  Variables a b : nat -> nat.

  Let sites := candidate_sites source.
  Let N := length sites.

  (** Select profile uses the game-theoretic procedure to find a profile *)
  Definition selected_profile (initial : profile) : profile :=
    select_profile N E uses a b initial.

  (** compiles (inlines) using the selected profile *)
  Definition pass (initial : profile) : option program :=
    compile_profile source sites (selected_profile initial).

  Theorem pass_correct initial :
    exists q, pass initial = Some q /\ preserves_execution source q.
  Proof. apply compile_profile_correct. Qed.

  (** Compare against every profile over the same original candidate set, and we are no worse than 2.5 *)
  Theorem pass_cost initial :
    forall alternative,
      2 * SocialCost N E uses a b (selected_profile initial) <=
      5 * SocialCost N E uses a b alternative.
  Proof.
    intros alternative. apply price_of_anarchy. apply select_profile_PNE.
  Qed.
End Pass.
