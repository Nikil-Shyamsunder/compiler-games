From Stdlib Require Import List Arith.
From VerifPerf Require Import Syntax Inlining Main.
Import ListNotations.

Module MainExamples.
  Definition source : program :=
    [mk_function []
       [Icall 1 [] 0 1; Icall 1 [] 0 2; Icall 2 [] 0 3; Iret 0];
     mk_function [] [Iret 0];
     mk_function [] [Icall 1 [] 0 1; Iret 0]].

  (** Calling function 2 is excluded because it is not initially a leaf. *)
  Example extracts_only_valid_leaf_sites :
    candidate_sites source =
      [mk_callsite 0 0; mk_callsite 0 1; mk_callsite 2 0].
  Proof. vm_compute. reflexivity. Qed.

  (** Inlining occupies shared resource 0 with latency equal to its load;
      leaving the call intact costs 2 on a private resource. *)
  Definition uses (i : nat) (bi : bool) (r : nat) : bool :=
    if bi then Nat.eqb r 0 else Nat.eqb r (S i).
  Definition slope (r : nat) : nat := if Nat.eqb r 0 then 1 else 0.
  Definition offset (r : nat) : nat := if Nat.eqb r 0 then 0 else 2.

  Definition selected (initial : profile) : profile :=
    select_profile 3 4 uses slope offset initial.

  Example selects_an_improving_inline :
    map (selected (fun _ => false)) [0; 1; 2] = [false; false; true].
  Proof. vm_compute. reflexivity. Qed.

  Example retracts_a_congested_inline :
    map (selected (fun _ => true)) [0; 1; 2] = [true; true; false].
  Proof. vm_compute. reflexivity. Qed.

  Example compiles_selected_inline_using_the_actual_pass :
    pass source 4 uses slope offset
      (fun _ => false) = inline source (mk_callsite 2 0).
  Proof. vm_compute. reflexivity. Qed.

  (** Starting from all-inline does not leave the retracted call inlined:
      emission starts from [source] and only applies the two selected passes. *)
  Example rebuilds_after_retraction :
    pass source 4 uses slope offset
      (fun _ => true) =
    match inline source (mk_callsite 0 0) with
    | Some q => inline q (mk_callsite 0 1)
    | None => None
    end.
  Proof. vm_compute. reflexivity. Qed.

  Example rejects_invalid_selected_sites :
    compile_profile source [mk_callsite 0 2] (fun _ => true) = None.
  Proof. vm_compute. reflexivity. Qed.

  Example leaves_unselected_sites_intact :
    compile_profile source (candidate_sites source) (fun _ => false) = Some source.
  Proof. vm_compute. reflexivity. Qed.
End MainExamples.
