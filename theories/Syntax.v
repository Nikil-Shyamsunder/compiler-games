From Stdlib Require Import List Nat Bool.
Import ListNotations.

Definition node := nat.
Definition reg := nat.

Inductive operation : Type :=
  | Oconst (n : nat)
  | Oadd | Osub | Omul | Odiv
  | Oeq | Olt | Ogt
  | Onot | Oid
.

Definition eval_op (op : operation) (args : list nat) : option nat :=
  match op, args with
  | Oconst n, nil => Some n
  | Oadd, v1::v2::nil => Some (v1 + v2)
  | Osub, v1::v2::nil => Some (v1 - v2)
  | Omul, v1::v2::nil => Some (v1 * v2)
  | Odiv, v1::v2::nil => if Nat.eqb v2 0 then None else Some (v1 / v2)
  | Oeq, v1::v2::nil => Some (if Nat.eqb v1 v2 then 1 else 0)
  | Olt, v1::v2::nil => Some (if Nat.ltb v1 v2 then 1 else 0)
  | Ogt, v1::v2::nil => Some (if Nat.ltb v2 v1 then 1 else 0)
  | Onot, v1::nil => Some (if Nat.eqb v1 0 then 1 else 0)
  | Oid, v1::nil => Some v1
  | _, _ => None
  end.

Inductive instruction : Type :=
  | Inop (succ : node)
  | Iop (op : operation) (args : list reg) (dst : reg) (succ : node)
  | Icond (cond : reg) (ifso ifnot : node)
  (* `target_func` indexes into the program *)
  | Icall (target_func : nat) (args : list reg) (dst : reg) (succ : node)
  | Iret (src : reg)
.

Definition code := list instruction.

Record function := mk_function {
  fn_params : list reg;
  fn_code : code;
  fn_entrypoint : node;
}.

Definition program := list function.

Record callsite := mk_callsite {
  cs_caller : nat;
  cs_pc : node;
}.

Definition isLeaf (f : function) : Prop :=
  Forall (fun i => match i with Icall _ _ _ _ => False | _ => True end)
         (fn_code f).
