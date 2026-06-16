From Stdlib Require Import List Nat Bool.
Import ListNotations.

Definition node := nat.
Definition reg := nat.

Inductive value : Type :=
  | Vundef
  | Vnat (n : nat).

Definition value_eqb (v1 v2 : value) : bool :=
  match v1, v2 with
  | Vundef, Vundef => true
  | Vnat n1, Vnat n2 => Nat.eqb n1 n2
  | _, _ => false
  end.

Inductive operation : Type :=
  | Oconst (n : nat)
  | Oadd | Osub | Omul | Odiv
  | Oeq | Olt | Ogt
  | Onot | Oid
.

Definition eval_op (op : operation) (args : list value) : option value :=
  let lift1 (f : nat -> nat) (v : value) :=
    match v with
    | Vundef => Vundef
    | Vnat n => Vnat (f n)
    end in
  let lift2 (f : nat -> nat -> nat) (v1 v2 : value) :=
    match v1, v2 with
    | Vnat n1, Vnat n2 => Vnat (f n1 n2)
    | _, _ => Vundef
    end in
  match op, args with
  | Oconst n, nil => Some (Vnat n)
  | Oadd, v1::v2::nil => Some (lift2 Nat.add v1 v2)
  | Osub, v1::v2::nil => Some (lift2 Nat.sub v1 v2)
  | Omul, v1::v2::nil => Some (lift2 Nat.mul v1 v2)
  | Odiv, v1::v2::nil =>
      match v1, v2 with
      | Vnat _, Vnat 0 => None
      | Vnat n1, Vnat n2 => Some (Vnat (n1 / n2))
      | _, _ => Some Vundef
      end
  | Oeq, v1::v2::nil =>
      match v1, v2 with
      | Vnat n1, Vnat n2 => Some (Vnat (if Nat.eqb n1 n2 then 1 else 0))
      | _, _ => Some Vundef
      end
  | Olt, v1::v2::nil =>
      match v1, v2 with
      | Vnat n1, Vnat n2 => Some (Vnat (if Nat.ltb n1 n2 then 1 else 0))
      | _, _ => Some Vundef
      end
  | Ogt, v1::v2::nil =>
      match v1, v2 with
      | Vnat n1, Vnat n2 => Some (Vnat (if Nat.ltb n2 n1 then 1 else 0))
      | _, _ => Some Vundef
      end
  | Onot, v1::nil =>
      match v1 with
      | Vnat n => Some (Vnat (if Nat.eqb n 0 then 1 else 0))
      | Vundef => Some Vundef
      end
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
}.

Definition program := list function.

Record callsite := mk_callsite {
  cs_caller : nat;
  cs_pc : node;
}.

Definition isLeaf (f : function) : Prop :=
  Forall (fun i => match i with Icall _ _ _ _ => False | _ => True end)
         (fn_code f).
