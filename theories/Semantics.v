From VerifPerf Require Import Syntax.
From Stdlib Require Import List Nat Bool.
Import ListNotations.

Definition regset := reg -> nat.

Definition empty_regs : regset := fun _ => 0.

Definition update (rs : regset) (x : reg) (v : nat) : regset :=
  fun y => if Nat.eqb y x then v else rs y.

Fixpoint init_regs_acc (rs : regset) (vals : list nat) (params : list reg) : regset :=
  match params, vals with
  | p :: ps, v :: vs => init_regs_acc (update rs p v) vs ps
  | _, _ => rs
  end.

Definition init_regs (vals : list nat) (params : list reg) : regset :=
  init_regs_acc empty_regs vals params.

Definition map_regs (rs : regset) (regs : list reg) : list nat :=
  map rs regs.

(* TODO: should this just be a record? *)
Inductive stackframe : Type :=
  | Stackframe (dst : reg) (f : function) (pc : node) (rs : regset).

Inductive state : Type :=
  (* State when executing within a function `f` at `pc` with register state `rs` *)
  | State (stack : list stackframe) (f : function) (pc : node) (rs : regset).

Inductive step (p : program) : state -> state -> Prop :=
  | exec_Inop : forall s f pc rs pc',
      nth_error (fn_code f) pc = Some (Inop pc') ->
      step p (State s f pc rs) (State s f pc' rs)

  | exec_Iop : forall s f pc rs op args dst pc' v,
      nth_error (fn_code f) pc = Some (Iop op args dst pc') ->
      eval_op op (map_regs rs args) = Some v ->
      step p (State s f pc rs) (State s f pc' (update rs dst v))

  | exec_Icond_true : forall s f pc rs cond ifso ifnot,
      nth_error (fn_code f) pc = Some (Icond cond ifso ifnot) ->
      rs cond <> 0 ->
      step p (State s f pc rs) (State s f ifso rs)

  | exec_Icond_false : forall s f pc rs cond ifso ifnot,
      nth_error (fn_code f) pc = Some (Icond cond ifso ifnot) ->
      rs cond = 0 ->
      step p (State s f pc rs) (State s f ifnot rs)

  | exec_Icall : forall s f pc rs target args dst pc' fd,
      nth_error (fn_code f) pc = Some (Icall target args dst pc') ->
      nth_error p target = Some fd ->
      step p (State s f pc rs)
             (State (Stackframe dst f pc' rs :: s) fd
                    0
                    (init_regs (map_regs rs args) (fn_params fd)))

  | exec_Iret : forall dst f_caller ret_pc rs_caller s f pc rs src,
      nth_error (fn_code f) pc = Some (Iret src) ->
      step p (State (Stackframe dst f_caller ret_pc rs_caller :: s) f pc rs)
             (State s f_caller ret_pc (update rs_caller dst (rs src)))
.

Definition initial_state (p : program) (s : state) : Prop :=
  exists f, nth_error p 0 = Some f /\
  s = State nil f 0 (init_regs nil (fn_params f)).

Definition final_state (s : state) (v : nat) : Prop :=
  exists f pc rs src,
    s = State nil f pc rs /\
    nth_error (fn_code f) pc = Some (Iret src) /\
    v = rs src.
