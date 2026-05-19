From VerifPerf Require Import Syntax.
From Stdlib Require Import List Nat Bool.
Import ListNotations.

Definition regset := reg -> nat.

Definition empty_regs : regset := fun _ => 0.

Definition update (rs : regset) (x : reg) (v : nat) : regset :=
  fun y => if Nat.eqb y x then v else rs y.

Fixpoint init_regs (vals : list nat) (params : list reg) : regset :=
  match params, vals with
  | p :: ps, v :: vs => update (init_regs vs ps) p v
  | _, _ => empty_regs
  end.

Definition map_regs (rs : regset) (regs : list reg) : list nat :=
  map rs regs.

(* TODO: should this just be a record? *)
Inductive stackframe : Type :=
  | Stackframe (dst : reg) (f : function) (pc : node) (rs : regset).

Inductive state : Type :=
  (* State when executing within a function `f` at `pc` with register state `rs` *)
  | State (stack : list stackframe) (f : function) (pc : node) (rs : regset)
  (* State when about to start executing a new function `f` with args `args` *)
  | Callstate (stack : list stackframe) (f : function) (args : list nat)
  (* State when a function is returning with some value `v` *)
  | Returnstate (stack : list stackframe) (v : nat).

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
             (Callstate (Stackframe dst f pc' rs :: s) fd (map_regs rs args))

  | exec_Iret : forall s f pc rs src,
      nth_error (fn_code f) pc = Some (Iret src) ->
      step p (State s f pc rs) (Returnstate s (rs src))

  | exec_function_entry : forall s f args,
      step p (Callstate s f args)
             (State s f (fn_entrypoint f) (init_regs args (fn_params f)))

  | exec_return : forall dst f pc rs s v,
      step p (Returnstate (Stackframe dst f pc rs :: s) v)
             (State s f pc (update rs dst v))
.

Definition initial_state (p : program) (s : state) : Prop :=
  exists f, nth_error p 0 = Some f /\
  s = Callstate nil f nil.

Definition final_state (s : state) (v : nat) : Prop :=
  s = Returnstate nil v.
