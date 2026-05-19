From VerifPerf Require Import Syntax.
From Stdlib Require Import List Nat Bool.
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
  fold_left (fun acc i => max acc (max_reg_instr i)) (fn_code f) 0.

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
  match args, params with
  | a :: args_rest, p :: params_rest =>
      Iop Oid [a] (p + reg_offset) (start_node + 1) ::
      bind_params args_rest params_rest reg_offset (start_node + 1)
  | _, _ => []
  end.

(* Replace Iret in the callee body with Iop Oid [src+offset] dst succ *)
Definition replace_ret (i : instruction) (reg_offset : nat) (dst : reg) (succ : node) : instruction :=
  match i with
  | Iret src => Iop Oid [src + reg_offset] dst succ
  | other => other
  end.

(* Transform callee body: remap registers, remap nodes, replace returns *)
Definition transform_callee_body (body : code) (reg_offset : nat)
    (node_offset : nat) (dst : reg) (succ : node) : code :=
  map (fun i => replace_ret (remap_nodes node_offset (remap_regs reg_offset i))
                            reg_offset dst succ) body.

(* Inline a single call site within a caller function.
   - caller: the function containing the call
   - callee: the leaf function to inline
   - call_pc: the node in caller where the Icall is
   - args: argument registers at the call site
   - dst: destination register for the return value
   - succ: successor node after the call *)
Definition inline_call_site (caller : function) (callee : function)
    (call_pc : nat) (args : list reg) (dst : reg) (succ : node) : code :=
  let reg_offset := max_reg_func caller + 1 in
  let node_offset := length (fn_code caller) in
  let param_binds := bind_params args (fn_params callee) reg_offset node_offset in
  let callee_body := transform_callee_body (fn_code callee) reg_offset
                       (node_offset + length param_binds) dst succ in
  let fix patch (c : list instruction) (pc : nat) :=
    match c with
    | [] => []
    | i :: rest =>
        (if Nat.eqb pc call_pc then Inop node_offset else i)
        :: patch rest (pc + 1)
    end
  in
  patch (fn_code caller) 0 ++ param_binds ++ callee_body.

(* Inline a specific call site (identified by pc) within a function.
   Returns None if the pc doesn't point to an Icall. *)
Definition inline_in_func (caller : function) (callee : function)
    (call_pc : nat) : option function :=
  match nth_error (fn_code caller) call_pc with
  | Some (Icall _ args dst succ) =>
      Some (mk_function
        (fn_params caller)
        (inline_call_site caller callee call_pc args dst succ)
        (fn_entrypoint caller))
  | _ => None
  end.

(* Decidable leaf check *)
Definition isLeafb (f : function) : bool :=
  forallb (fun i => match i with Icall _ _ _ _ => false | _ => true end)
          (fn_code f).

(* Top-level: inline a specific call site.
   Returns None if the callsite is invalid or the target isn't a leaf. *)
Definition inline (p : program) (cs : callsite) : option program :=
  match nth_error p (cs_target cs) with
  | None => None
  | Some callee =>
      if isLeafb callee then
        match nth_error p (cs_caller cs) with
        | None => None
        | Some caller =>
            match inline_in_func caller callee (cs_pc cs) with
            | None => None
            | Some caller' =>
                Some (firstn (cs_caller cs) p ++ [caller'] ++ skipn (cs_caller cs + 1) p)
            end
        end
      else None
  end.
