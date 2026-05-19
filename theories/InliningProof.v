From VerifPerf Require Import Syntax Semantics Inlining.
From Stdlib Require Import List Nat Bool Relations.
Import ListNotations.

Section INLINING_PROOF.

Variable p : program.
Variable cs : callsite.
Variable p' : program.
Variable Hinline : inline p cs = Some p'.

(* The callee function that was inlined *)
Let callee := match nth_error p (cs_target cs) with
              | Some f => f
              | None => mk_function [] [] 0
              end.

Let caller := match nth_error p (cs_caller cs) with
              | Some f => f
              | None => mk_function [] [] 0
              end.

Let reg_offset := max_reg_func caller + 1.

(* Node offset: where the callee body starts in the inlined code *)
Let call_args := match nth_error (fn_code caller) (cs_pc cs) with
                 | Some (Icall _ args _ _) => args
                 | _ => []
                 end.
                                  
Let node_offset := length (fn_code caller) +
                   length (bind_params call_args (fn_params callee)
                             reg_offset (length (fn_code caller))).

(* Register agreement: source and target registers agree on the caller's registers.
   The inlined code uses registers above reg_offset, which the caller never touches. *)
Definition regs_agree (rs_src rs_tgt : regset) : Prop :=
  forall r, r <= max_reg_func caller -> rs_src r = rs_tgt r.

(* Stack matching: relates source stack (which has a frame for the inlined call)
   to target stack (which does not). *)
Inductive match_stacks : list stackframe -> list stackframe -> Prop :=
  | match_stacks_nil :
      match_stacks nil nil
  | match_stacks_cons : forall dst f pc rs_src rs_tgt s_src s_tgt,
      regs_agree rs_src rs_tgt ->
      match_stacks s_src s_tgt ->
      match_stacks (Stackframe dst f pc rs_src :: s_src)
                   (Stackframe dst f pc rs_tgt :: s_tgt)
.

(* match_states relates a source state (executing p) to a target state (executing p').
   Two cases:
   1. Normal: both programs are at corresponding points
   2. Inside inlined code: source has pushed a frame and is inside the callee,
      while target is still in the caller executing the spliced-in code *)
Inductive match_states : state -> state -> Prop :=
  (* Both executing the same function at the same pc *)
  | match_normal : forall s_src s_tgt f pc rs_src rs_tgt,
      match_stacks s_src s_tgt ->
      (* TODO: we could make this stronger since there is no inlining and 
      just have register state equality? *)
      regs_agree rs_src rs_tgt ->
      match_states (State s_src f pc rs_src)
                   (State s_tgt f pc rs_tgt)

  (* Source is inside the callee (has pushed a stack frame),
     target is executing the inlined body within the caller *)
  | match_inlined : forall s_src s_tgt
      (dst : reg) (ret_pc : node) (rs_caller_src rs_caller_tgt : regset)
      (pc_callee : node) (rs_callee_src rs_tgt : regset),
      (* Stacks below the inlined frame correspond *)
      match_stacks s_src s_tgt ->
      (* Caller registers agreed before the call *)
      regs_agree rs_caller_src rs_caller_tgt ->
      (* Target registers agree with callee's on the remapped registers *)
      (forall r, rs_callee_src r = rs_tgt (r + reg_offset)) ->
      (* Target is at the corresponding inlined node *)
      match_states
        (* the source is executing inside the callee at
           node pc_callee *)
        (State ((Stackframe dst caller ret_pc rs_caller_src) :: s_src)
               callee pc_callee rs_callee_src)

        (* the target is executing in the caller at the
           corresponding inlined node *)
        (State s_tgt caller (pc_callee + node_offset) rs_tgt)

  (* Both in a callstate (for calls other than the inlined one) *)
  | match_callstate : forall s_src s_tgt f args,
      match_stacks s_src s_tgt ->
      match_states (Callstate s_src f args)
                   (Callstate s_tgt f args)

  (* Both in a returnstate (for returns other than from the inlined callee) *)
  | match_returnstate : forall s_src s_tgt v,
      match_stacks s_src s_tgt ->
      match_states (Returnstate s_src v)
                   (Returnstate s_tgt v)
.

(* The main (forward) simulation theorem:
   If source steps and states match, then target steps (possibly multiple)
   and the resulting states match. *)
Theorem step_simulation :
  forall s1 s1' s2,
    match_states s1 s2 ->
    step p s1 s1' ->
    exists s2', (step p' s2 s2' \/ clos_refl_trans_1n _ (step p') s2 s2') /\
                match_states s1' s2'.
Proof.
Admitted.

End INLINING_PROOF.
