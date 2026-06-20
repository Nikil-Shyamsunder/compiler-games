(** * CongestionGame.v

    Inlining-as-congestion-game layer (self-contained, plain Stdlib [nat]).

    See CONGESTION_GAME_PLAN.md for the full design.  This file currently
    contains ONLY the definitions and the three top-level theorems, all
    [Admitted].  Helper lemmas are added afterwards, bottom-up.

    Model: players = candidate call sites; strategy = [bool] ([true] = inline);
    resources = I-cache lines [0..E-1]; resource costs linear over [nat]
    ([rcost r x = a r * x + b r]).

    Top-level results:
      (GOAL 1) [step_decreases_Phi] : every improving best-response move
               strictly decreases the Rosenthal potential.
      (GOAL 2) [convergence] / [exists_PNE] : iterative best response reaches,
               and hence there exists, a pure Nash equilibrium.
      (GOAL 3) [price_of_anarchy] : every pure Nash equilibrium has social cost
               at most 5/2 the optimum, i.e. [2*Cost(nash) <= 5*Cost(opt)]. *)

From Stdlib Require Import List Nat Bool Lia Arith Relations Wf_nat.
From VerifPerf Require Import Syntax.
Import ListNotations.

(** [Sum n f = f 0 + f 1 + ... + f (n-1)]. *)
Definition Sum (n : nat) (f : nat -> nat) : nat :=
  fold_right (fun i acc => f i + acc) 0 (seq 0 n).


Section CongestionGame.

  Variable N : nat.                       (* number of players (call sites)    *)
  Variable E : nat.                       (* number of resources (cache lines) *)
  Variable uses : nat -> bool -> nat -> bool.
                                          (* uses i b r : player i, strategy b,*)
                                          (* occupies resource r               *)
  Variable a : nat -> nat.                (* linear cost slope  per resource   *)
  Variable b : nat -> nat.                (* linear cost offset per resource   *)

  (** A pure strategy profile (only coordinates [< N] are ever inspected). *)
  Definition profile := nat -> bool.

  (** Linear resource cost. *)
  Definition rcost (r x : nat) : nat := a r * x + b r.

  (** Load of resource [r]: number of players (< N) occupying it. *)
  Definition load (s : profile) (r : nat) : nat :=
    length (filter (fun i => uses i (s i) r) (seq 0 N)).

  (** Cost experienced by player [i]. *)
  Definition pcost (s : profile) (i : nat) : nat :=
    Sum E (fun r => if uses i (s i) r then rcost r (load s r) else 0).

  (** Social cost = sum of player costs. *)
  Definition SocialCost (s : profile) : nat := Sum N (pcost s).

  (** Rosenthal potential.  [Phi_res r m = rcost r 1 + ... + rcost r m]. *)
  Definition Phi_res (r m : nat) : nat := Sum m (fun k => rcost r (S k)).
  Definition Phi (s : profile) : nat := Sum E (fun r => Phi_res r (load s r)).

  (** Unilateral update: player [i] switches to [bi]. *)
  Definition upd (s : profile) (i : nat) (bi : bool) : profile :=
    fun j => if Nat.eqb j i then bi else s j.

  (** An improving move strictly lowers the mover's own cost. *)
  Definition improving (s : profile) (i : nat) (bi : bool) : Prop :=
    i < N /\ pcost (upd s i bi) i < pcost s i.

  (** One step of iterative best response. *)
  Inductive step : profile -> profile -> Prop :=
  | step_intro : forall s i bi, improving s i bi -> step s (upd s i bi).

  (** Pure Nash equilibrium: no player has an improving deviation. *)
  Definition PNE (s : profile) : Prop :=
    forall i bi, i < N -> pcost s i <= pcost (upd s i bi) i.

  (* ---------------------------------------------------------------- *)
  (** ** GOAL 1 — monotone progress *)
  (* ---------------------------------------------------------------- *)

  Theorem step_decreases_Phi s s' :
    step s s' -> Phi s' < Phi s.
  Proof.
  Admitted.

  (* ---------------------------------------------------------------- *)
  (** ** GOAL 2 — convergence to a pure Nash equilibrium *)
  (* ---------------------------------------------------------------- *)

  Theorem convergence :
    forall s, exists s', clos_refl_trans profile step s s' /\ PNE s'.
  Proof.
  Admitted.

  Corollary exists_PNE : exists s, PNE s.
  Proof.
  Admitted.

  (* ---------------------------------------------------------------- *)
  (** ** GOAL 3 — price of anarchy 5/2 *)
  (* ---------------------------------------------------------------- *)

  Theorem price_of_anarchy s p :
    PNE s -> 2 * SocialCost s <= 5 * SocialCost p.
  Proof.
  Admitted.

End CongestionGame.

(* ================================================================== *)
(** ** Instantiation: a program's call sites are the players.

    The abstract game is parameterized by [N], [E], [uses], [a], [b] —
    exactly the "arbitrary linear cost functions and inline/not-inline
    I-cache line mappings" of the goal.  [collect_callsites p] is the player
    set for program [p]; [N := length (collect_callsites p)].  The three
    theorems above specialize verbatim. *)
(* ================================================================== *)

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
