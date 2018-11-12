Require Export Coq.Program.Equality.
Require Export Omega.

(* Hints for invoking omega on arithmetic subgoals. *)

Hint Extern 1 (_ = _ :> nat) => omega.
Hint Extern 1 (_ <> _ :> nat) => omega.
Hint Extern 1 (_ = _ :> Z) => omega.
Hint Extern 1 (_ <> _ :> Z) => omega.
Hint Extern 1 (_ < _) => omega.
Hint Extern 1 (_ > _) => omega.
Hint Extern 1 (_ <= _) => omega.
Hint Extern 1 (_ >= _) => omega.

(* Dealing with if *)

Ltac case_if :=
  let H := fresh in
  match goal with
  | |- context [if ?b then _ else _] =>
    destruct b eqn:H
  | h: context [if ?b then _ else _] |- _ =>
    destruct b eqn:H
  end.

(* Hypothesis handling *)

Ltac applyin H :=
  match goal with h: _ |- _ => apply H in h end.

Ltac spec1 H :=
  lazymatch type of H with
  | ?A -> ?B =>
    let a := fresh in
    assert (a : A); [ eauto | specialize (H a); clear a ]
  | forall x : ?A, _ =>
    let a := fresh in
    evar (a : A);
    specialize (H a); subst a
  end.

Ltac spec H :=
  repeat (spec1 H; []).

(* This tactic unpacks all existentially quantified hypotheses and splits all
   conjunctive hypotheses. *)

Ltac unpack1 :=
  match goal with
  | h: ex _ |- _ => destruct h
  | h: (_ /\ _) |- _ => destruct h
  | h: exists2 x, _ & _ |- _ => destruct h
  end.

Tactic Notation "unpack" :=
  repeat progress unpack1.

Goal
  forall (P Q : nat -> Prop),
  (exists n, P n /\ Q n) ->
  (exists n, Q n /\ P n).
Proof.
  intros. unpack. eauto.
Qed.

(* This variant is analogous, but attacks only one hypothesis, whose name is
   specified. *)

Ltac named_unpack h :=
  generalize h; clear h;
  match goal with
  | |- ex _ -> _ => intros [ ? h ]; named_unpack h
  | |- (_ /\ _) -> _ => intros [ ? h ]; named_unpack h
  | |- _ -> _ => intro h
  end.

Tactic Notation "unpack" hyp(h) := named_unpack h.

Goal
  forall (P Q : nat -> Prop),
  (exists n, P n /\ Q n) ->
  (exists n, Q n /\ P n).
Proof.
  intros ? ? h. unpack h. eauto.
Qed.

(* This variant is analogous, but attacks a term. *)

Ltac term_unpack t :=
  let h := fresh in
  generalize t; intro h; named_unpack h.

Tactic Notation "unpack" constr(t) := term_unpack t.

Goal
  forall (P Q : nat -> Prop) (x : nat),
  x = 0 ->
  (x = 0 -> exists n, P n /\ Q n) ->
  (exists n, Q n /\ P n).
Proof.
  intros ? ? ? z h. unpack (h z). unpack h. eauto.
Qed.

(* Turn some tactics into hints. *)

Hint Extern 1 => f_equal : f_equal.

Hint Extern 1 => congruence : congruence.
