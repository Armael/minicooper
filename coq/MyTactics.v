Require Export Coq.Program.Equality.
Require Export TLC.LibTactics.
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

(* Dealing with integer comparisons. *)

Ltac inspect_cases :=
  match goal with
  | |- context [le_gt_dec ?n ?n'] =>
      case (le_gt_dec n n')
  | h: context [le_gt_dec ?n ?n'] |- _ =>
      generalize h; clear h; case (le_gt_dec n n'); intro h
  | |- context [eq_nat_dec ?n ?n'] =>
      case (eq_nat_dec n n')
  | h: context [eq_nat_dec ?n ?n'] |- _ =>
      generalize h; clear h; case (eq_nat_dec n n'); intro h
  | |- context [(lt_eq_lt_dec ?n ?n')] =>
       let s := fresh in
       case (lt_eq_lt_dec n n'); [ intro s; case s; clear s | idtac ]
  end.

Ltac by_cases :=
  repeat inspect_cases; try solve [ intros; false; omega ]; intros.

Ltac easy :=
  try omega;
  try ( f_equal; omega );
  try solve [ auto ].

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

(* Destructuring triples of propositions. *)

Set Implicit Arguments.

Lemma pi1:
  forall A B C, A /\ B /\ C -> A.
Proof.
  intuition.
Qed.

Lemma pi2:
  forall A B C, A /\ B /\ C -> B.
Proof.
  intuition.
Qed.

Lemma pi3:
  forall A B C, A /\ B /\ C -> C.
Proof.
  intuition.
Qed.

(* A convenient function. *)

Definition transpose A B (f : A -> A -> B) x y := f y x.

(* Turn some tactics into hints. *)

Hint Extern 1 => f_equal : f_equal.

Hint Extern 1 => congruence : congruence.

(* Support for marking the induction hypothesis. The mark [mark_ih] must be
   used in the statement, after the hypothesis that serves for the induction.
   The tactic [intros_ih] introduces the hypotheses, while unfolding the mark
   in the goal, so it does not block the hypotheses that follow it. The tactic
   [use_ih] applies and clears a hypothesis that bears the mark. *)

Definition mark_ih (P : Prop) := P.

Ltac intros_ih :=
  intros; unfold mark_ih; intros.

Ltac use_ih :=
  match goal with ih: mark_ih _ |- _ => unfold mark_ih in ih; eapply ih; clear ih end.

Ltac clear_ih :=
  repeat match goal with ih: mark_ih _ |- _ => clear ih end.
