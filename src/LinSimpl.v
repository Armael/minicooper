Set Implicit Arguments.
Require Import ZArith Psatz.
Require Import Znumtheory.
Require Import List Sorting Permutation.
Require Import MiniCooper.MyTactics.
Import ListNotations.
Open Scope list_scope.
Open Scope Z_scope.

(* Normalization procedure on linear combinations. *)

Module Type LinVar.
  Parameter t : Type.
  Parameter eqdec : forall (v1 v2 : t), { v1 = v2 } + { v1 <> v2 }.
  Parameter leb : t -> t -> bool.
  Parameter leb_total : forall a b, is_true (leb a b) \/ is_true (leb b a).
End LinVar.

Module NatVar <: LinVar.
  Definition t := nat.
  Definition eqdec := Nat.eq_dec.
  Definition leb := Nat.leb.
  Lemma leb_total : forall a b, is_true (Nat.leb a b) \/ is_true (Nat.leb b a).
  Proof.
    intros. unfold is_true. rewrite !Nat.leb_le. lia.
  Qed.
End NatVar.


Module LinSimpl (Var : LinVar).

(* A monom is a variable multiplied by a constant coefficient *)
Notation monom := (Var.t * Z)%type.

(* A linear combination is a list of monoms, and should be interpreted as their
   sum. *)
Definition lin := list monom.

Definition interpret_lin (var : Var.t -> Z) (l : lin) : Z :=
  fold_right (fun '(v, k) acc =>
    acc + k * var v
  ) 0 l.

(* ------------------------------------------------------------------------- *)

Definition add (l1 l2 : lin) :=
  l1 ++ l2.

Lemma interpret_add:
  forall var l1 l2,
  interpret_lin var (add l1 l2) =
  interpret_lin var l1 + interpret_lin var l2.
Proof.
  induction l1 as [|[? ?]]; intros; simpl in *; rewrite ?IHl1; eauto.
Qed.

Definition mul (k : Z) (l : lin) :=
  map (fun '(v, k') => (v, k * k')) l.

Lemma interpret_mul:
  forall var k l,
  interpret_lin var (mul k l) = k * interpret_lin var l.
Proof.
  induction l as [|[? ?]]; intros; simpl in *; rewrite ?IHl; lia.
Qed.

Definition sub (l1 l2 : lin) :=
  add l1 (mul (-1) l2).

Lemma interpret_sub:
  forall var l1 l2,
  interpret_lin var (sub l1 l2) =
  interpret_lin var l1 -
  interpret_lin var l2.
Proof.
  intros; unfold sub; rewrite interpret_add, interpret_mul; lia.
Qed.

(* ------------------------------------------------------------------------- *)

Definition clear_zeros (l : lin) : lin :=
  filter (fun '(v, k) => negb (Z.eqb k 0)) l.

(* Compaction: merges coefficients of monoms with the same variable.
   This assumes [l] to be sorted. *)
Fixpoint compact_with (m : monom) (l : lin) : lin :=
  let '(v, k) := m in
  match l with
  | [] =>
    [m]
  | (v', k') :: l' =>
    if Var.eqdec v v' then
      compact_with (v, k + k') l'
    else
      m :: compact_with (v', k') l'
  end.

Definition compact (l : lin) : lin :=
  match l with
  | [] =>
    []
  | m :: l' =>
    compact_with m l'
  end.

Module MonomOrder <: Orders.TotalLeBool.
  Definition t := monom.
  Definition leb (x y : t) := Var.leb (fst x) (fst y).
  Lemma leb_total : forall a b, is_true (leb a b) \/ is_true (leb b a).
  Proof.
    destruct a, b; unfold leb; simpl.
    destruct (Var.leb_total t0 t1); eauto.
  Qed.
End MonomOrder.

Module MonomSort := Sort MonomOrder.

Definition simpl (l : lin) : lin :=
  let l := MonomSort.sort l in
  let l := compact l in
  clear_zeros l.

(* ------------------------------------------------------------------------- *)

Local Ltac rew :=
  rewrite
     ?Nat.eqb_eq, ?Nat.eqb_neq,
     ?Bool.negb_false_iff, ?Bool.negb_true_iff,
     ?Z.eqb_eq, ?Z.eqb_neq
  in *.

Lemma interpret_clear_zeros:
  forall var l,
  interpret_lin var (clear_zeros l) = interpret_lin var l.
Proof.
  induction l as [| [? ?]]; intros; simpl in *; eauto.
  case_if; simpl; rew; subst; lia.
Qed.

Lemma interpret_compact_with:
  forall var l k v,
  interpret_lin var (compact_with (v,k) l) =
  k * var v + interpret_lin var l.
Proof.
  induction l as [| [? ?]]; intros; simpl in *; eauto.
  case_if; simpl; rewrite IHl; rew; subst; nia.
Qed.

Lemma interpret_compact:
  forall var l,
  interpret_lin var (compact l) = interpret_lin var l.
Proof.
  intros. unfold compact. destruct l as [|[? ?]]; eauto.
  rewrite interpret_compact_with. simpl. nia.
Qed.

Lemma interpret_lin_permutation:
  forall var l1 l2,
  Permutation l1 l2 ->
  interpret_lin var l1 = interpret_lin var l2.
Proof.
  introv HP. induction HP;
  repeat match goal with x: (_ * _)%type |- _ => destruct x end;
  simpl; auto.
Qed.

Lemma interpret_simpl:
  forall var l,
  interpret_lin var (simpl l) =
  interpret_lin var l.
Proof.
  intros. unfold simpl.
  rewrite interpret_clear_zeros, interpret_compact.
  rewrite interpret_lin_permutation with (l1:=l) (l2:=(MonomSort.sort l));
  auto using MonomSort.Permuted_sort.
Qed.

End LinSimpl.