Set Implicit Arguments.
Require Import ZArith Psatz.
Open Scope Z_scope.
Require Import Znumtheory.
Require Import MyTactics.
Require Import FunInd Recdef.
Require Import List Sorting Permutation.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

Require Import Cooper.

Notation ground := num (only parsing).

Inductive raw_term :=
| RAdd : raw_term -> raw_term -> raw_term
| RSub : raw_term -> raw_term -> raw_term
| RMul : ground -> var -> raw_term
| ROpp : raw_term -> raw_term
| RVar : var -> raw_term
| RConstant : num -> raw_term.

Hint Constructors raw_term.

Inductive raw_predicate_1 :=
| RDv : ground -> raw_predicate_1.

Hint Constructors raw_predicate_1.

Inductive raw_predicate_2 :=
| REq : raw_predicate_2
| RLt : raw_predicate_2
| RLe : raw_predicate_2
| RGt : raw_predicate_2
| RGe : raw_predicate_2.

Hint Constructors raw_predicate_2.

Inductive raw_predicate :=
| RPred1 : raw_predicate_1 -> raw_term -> raw_predicate
| RPred2 : raw_predicate_2 -> raw_term -> raw_term -> raw_predicate.

Hint Constructors raw_predicate.

Inductive raw_formula :=
| RAtom : raw_predicate -> raw_formula
| RFalse : raw_formula
| RTrue : raw_formula
| RAnd : raw_formula -> raw_formula -> raw_formula
| ROr : raw_formula -> raw_formula -> raw_formula
| RNot : raw_formula -> raw_formula
| RExists : raw_formula -> raw_formula.

Hint Constructors raw_formula.

Notation monoms_sign := (list (bool * (ground * var)))%type.
Notation csts_sign := (list (bool * num))%type.
Notation linearized_sign := (monoms_sign * csts_sign)%type.

Definition app2 A B (p1 p2: list A * list B) :=
  let '(l1a, l1b) := p1 in
  let '(l2a, l2b) := p2 in
  (l1a ++ l2a, l1b ++ l2b).

Notation "x ++2 y" := (app2 x y) (at level 50).

Fixpoint linearize_raw_term'
  (t : raw_term)
  (sign : bool)
: linearized_sign
:=
  match t with
  | RAdd t1 t2 =>
    (linearize_raw_term' t1 sign) ++2 (linearize_raw_term' t2 sign)
  | RSub t1 t2 =>
    (linearize_raw_term' t1 sign) ++2 (linearize_raw_term' t2 (negb sign))
  | RMul k v =>
    ([(sign, (k, v))], [])
  | ROpp t =>
    linearize_raw_term' t (negb sign)
  | RVar v =>
    ([(sign, (1, v))], [])
  | RConstant x =>
    ([], [(sign, x)])
  end.

Definition linearize_raw_term (t : raw_term) : linearized_sign :=
  linearize_raw_term' t true.

Definition neg_list A (l : list (bool * A)) :=
  map (fun '(x, y) => (negb x, y)) l.

Definition neg_linearized (t : linearized_sign) : linearized_sign :=
  let '(l, c) := t in
  (neg_list l, neg_list c).

Definition sub_linearized (t1 t2 : linearized_sign) : linearized_sign :=
  let '(l1, c1) := t1 in
  let '(l2, c2) := t2 in
  (l1 ++ neg_list l2, c1 ++ neg_list c2).

Notation monoms := (list (ground * var))%type.
Notation linearized := (monoms * num)%type.

Definition monoms_sign_to_monoms (l : monoms_sign) : monoms :=
  map (fun '(b, (k, v)) => if (b:bool) then (k, v) else (- k, v)) l.

Definition csts_sign_to_csts (c : csts_sign) : num :=
  fold_right (fun '(b, x) acc => if (b:bool) then acc + x else acc - x) 0 c.

Definition linearized_sign_to_linearized '((l, c) : linearized_sign) : linearized :=
  (monoms_sign_to_monoms l, csts_sign_to_csts c).

Definition clear_zeros (l : monoms) : monoms :=
  filter (fun '(k, _) => negb (Z.eqb k 0)) l.

Fixpoint compact_with (m : ground * var) (l : monoms) : monoms :=
  let '(k, v) := m in
  match l with
  | [] =>
    [m]
  | (k', v') :: l' =>
    if Nat.eqb v v' then
      compact_with (k + k', v) l'
    else
      m :: compact_with (k', v') l'
  end.

Definition compact (l : monoms) : monoms :=
  match l with
  | [] =>
    []
  | m :: l' =>
    compact_with m l'
  end.

Require Import Sorting.

Module MonomOrder <: Orders.TotalLeBool.
  Definition t := (num * var)%type.
  Definition leb (x y : t) := Nat.leb (snd x) (snd y).
  Lemma leb_total : forall a b, is_true (leb a b) \/ is_true (leb b a).
  Proof.
    destruct a, b; unfold leb; simpl.
    destruct (n <=? n0)%nat eqn:H1; [now left | right].
    destruct (n0 <=? n)%nat eqn:H2; auto.
    apply Nat.leb_gt in H1.
    apply Nat.leb_gt in H2.
    omega.
  Qed.
End MonomOrder.

Module MonomSort := Sort MonomOrder.

Definition normalize_linearized (t : linearized) : linearized :=
  let '(l, c) := t in
  let l := MonomSort.sort l in
  let l := compact l in
  let l := clear_zeros l in
  (l, c).

Definition linearized_to_term (t : linearized) : term :=
  let '(l, c) := t in
  fold_right (fun '(k, y) acc => TSummand k y acc) (TConstant c) l.

Definition to_term (t : linearized_sign) : term :=
  let t := linearized_sign_to_linearized t in
  let t := normalize_linearized t in
  linearized_to_term t.

Definition plus1 '((l, c) : linearized_sign) : linearized_sign :=
  (l, (true, 1) :: c).

Definition raw_predicate_to_atom (p : raw_predicate) : predicate * term :=
  match p with
  | RPred1 (RDv c) t =>
    let t := linearize_raw_term t in
    if Z.eqb c 0 then
      (Eq, to_term t)
    else
      (Dv c, to_term t)
  | RPred2 p t1 t2 =>
    let t1 := linearize_raw_term t1 in
    let t2 := linearize_raw_term t2 in
    match p with
    | REq => (* t1 = t2 *)
      let t := sub_linearized t2 t1 in (* 0 = t2 - t1 *)
      (Eq, to_term t)
    | RLt => (* t1 < t2 *)
      let t := sub_linearized t2 t1 in (* 0 < t2 - t1 *)
      (Lt, to_term t)
    | RLe => (* t1 <= t2 *)
      let t := plus1 (sub_linearized t2 t1) in (* 0 < t2 - t1 + 1 *)
      (Lt, to_term t)
    | RGt => (* t1 > t2 *)
      let t := sub_linearized t1 t2 in (* 0 < t1 - t2 *)
      (Lt, to_term t)
    | RGe => (* t1 >= t2 *)
      let t := plus1 (sub_linearized t1 t2) in (* 0 < t1 - t2 + 1 *)
      (Lt, to_term t)
    end
  end.

Fixpoint raw_formula_to_formula (f : raw_formula) : formula :=
  match f with
  | RAtom p =>
    let '(p, t) := raw_predicate_to_atom p in
    FAtom p t
  | RFalse =>
    FFalse
  | RTrue =>
    FTrue
  | RAnd f1 f2 =>
    FAnd (raw_formula_to_formula f1) (raw_formula_to_formula f2)
  | ROr f1 f2 =>
    FOr (raw_formula_to_formula f1) (raw_formula_to_formula f2)
  | RNot f =>
    FNot (raw_formula_to_formula f)
  | RExists f =>
    FExists (raw_formula_to_formula f)
  end.

(* ------------------------------------------------------------------------- *)
(* Now prove that all these transformations preserve interpretation of
   terms/predicates/formulas. *)

(* Semantics *)

Fixpoint interpret_raw_term (env : environment) (t : raw_term) : num :=
  match t with
  | RAdd t1 t2 =>
    (interpret_raw_term env t1) + (interpret_raw_term env t2)
  | RSub t1 t2 =>
    (interpret_raw_term env t1) - (interpret_raw_term env t2)
  | RMul k v =>
    k * (env v)
  | ROpp t =>
    - (interpret_raw_term env t)
  | RVar v =>
    env v
  | RConstant c =>
    c
  end.

Fixpoint interpret_raw_predicate_1 (p : raw_predicate_1) (t : num) : Prop :=
  match p with
  | RDv c =>
    (c | t)
  end.

Fixpoint interpret_raw_predicate_2 (p : raw_predicate_2) (t1 t2 : num) : Prop :=
  match p with
  | REq =>
    t1 = t2
  | RLt =>
    t1 < t2
  | RLe =>
    t1 <= t2
  | RGt =>
    t1 > t2
  | RGe =>
    t1 >= t2
  end.

Fixpoint interpret_raw_predicate (env : environment) (p : raw_predicate) : Prop :=
  match p with
  | RPred1 p t =>
    interpret_raw_predicate_1 p (interpret_raw_term env t)
  | RPred2 p t1 t2 =>
    interpret_raw_predicate_2 p (interpret_raw_term env t1) (interpret_raw_term env t2)
  end.

Fixpoint interpret_raw_formula (env : environment) (f : raw_formula) : Prop :=
  match f with
  | RAtom p =>
    interpret_raw_predicate env p
  | RFalse =>
    False
  | RTrue =>
    True
  | RAnd f1 f2 =>
    (interpret_raw_formula env f1) /\ (interpret_raw_formula env f2)
  | ROr f1 f2 =>
    (interpret_raw_formula env f1) \/ (interpret_raw_formula env f2)
  | RNot f' =>
    ~ (interpret_raw_formula env f')
  | RExists f' =>
    exists z, interpret_raw_formula (extend env z) f'
  end.

Definition sign2num (b : bool) : num :=
  if b then 1 else -1.

Definition interpret_monoms_sign (env : environment) (l : monoms_sign) : num :=
  fold_right (fun '(b, (k, v)) acc =>
    acc + (sign2num b) * k * env v
  ) 0 l.

Definition interpret_csts_sign (l : csts_sign) : num :=
  fold_right (fun '(b, x) acc =>
    acc + (sign2num b) * x
  ) 0 l.

Definition interpret_linearized_sign (env : environment) '((l,c) : linearized_sign) : num :=
  interpret_monoms_sign env l + interpret_csts_sign c.

Definition interpret_monoms (env : environment) (l : monoms) : num :=
  fold_right (fun '(k, v) acc =>
    acc + k * env v
  ) 0 l.

Definition interpret_linearized (env : environment) '((l, c) : linearized) : num :=
  interpret_monoms env l + c.

(* ------------------------------------------------------------------------- *)

(* Proofs *)

Create HintDb interp.

Hint Rewrite
     Nat.eqb_eq Nat.eqb_neq
     Bool.negb_false_iff Bool.negb_true_iff
     Z.eqb_eq Z.eqb_neq
: interp.

Ltac interp :=
  simpl; autorewrite with interp in *.

Lemma interpret_monoms_sign_app:
  forall env l1 l2,
  interpret_monoms_sign env (l1 ++ l2) =
  interpret_monoms_sign env l1 + interpret_monoms_sign env l2.
Proof.
  induction l1 as [| [? [? ?]]]; intros; simpl in *; try rewrite IHl1; eauto.
Qed.

Lemma interpret_csts_sign_app:
  forall l1 l2,
  interpret_csts_sign (l1 ++ l2) =
  interpret_csts_sign l1 + interpret_csts_sign l2.
Proof.
  induction l1 as [| [? ?]]; intros; simpl in *; try rewrite IHl1; eauto.
Qed.

Hint Rewrite
     interpret_monoms_sign_app
     interpret_csts_sign_app
: interp.

Lemma interpret_linearized_sign_app2:
  forall env t1 t2,
  interpret_linearized_sign env (t1 ++2 t2) =
  interpret_linearized_sign env t1 + interpret_linearized_sign env t2.
Proof.
  destruct t1 as [l1 c1]. destruct t2 as [l2 c2]. interp. omega.
Qed.

Hint Rewrite interpret_linearized_sign_app2 : interp.

Lemma sign2num_negb:
  forall b,
  sign2num (negb b) = - sign2num b.
Proof. intros. unfold sign2num. repeat case_if; omega. Qed.

Hint Rewrite sign2num_negb : interp.

Lemma interpret_linearize_raw_term':
  forall env t sign,
  interpret_linearized_sign env (linearize_raw_term' t sign) =
  (sign2num sign) * interpret_raw_term env t.
Proof.
  induction t; intros; simpl in *; eauto; interp; try nia.
  - rewrite IHt1, IHt2. nia.
  - rewrite IHt1, IHt2. interp. nia.
  - rewrite IHt. interp. nia.
Qed.

Lemma interpret_linearize_raw_term:
  forall env t,
  interpret_linearized_sign env (linearize_raw_term t) = interpret_raw_term env t.
Proof.
  intros. unfold linearize_raw_term. rewrite interpret_linearize_raw_term'.
  unfold sign2num. eauto.
Qed.

Hint Rewrite interpret_linearize_raw_term : interp.

Lemma interpret_monoms_sign_neg:
  forall env l,
  interpret_monoms_sign env (neg_list l) =
  - interpret_monoms_sign env l.
Proof.
  induction l as [| [? [? ?]]]; intros; simpl in *; eauto.
  rewrite IHl, sign2num_negb. nia.
Qed.

Lemma interpret_csts_sign_neg:
  forall l,
  interpret_csts_sign (neg_list l) =
  - interpret_csts_sign l.
Proof.
  induction l as [| [? ?]]; intros; simpl in *; eauto.
  rewrite IHl, sign2num_negb. nia.
Qed.

Hint Rewrite interpret_monoms_sign_neg interpret_csts_sign_neg : interp.

Lemma interpret_linearized_sign_neg:
  forall env t,
  interpret_linearized_sign env (neg_linearized t) =
  - interpret_linearized_sign env t.
Proof. destruct t. interp. nia. Qed.

Hint Rewrite interpret_linearized_sign_neg : interp.

Lemma interpret_linearized_sign_sub:
  forall env t1 t2,
  interpret_linearized_sign env (sub_linearized t1 t2) =
  interpret_linearized_sign env t1 - interpret_linearized_sign env t2.
Proof. destruct t1, t2. interp. nia. Qed.

Hint Rewrite interpret_linearized_sign_sub : interp.

Arguments Z.mul : simpl nomatch.

Lemma interpret_monoms_sign_to_monoms:
  forall env l,
  interpret_monoms env (monoms_sign_to_monoms l) =
  interpret_monoms_sign env l.
Proof.
  induction l as [| [? [? ?]]]; intros; simpl in *; eauto.
  case_if; rewrite IHl; subst; simpl; nia.
Qed.

Lemma interpret_csts_sign_to_csts:
  forall l,
  csts_sign_to_csts l = interpret_csts_sign l.
Proof.
  induction l as [| [? ?]]; intros; simpl in *; eauto.
  case_if; rewrite IHl; simpl; nia.
Qed.

Hint Rewrite
  interpret_monoms_sign_to_monoms interpret_csts_sign_to_csts : interp.

Lemma interpret_linearized_sign_to_linearized:
  forall env t,
  interpret_linearized env (linearized_sign_to_linearized t) =
  interpret_linearized_sign env t.
Proof. destruct t; interp; auto. Qed.

Hint Rewrite interpret_linearized_sign_to_linearized : interp.

Lemma interpret_clear_zeros:
  forall env l,
  interpret_monoms env (clear_zeros l) = interpret_monoms env l.
Proof.
  induction l as [| [? ?]]; intros; simpl in *; eauto.
  case_if; interp; nia.
Qed.

Hint Rewrite interpret_clear_zeros : interp.

Lemma interpret_compact_with:
  forall env l k v,
  interpret_monoms env (compact_with (k,v) l) =
  k * env v + interpret_monoms env l.
Proof.
  induction l as [| [? ?]]; intros; simpl in *; eauto.
  case_if; simpl; rewrite IHl; interp; subst; nia.
Qed.

Lemma interpret_compact:
  forall env l,
  interpret_monoms env (compact l) = interpret_monoms env l.
Proof.
  intros. unfold compact. destruct l as [|[? ?]]; eauto.
  rewrite interpret_compact_with. simpl. nia.
Qed.

Hint Rewrite interpret_compact : interp.

Lemma interpret_monoms_permutation:
  forall env l1 l2,
  Permutation l1 l2 ->
  interpret_monoms env l1 = interpret_monoms env l2.
Proof.
  introv HP. induction HP;
  repeat match goal with x: (_ * _)%type |- _ => destruct x end;
  simpl; auto.
Qed.

Lemma interpret_normalize_linearized:
  forall env t,
  interpret_linearized env (normalize_linearized t) = interpret_linearized env t.
Proof.
  destruct t as [l c]. unfold normalize_linearized. interp.
  rewrite interpret_monoms_permutation with (l1:=l) (l2:=(MonomSort.sort l));
  auto using MonomSort.Permuted_sort.
Qed.

Hint Rewrite interpret_normalize_linearized : interp.

Lemma interpret_linearized_to_term:
  forall env t,
  interpret_term env (linearized_to_term t) =
  interpret_linearized env t.
Proof.
  destruct t as [l c].
  induction l as [| [? ?]]; intros; simpl in *; eauto.
Qed.

Hint Rewrite interpret_linearized_to_term : interp.

Lemma interpret_to_term:
  forall env t,
  interpret_term env (to_term t) =
  interpret_linearized_sign env t.
Proof. intros. unfold to_term. now interp. Qed.

Hint Rewrite interpret_to_term : interp.

Lemma interpret_plus1:
  forall env t,
  interpret_linearized_sign env (plus1 t) =
  interpret_linearized_sign env t + 1.
Proof. destruct t as [? ?]. simpl. lia. Qed.

Hint Rewrite interpret_plus1 : interp.

Lemma interpret_raw_predicate_to_atom:
  forall env p,
  let '(p', t) := raw_predicate_to_atom p in
  interpret_predicate p' (interpret_term env t) <->
  interpret_raw_predicate env p.
Proof.
  intros env p. destruct p as [p1|p2].
  { destruct p1. simpl. case_if; interp; subst; try reflexivity.
    split; [ intros <- | intros ]. reflexivity. forwards*: Z.divide_0_l. }
  { destruct p2; interp; lia. }
Qed.

Lemma interpret_raw_formula_to_formula:
  forall f env,
  interpret_formula env (raw_formula_to_formula f) <->
  interpret_raw_formula env f.
Proof.
  induction f; intros; interp; [
    repeat match goal with h: forall _:environment, _ |- _ =>
      specialize (h env) end
  .. |];
  try tauto.
  - match goal with r:raw_predicate |- _ =>
      forwards: interpret_raw_predicate_to_atom env r end.
    destruct (raw_predicate_to_atom r). eauto.
  - apply exists_equivalence. eauto.
Qed.

Hint Rewrite interpret_raw_formula_to_formula : interp.
