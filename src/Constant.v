Set Implicit Arguments.
Require Import ZArith Psatz.
Require Import Znumtheory.
Require Import Classical.
Require Import FunInd Recdef.
Require Import List.
Import ListNotations.
Require Import MiniCooper.MyTactics.
Require Import MiniCooper.LinSimpl.
Open Scope list_scope.
Open Scope Z_scope.

(* ------------------------------------------------------------------------- *)
(* Constants can be a combination of numeric literals and arbitrary expressions
   (those are treated as abstract and kept in an environment). *)

Notation var := nat.

Notation environment := (var -> Z).

Inductive constant :=
| CAdd: constant -> constant -> constant
| CMul: Z -> constant -> constant
| CGround: Z -> constant
| CAbstract: var -> constant.

Fixpoint interpret_constant (cenv : environment) (c : constant) : Z :=
  match c with
  | CAdd c1 c2 =>
    (interpret_constant cenv c1) + (interpret_constant cenv c2)
  | CMul k c =>
    k * (interpret_constant cenv c)
  | CGround k =>
    k
  | CAbstract v =>
    cenv v
  end.

(* Smart constructors for CAdd and CMul *)

Function cadd (c1 c2 : constant) : constant :=
  match (c1, c2) with
  | (CGround k1, CGround k2) =>
    CGround (k1 + k2)
  | (CGround 0, _) =>
    c2
  | (_, CGround 0) =>
    c1
  | (_, _) =>
    CAdd c1 c2
  end.

Lemma interpret_cadd:
  forall cenv c1 c2,
  interpret_constant cenv (cadd c1 c2) =
  interpret_constant cenv c1 + interpret_constant cenv c2.
Proof.
  intros. functional induction (cadd c1 c2); simpl in *; eauto.
Qed.

Function cmul (k : Z) (c : constant) : constant :=
  match c with
  | CGround k' =>
    CGround (k * k')
  | _ =>
    match k with
    | 1 => c
    | _ => CMul k c
    end
  end.

Lemma interpret_cmul:
  forall cenv k c,
  interpret_constant cenv (cmul k c) =
  k * interpret_constant cenv c.
Proof.
  intros. functional induction (cmul k c); cbn -[Z.mul] in *; eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* Simplification procedure for constants. *)

Module LinCst := LinSimpl (NatVar).

Definition interp_var (cenv : environment) (v : var) :=
  (* Use variable index [0] for the ground term *)
  match v with
  | O => 1
  | S n => cenv n
  end.

(* Conversion from [constant] to [LinCst.t] *)

Fixpoint linearize_constant (c : constant) : LinCst.lin :=
  match c with
  | CAdd c1 c2 =>
    LinCst.add (linearize_constant c1) (linearize_constant c2)
  | CMul k c =>
    LinCst.mul k (linearize_constant c)
  | CGround k =>
    [(O, k)]
  | CAbstract n =>
    [(S n, 1)]
  end.

(* Conversion from [LinCst.t] to [constant] *)

Definition linearized_to_constant (l : LinCst.lin) : constant :=
  fold_right (fun '(v, k) acc =>
    cadd acc
      match v with
      | O => CGround k
      | S n => cmul k (CAbstract n)
      end
  ) (CGround 0) l.

(* The simplification procedure *)

Definition simpl_constant (c : constant) : constant :=
  let l := linearize_constant c in
  let l := LinCst.simpl l in
  linearized_to_constant l.

(* ------------------------------------------------------------------------- *)

Lemma interpret_linearize_constant:
  forall cenv c,
  LinCst.interpret_lin (interp_var cenv) (linearize_constant c) =
  interpret_constant cenv c.
Proof.
  induction c; simpl in *; eauto.
  - rewrite LinCst.interpret_add. eauto.
  - rewrite LinCst.interpret_mul, IHc. eauto.
  - now destruct (cenv n).
Qed.

Local Arguments cmul : simpl never.

Lemma interpret_linearized_to_constant:
  forall cenv l,
  interpret_constant cenv (linearized_to_constant l) =
  LinCst.interpret_lin (interp_var cenv) l.
Proof.
  induction l as [|[? ?]]; eauto.
  simpl. rewrite interpret_cadd, IHl.
  destruct t; simpl.
  - eauto with zarith.
  - rewrite interpret_cmul. eauto with zarith.
Qed.

Lemma interpret_simpl_constant:
  forall cenv c,
  interpret_constant cenv (simpl_constant c) =
  interpret_constant cenv c.
Proof.
  intros; unfold simpl_constant.
  now rewrite interpret_linearized_to_constant,
              LinCst.interpret_simpl,
              interpret_linearize_constant.
Qed.