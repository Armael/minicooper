Set Implicit Arguments.
Require Import ZArith Psatz.
Open Scope Z_scope.
Require Import Znumtheory.
Require Import List Sorting Permutation.
Import ListNotations.
Open Scope list_scope.

Require Import MiniCooper.MyTactics.
Require Import MiniCooper.Theory.

(* ------------------------------------------------------------------------- *)
(* The surface syntax that the tactic recognizes.

   The goal is to the least amount of work possible in Ltac, so the syntax is
   directly reified to the surface syntax defined here, and
   preprocessing/normalization is written as Coq functions. *)

Notation ground := num (only parsing).

Inductive raw_term :=
| RAdd : raw_term -> raw_term -> raw_term
| RSub : raw_term -> raw_term -> raw_term
| RMul : ground -> var -> raw_term
| ROpp : raw_term -> raw_term
| RVar : var -> raw_term
| RConstant : constant -> raw_term.

Inductive raw_predicate_1 :=
| RDv : ground -> raw_predicate_1.

Inductive raw_predicate_2 :=
| REq : raw_predicate_2
| RLt : raw_predicate_2
| RLe : raw_predicate_2
| RGt : raw_predicate_2
| RGe : raw_predicate_2.

Inductive raw_predicate :=
| RPred1 : raw_predicate_1 -> raw_term -> raw_predicate
| RPred2 : raw_predicate_2 -> raw_term -> raw_term -> raw_predicate.

Inductive raw_formula :=
| RAtom : raw_predicate -> raw_formula
| RFalse : raw_formula
| RTrue : raw_formula
| RAnd : raw_formula -> raw_formula -> raw_formula
| ROr : raw_formula -> raw_formula -> raw_formula
| RNot : raw_formula -> raw_formula
| RExists : raw_formula -> raw_formula.

Hint Constructors
     raw_term
     raw_predicate_1 raw_predicate_2 raw_predicate
     raw_formula.

(* ------------------------------------------------------------------------- *)
(* Semantics of the surface syntax. *)

Fixpoint interpret_raw_term (cenv env : environment) (t : raw_term) : num :=
  match t with
  | RAdd t1 t2 =>
    (interpret_raw_term cenv env t1) + (interpret_raw_term cenv env t2)
  | RSub t1 t2 =>
    (interpret_raw_term cenv env t1) - (interpret_raw_term cenv env t2)
  | RMul k v =>
    k * (env v)
  | ROpp t =>
    - (interpret_raw_term cenv env t)
  | RVar v =>
    env v
  | RConstant c =>
    interpret_constant cenv c
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

Fixpoint interpret_raw_predicate (cenv env : environment) (p : raw_predicate)
: Prop :=
  match p with
  | RPred1 p t =>
    interpret_raw_predicate_1 p (interpret_raw_term cenv env t)
  | RPred2 p t1 t2 =>
    interpret_raw_predicate_2 p
      (interpret_raw_term cenv env t1) (interpret_raw_term cenv env t2)
  end.

Fixpoint interpret_raw_formula (cenv env : environment) (f : raw_formula)
: Prop :=
  match f with
  | RAtom p =>
    interpret_raw_predicate cenv env p
  | RFalse =>
    False
  | RTrue =>
    True
  | RAnd f1 f2 =>
    (interpret_raw_formula cenv env f1) /\ (interpret_raw_formula cenv env f2)
  | ROr f1 f2 =>
    (interpret_raw_formula cenv env f1) \/ (interpret_raw_formula cenv env f2)
  | RNot f' =>
    ~ (interpret_raw_formula cenv env f')
  | RExists f' =>
    exists z, interpret_raw_formula cenv (extend env z) f'
  end.

(* ------------------------------------------------------------------------- *)
(* Intermediate representation for terms. *)

Notation monoms := (list (ground * var))%type.
Notation linearized := (monoms * constant)%type.

(* Its semantics *)

Definition interpret_monoms (env : environment) (l : monoms) : num :=
  fold_right (fun '(k, v) acc =>
    acc + k * env v
  ) 0 l.

Definition interpret_linearized (cenv env : environment) '((l, c) : linearized)
: num :=
  interpret_monoms env l + interpret_constant cenv c.

(* ------------------------------------------------------------------------- *)
(* Conversion from a [raw_term] to a [linearized]. *)

Definition add_lin (l1 l2 : linearized) :=
  let '(m1, c1) := l1 in
  let '(m2, c2) := l2 in
  (m1 ++ m2, cadd c1 c2).

Definition neg_lin '((m, c) : linearized) :=
  (map (fun '(k, v) => (-k, v)) m, cneg c).

Definition sub_lin (l1 l2 : linearized) :=
  add_lin l1 (neg_lin l2).

Fixpoint linearize_raw_term (t : raw_term) : linearized :=
  match t with
  | RAdd t1 t2 =>
    add_lin (linearize_raw_term t1) (linearize_raw_term t2)
  | RSub t1 t2 =>
    sub_lin (linearize_raw_term t1) (linearize_raw_term t2)
  | RMul k v =>
    ([(k, v)], CGround 0)
  | ROpp t =>
    neg_lin (linearize_raw_term t)
  | RVar v =>
    ([(1, v)], CGround 0)
  | RConstant x =>
    ([], x)
  end.

(* ------------------------------------------------------------------------- *)
(* Normalization procedure on [linearized] (the goal is to produce terms that
   are well-formed according to [wft]). *)

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

(* ------------------------------------------------------------------------- *)
(* Conversion to the internal syntax of formulas, defined in MiniCooper.Theory.
*)

Definition linearized_to_term (t : linearized) : term :=
  let '(l, c) := t in
  fold_right (fun '(k, y) acc => TSummand k y acc) (TConstant c) l.

Definition to_term (t : linearized) : term :=
  let t := normalize_linearized t in
  linearized_to_term t.

Definition plus1 '((m, c) : linearized) : linearized :=
  (m, cadd c (CGround 1)).

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
      let t := sub_lin t2 t1 in (* 0 = t2 - t1 *)
      (Eq, to_term t)
    | RLt => (* t1 < t2 *)
      let t := sub_lin t2 t1 in (* 0 < t2 - t1 *)
      (Lt, to_term t)
    | RLe => (* t1 <= t2 *)
      let t := plus1 (sub_lin t2 t1) in (* 0 < t2 - t1 + 1 *)
      (Lt, to_term t)
    | RGt => (* t1 > t2 *)
      let t := sub_lin t1 t2 in (* 0 < t1 - t2 *)
      (Lt, to_term t)
    | RGe => (* t1 >= t2 *)
      let t := plus1 (sub_lin t1 t2) in (* 0 < t1 - t2 + 1 *)
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

Create HintDb interp.

Hint Rewrite
     Nat.eqb_eq Nat.eqb_neq
     Bool.negb_false_iff Bool.negb_true_iff
     Z.eqb_eq Z.eqb_neq
     interpret_cadd interpret_cmul interpret_cneg
: interp.

Ltac interp :=
  simpl; autorewrite with interp in *.

Lemma interpret_add_lin:
  forall cenv env l1 l2,
  interpret_linearized cenv env (add_lin l1 l2) =
  interpret_linearized cenv env l1 + interpret_linearized cenv env l2.
Proof.
  destruct l1 as [m1 c1]. destruct l2 as [m2 c2].
  induction m1 as [| [? ?]]; intros; simpl in *; interp; eauto.
Qed.

Lemma interpret_neg_lin:
  forall cenv env l,
  interpret_linearized cenv env (neg_lin l) =
  - interpret_linearized cenv env l.
Proof.
  destruct l as [m c].
  induction m as [| [? ?]]; intros; simpl in *; interp; eauto. nia.
Qed.

Lemma interpret_sub_lin:
  forall cenv env l1 l2,
  interpret_linearized cenv env (sub_lin l1 l2) =
  interpret_linearized cenv env l1 - interpret_linearized cenv env l2.
Proof.
  intros; unfold sub_lin; interp. rewrite interpret_add_lin, interpret_neg_lin.
  omega.
Qed.

Hint Rewrite interpret_add_lin interpret_neg_lin interpret_sub_lin : interp.

Local Arguments Z.mul : simpl nomatch.

Lemma interpret_linearize_raw_term:
  forall cenv env t,
  interpret_linearized cenv env (linearize_raw_term t) =
  interpret_raw_term cenv env t.
Proof.
  induction t; intros; simpl in *; eauto; interp; try nia.
Qed.

Hint Rewrite interpret_linearize_raw_term : interp.

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
  forall cenv env t,
  interpret_linearized cenv env (normalize_linearized t) =
  interpret_linearized cenv env t.
Proof.
  destruct t as [l c]. unfold normalize_linearized. interp.
  rewrite interpret_monoms_permutation with (l1:=l) (l2:=(MonomSort.sort l));
  auto using MonomSort.Permuted_sort.
Qed.

Hint Rewrite interpret_normalize_linearized : interp.

Lemma interpret_linearized_to_term:
  forall cenv env t,
  interpret_term cenv env (linearized_to_term t) =
  interpret_linearized cenv env t.
Proof.
  destruct t as [l c].
  induction l as [| [? ?]]; intros; simpl in *; eauto.
Qed.

Hint Rewrite interpret_linearized_to_term : interp.

Lemma interpret_to_term:
  forall cenv env t,
  interpret_term cenv env (to_term t) =
  interpret_linearized cenv env t.
Proof. intros. unfold to_term. now interp. Qed.

Hint Rewrite interpret_to_term : interp.

Lemma interpret_plus1:
  forall cenv env t,
  interpret_linearized cenv env (plus1 t) =
  interpret_linearized cenv env t + 1.
Proof. destruct t as [? ?]. interp. simpl. lia. Qed.

Hint Rewrite interpret_plus1 : interp.

Lemma interpret_raw_predicate_to_atom:
  forall cenv env p,
  let '(p', t) := raw_predicate_to_atom p in
  interpret_predicate p' (interpret_term cenv env t) <->
  interpret_raw_predicate cenv env p.
Proof.
  intros cenv env p. destruct p as [p1|p2].
  { destruct p1. simpl. case_if; interp; subst; try reflexivity.
    split; [ intros <- | intros ]. reflexivity. forwards*: Z.divide_0_l. }
  { destruct p2; interp; lia. }
Qed.

Lemma interpret_raw_formula_to_formula:
  forall cenv f env,
  interpret_formula cenv env (raw_formula_to_formula f) <->
  interpret_raw_formula cenv env f.
Proof.
  induction f; intros; interp; [
    repeat match goal with h: forall _:environment, _ |- _ =>
      specialize (h env) end
  .. |];
  try tauto.
  - match goal with r:raw_predicate |- _ =>
      forwards: interpret_raw_predicate_to_atom cenv env r end.
    destruct (raw_predicate_to_atom r). eauto.
  - apply exists_equivalence. eauto.
Qed.

Hint Rewrite interpret_raw_formula_to_formula : interp.

(* ------------------------------------------------------------------------- *)
(* At the moment, we do not prove that the resulting formulas are well-formed.
   Instead we write a checker. *)

Fixpoint check_wft (n : nat) (t : term) : bool :=
  match t with
  | TSummand k n' u =>
    negb (Z.eqb k 0) &&
    Nat.leb n n' &&
    check_wft (S n') u
  | TConstant _ =>
    true
  end.

Definition check_wfp (p : predicate) : bool :=
  match p with
  | Dv c =>
    Z.ltb 0 c
  | _ =>
    true
  end.

Fixpoint check_wff (f : formula) : bool :=
  match f with
  | FAtom p t =>
    check_wft 0 t && check_wfp p
  | FFalse | FTrue =>
    true
  | FAnd f1 f2 | FOr f1 f2 =>
    check_wff f1 && check_wff f2
  | FNot f | FExists f=>
    check_wff f
  end.

Lemma check_wft_correct:
  forall t n,
  check_wft n t = true ->
  wft n t.
Proof.
  induction t; intros; simpl in *; eauto.
  rewrite !Bool.andb_true_iff in *. unpack.
  rewrite Bool.negb_true_iff, Z.eqb_neq, Nat.leb_le in *. eauto.
Qed.

Lemma check_wfp_correct:
  forall p,
  check_wfp p = true ->
  wfp p.
Proof.
  destruct p; simpl in *; intros; try rewrite Z.ltb_lt in *; eauto.
Qed.

Lemma check_wff_correct:
  forall f,
  check_wff f = true ->
  wff_ue f.
Proof.
  induction f; intros; simpl in *;
    try rewrite Bool.andb_true_iff in *; unpack;
      eauto using check_wft_correct, check_wfp_correct.
Qed.

(* ------------------------------------------------------------------------- *)

(* The main theorem used by the tactic *)

Definition empty_env : environment := (fun (n:nat) => 0).

Lemma cooper_qe_theorem (cenv : environment) (f : raw_formula) :
  let f' := raw_formula_to_formula f in
  check_wff f' = true ->
  forall qef',
  qe f' = qef' ->
  interpret_formula cenv empty_env qef' ->
  interpret_raw_formula cenv empty_env f.
Proof.
  simpl; intros. subst qef'. rewrite interpret_qe in *; interp; auto.
  apply~ check_wff_correct.
Qed.

(* ------------------------------------------------------------------------- *)
(* We use template-coq for the reification part. *)

Require Import Template.All.

Fixpoint nthZ (n : nat) (l : list num) : num :=
  match l with
  | [] => 0
  | x :: xs =>
    match n with
    | O => x
    | S n' => nthZ n' xs
    end
  end.

Ltac is_ground_positive term :=
  lazymatch term with
  | tConstruct {| inductive_mind := "Coq.Numbers.BinNums.positive";
                  inductive_ind := _ |} _ [] =>
    idtac
  | tApp ?x [?y] =>
    is_ground_positive x;
    is_ground_positive y
  end.

Ltac is_ground_Z term :=
  lazymatch term with
  | tConstruct {| inductive_mind := "Coq.Numbers.BinNums.Z";
                  inductive_ind := _ |} _ [] =>
    idtac
  | tApp ?x [?pos] =>
    is_ground_Z x;
    is_ground_positive pos
  end.

Ltac reflect_term term csts cid cont :=
  lazymatch term with
  | tApp (tConst "Coq.ZArith.BinIntDef.Z.add" []) [?x; ?y] =>
    reflect_term x csts cid ltac:(fun t1 csts cid =>
    reflect_term y csts cid ltac:(fun t2 csts cid =>
    cont (RAdd t1 t2) csts cid))
  | tApp (tConst "Coq.ZArith.BinIntDef.Z.sub" []) [?x; ?y] =>
    reflect_term x csts cid ltac:(fun t1 csts cid =>
    reflect_term y csts cid ltac:(fun t2 csts cid =>
    cont (RSub t1 t2) csts cid))
  | tApp (tConst "Coq.ZArith.BinIntDef.Z.mul" []) [?x; tRel ?v] =>
    tryif is_ground_Z x then (
      denote_term x ltac:(fun k =>
      cont (RMul k v) csts cid)
    ) else fail 100 "Multiplicative constants must be concrete terms"
  | tApp (tConst "Coq.ZArith.BinIntDef.Z.mul" []) [tRel ?v; ?x] =>
    tryif is_ground_Z x then (
      denote_term x ltac:(fun k =>
      cont (RMul k v) csts cid)
    ) else fail 100 "Multiplicative constants must be concrete terms"
  | tApp (tConst "Coq.ZArith.BinIntDef.Z.opp" []) [?x] =>
    reflect_term x csts cid ltac:(fun t csts cid =>
    cont (ROpp t) csts cid)
  | tRel ?n =>
    cont (RVar n) csts cid
  | ?x =>
    denote_term x ltac:(fun k =>
      tryif is_ground_Z x then
        cont (RConstant (CGround k)) csts cid
      else
        cont (RConstant (CAbstract cid)) (k::csts) (S cid)
    )
  end.

Ltac reflect_predicate term csts cid cont :=
  lazymatch term with
  | tApp (tInd {| inductive_mind := "Coq.Init.Logic.eq"; inductive_ind := 0 |} [])
      [tInd {| inductive_mind := "Coq.Numbers.BinNums.Z"; inductive_ind := 0 |} [];
       ?x; ?y] =>
    reflect_term x csts cid ltac:(fun t1 csts cid =>
    reflect_term y csts cid ltac:(fun t2 csts cid =>
    cont (RPred2 REq t1 t2) csts cid))
  | tApp (tConst "Coq.ZArith.BinInt.Z.lt" []) [?x; ?y] =>
    reflect_term x csts cid ltac:(fun t1 csts cid =>
    reflect_term y csts cid ltac:(fun t2 csts cid =>
    cont (RPred2 RLt t1 t2) csts cid))
  | tApp (tConst "Coq.ZArith.BinInt.Z.le" []) [?x; ?y] =>
    reflect_term x csts cid ltac:(fun t1 csts cid =>
    reflect_term y csts cid ltac:(fun t2 csts cid =>
    cont (RPred2 RLe t1 t2) csts cid))
  | tApp (tConst "Coq.ZArith.BinInt.Z.gt" []) [?x; ?y] =>
    reflect_term x csts cid ltac:(fun t1 csts cid =>
    reflect_term y csts cid ltac:(fun t2 csts cid =>
    cont (RPred2 RGt t1 t2) csts cid))
  | tApp (tConst "Coq.ZArith.BinInt.Z.ge" []) [?x; ?y] =>
    reflect_term x csts cid ltac:(fun t1 csts cid =>
    reflect_term y csts cid ltac:(fun t2 csts cid =>
    cont (RPred2 RGe t1 t2) csts cid))
  | tApp (tConst "Coq.ZArith.BinInt.Z.divide" []) [?x; ?y] =>
    tryif is_ground_Z x then (
      denote_term x ltac:(fun c =>
      reflect_term y csts cid ltac:(fun t csts cid =>
      cont (RPred1 (RDv c) t) csts cid))
    ) else fail 100 "Divisibility can only be by concrete constants"
  end.

Ltac reflect_formula term csts cid cont :=
  lazymatch term with
  | tInd {| inductive_mind := "Coq.Init.Logic.False"; inductive_ind := 0 |} [] =>
    cont RFalse csts cid
  | tInd {| inductive_mind := "Coq.Init.Logic.True"; inductive_ind := 0 |} [] =>
    cont RTrue csts cid
  | tApp (tInd {| inductive_mind := "Coq.Init.Logic.and"; inductive_ind := 0 |} [])
         [?P; ?Q] =>
    reflect_formula P csts cid ltac:(fun f1 csts cid =>
    reflect_formula Q csts cid ltac:(fun f2 csts cid =>
    cont (RAnd f1 f2) csts cid))
  | tApp (tInd {| inductive_mind := "Coq.Init.Logic.or"; inductive_ind := 0 |} [])
         [?P; ?Q] =>
    reflect_formula P csts cid ltac:(fun f1 csts cid =>
    reflect_formula Q csts cid ltac:(fun f2 csts cid =>
    cont (ROr f1 f2) csts cid))
  | tApp (tConst "Coq.Init.Logic.not" []) [?P] =>
    reflect_formula P csts cid ltac:(fun f csts cid =>
    cont (RNot f) csts cid)
  | tApp (tInd {| inductive_mind := "Coq.Init.Logic.ex"; inductive_ind := 0 |} [])
         [tInd {| inductive_mind := "Coq.Numbers.BinNums.Z"; inductive_ind := 0 |} [];
          tLambda _ _ ?body] =>
    reflect_formula body csts cid ltac:(fun f csts cid =>
    cont (RExists f) csts cid)
  | ?f =>
    reflect_predicate f csts cid ltac:(fun p csts cid =>
    cont (RAtom p) csts cid)
  end.

Fixpoint myrev (l l' : list num) : list num :=
  match l with
  | [] => l'
  | x :: xs => myrev xs (x :: l')
  end.

Ltac mkcenv csts :=
  let csts := eval cbv [myrev] in (myrev csts []) in
  constr:(fun n => nthZ n csts).

Ltac qe :=
  match goal with |- ?X => quote_term X ltac:(fun tm =>
    reflect_formula tm ([]:list num) 0%nat ltac:(fun f csts _ =>
      let cenv := mkcenv csts in
      eapply (@cooper_qe_theorem cenv f); [
        cbv; reflexivity
      | cbv; reflexivity
      | cbv [interpret_formula interpret_predicate
             interpret_term interpret_constant nthZ]
      ]
    )
  ) end.

Goal exists x, 0 <= 2 * x + 5 \/ x > 3.
  qe. cbn. lia.
Qed.

Goal forall a, exists x, a <= x /\ x < a + 1.
  intro. qe.
  lia.
Qed.

Goal forall a b, ~ (exists x, ~(~ (b < x) \/ a <= x)).
  intros. qe.
Abort.
