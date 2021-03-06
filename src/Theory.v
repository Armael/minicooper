Set Implicit Arguments.
Require Import ZArith Psatz.
Require Import Znumtheory.
Require Import Classical.
Require Import FunInd Recdef.
Require Import List.
Import ListNotations.
Require Import MiniCooper.MyTactics.
Require Import MiniCooper.Constant.
Open Scope list_scope.
Open Scope Z_scope.


(* ------------------------------------------------------------------------- *)

(* Arithmetic lemmas. *)

Ltac Zabs_either :=
  match goal with |- context[Z.abs ?k] =>
    pattern (Z.abs k); eapply Zabs_intro; intros
  end.

Ltac quotient q :=
  match goal with
  h: (?z | ?l), nz: ?z <> 0 |- _ =>
    let eq := fresh in
    destruct h as [ q eq ];
    rewrite eq in *; (* replace [l] with [q * z] *)
    try rewrite (@Z_div_mult_full q z nz) in * (* replace [l / z] with [q] *)
 end.

Lemma nonzero_quotient:
  forall z l,
  l <> 0 ->
  z <> 0 ->
  (z | l) ->
  l / z <> 0.
Proof.
  intros. quotient q. intro. subst. omega.
Qed.

Lemma sign_multiply_is_Zabs:
  forall q,
  q / Z.abs q * q = Z.abs q.
Proof.
  intros.
  destruct (@Ztrichotomy q 0) as [ | [ | ]].
  (* Sub-case: [q < 0]. *)
  rewrite Zabs_non_eq; try omega.
  rewrite Z_div_zero_opp_r; eauto using Z_mod_same_full.
  rewrite Z_div_same_full; try omega.
  (* Sub-case: [q = 0]. *)
  subst. auto.
  (* Sub-case: [q > 0]. *)
  rewrite Z.abs_eq; try omega.
  rewrite Z_div_same_full; omega.
Qed.

Lemma Zlcm_pos:
  forall a b,
  0 < a ->
  0 < b ->
  0 < Z.lcm a b.
Proof.
  intros. rewrite Z.le_neq. split. apply Z.lcm_nonneg.
  intro HH. symmetry in HH. rewrite Z.lcm_eq_0 in HH. lia.
Qed.

Hint Constructors Forall.

Lemma Forall_app : forall A P (l1 l2: list A),
  Forall P l1 ->
  Forall P l2 ->
  Forall P (l1 ++ l2).
Proof.
  induction l1; intros; simpl in *; eauto.
  match goal with h: Forall _ (_ :: _) |- _ => depelim h end.
  auto.
Qed.

(* ------------------------------------------------------------------------- *)

(* Our model is Z. *)

Notation num := Z.

(* We represent variables using de Bruijn indices. *)

Notation var := nat.

(* An environment is a total function of variables into the model. *)

Notation environment := (var -> num).

(* Extensional equality of environments. *)

Definition enveq (env1 env2 : environment) : Prop :=
  forall x, env1 x = env2 x.

(* ------------------------------------------------------------------------- *)

(* A term is a sum of summands of the form [k.x], where [k] is a constant and
   [x] is a variable, and of a final constant. *)

Inductive term :=
| TSummand: num -> var -> term -> term
| TConstant: constant -> term.

(* The logical interpretation of a term. *)

Fixpoint interpret_term (cenv env : environment) (t : term) : num :=
  match t with
  | TSummand k y u =>
      k * env y + interpret_term cenv env u
  | TConstant c =>
      interpret_constant cenv c
  end.

(* A term is well-formed if its coefficients are non-zero and its variables
   are sorted in increasing order. *)

Inductive wft : var -> term -> Prop :=
| WftSummand:
    forall x k y u,
    k <> 0 ->
    (x <= y)%nat ->
    wft (S y) u ->
    wft x (TSummand k y u)
| WftConstant:
    forall x k,
    wft x (TConstant k).

Hint Constructors wft.

Lemma wft_monotone:
  forall x1 x2 t,
  wft x2 t ->
  (x1 <= x2)%nat ->
  wft x1 t.
Proof.
  induction 1; intros; eauto.
Qed.

(* ------------------------------------------------------------------------- *)

(* Multiplication of a term by a constant. *)

Fixpoint mul_nonzero (n : num) (t : term) : term :=
  match t with
  | TSummand k x u =>
      TSummand (n * k) x (mul_nonzero n u)
  | TConstant k =>
      TConstant (cmul n k)
  end.

Definition mul (n : num) (t : term) : term :=
  if Z.eq_dec n 0 then TConstant (CGround 0) else mul_nonzero n t.

Lemma wf_mul_nonzero:
  forall n,
  n <> 0 ->
  forall x t,
  wft x t ->
  wft x (mul_nonzero n t).
Proof.
  induction 2; simpl; econstructor; eauto. nia.
Qed.

Lemma wf_mul:
  forall n x t,
  wft x t ->
  wft x (mul n t).
Proof.
  intros. unfold mul. destruct (Z.eq_dec n 0); eauto using wf_mul_nonzero.
Qed.

Lemma interpret_mul_nonzero:
  forall cenv env n t,
  interpret_term cenv env (mul_nonzero n t) = n * interpret_term cenv env t.
Proof.
  induction t; simpl; auto. rewrite IHt. ring. now rewrite interpret_cmul.
Qed.

Lemma interpret_mul:
  forall cenv env n t,
  interpret_term cenv env (mul n t) = n * interpret_term cenv env t.
Proof.
  intros. unfold mul. destruct (Z.eq_dec n 0).
  subst. simpl. auto.
  eauto using interpret_mul_nonzero.
Qed.

(* ------------------------------------------------------------------------- *)

(* Negation of a term. *)

Definition neg t :=
  mul (-1) t.

Lemma wf_neg:
  forall x t,
  wft x t ->
  wft x (neg t).
Proof.
  unfold neg. eauto using wf_mul.
Qed.

Lemma interpret_neg:
  forall cenv env t,
  interpret_term cenv env (neg t) = -(interpret_term cenv env t).
Proof.
  unfold neg. intros. rewrite interpret_mul. ring.
Qed.

(* ------------------------------------------------------------------------- *)

(* Addition of two terms. *)

(* This is analogous to merging two sorted lists. *)

(* TEMPORARY comparison over nat is very inefficient; use positive or some
   other representation of terms? *)

Fixpoint add (t1 t2 : term) : term :=
  let fix add_t1 t2 :=
    match t1, t2 with
    | TSummand k1 x1 u1, TSummand k2 x2 u2 =>
        match Nat.compare x1 x2 with
        | Eq =>
            (* [x1 = x2] *)
            let k := k1 + k2 in
            if Z.eq_dec k 0 then
              add u1 u2
            else
              TSummand k x1 (add u1 u2)
        | Lt =>
            (* [x1 < x2] *)
            TSummand k1 x1 (add u1 t2)
        | Gt =>
            (* [x1 > x2] *)
            TSummand k2 x2 (add_t1 u2)
        end
    | TSummand k1 x1 u1, TConstant _ =>
        TSummand k1 x1 (add u1 t2)
    | TConstant _, TSummand k2 x2 u2 =>
        TSummand k2 x2 (add_t1 u2)
    | TConstant k1, TConstant k2 =>
        TConstant (cadd k1 k2)
    end
  in
  add_t1 t2.

Lemma wf_add:
  forall t1 t2 x,
  wft x t1 ->
  wft x t2 ->
  wft x (add t1 t2).
Proof.
  induction t1 as [ k1 x1 u1 | k1 ];
  induction t2 as [ k2 x2 u2 | k2 ];
  inversion 1; inversion 1; subst; simpl.
  (* Case TSummand/TSummand. *)
  case_eq (Nat.compare x1 x2); intro.
    (* Sub-case x1 = x2. *)
    applyin nat_compare_eq.
    (* forwards: nat_compare_eq.  eassumption.*)
    destruct (Z.eq_dec (k1 + k2) 0); eauto using wft_monotone.
    (* Sub-case x1 < x2. *)
    applyin nat_compare_Lt_lt.
    (* forwards: nat_compare_Lt_lt. eassumption. *)
    eauto using wft_monotone.
    (* Sub-case x1 > x2. *)
    applyin nat_compare_Gt_gt.
    (* forwards: nat_compare_Gt_gt. eassumption. *)
    eauto using wft_monotone.
  (* Case TSummand/TConstant. *)
  eauto.
  (* Case TConstant/TSummand. *)
  eauto.
  (* Case TConstant/TConstant. *)
  eauto.
Qed.

Lemma interpret_add:
  forall cenv env t1 t2,
  interpret_term cenv env (add t1 t2) =
  interpret_term cenv env t1 + interpret_term cenv env t2.
Proof.
  induction t1 as [ k1 x1 u1 | k1 ];
  induction t2 as [ k2 x2 u2 | k2 ];
  simpl.
  (* Case TSummand/TSummand. *)
  case_eq (Nat.compare x1 x2); intro.
    (* Sub-case x1 = x2. *)
    applyin nat_compare_eq.
    (* forwards: nat_compare_eq. eassumption.  *)subst x1.
    destruct (Z.eq_dec (k1 + k2) 0) as [ k1k2 | ].
      (* Sub-sub-case k1 + k2 = 0. *)
      match goal with |- ?lhs = _ =>
        assert (lhs = lhs + (k1 + k2) * env x2) as -> end.
      now rewrite k1k2; ring. rewrite IHu1. ring.
      (* Sub-sub-sub k1 + k2 <> 0. *)
      simpl. rewrite IHu1. ring.
    (* Sub-case x1 < x2. *)
    simpl. rewrite IHu1. simpl. ring.
    (* Sub-case x1 > x2. *)
    simpl in *. rewrite IHu2. ring.
  (* Case TSummand/TConstant. *)
  rewrite IHu1. simpl. ring.
  (* Case TConstant/TSummand. *)
  simpl in *. rewrite IHu2. ring.
  (* Case TConstant/TConstant. *)
  rewrite interpret_cadd. ring.
Qed.

(* ------------------------------------------------------------------------- *)

(* Subtraction of two terms. *)

Definition sub t1 t2 :=
  add t1 (neg t2).

Lemma wf_sub:
  forall t1 t2 x,
  wft x t1 ->
  wft x t2 ->
  wft x (sub t1 t2).
Proof.
  unfold sub. eauto using wf_add, wf_neg.
Qed.

Lemma interpret_sub:
  forall cenv env t1 t2,
  interpret_term cenv env (sub t1 t2) =
  interpret_term cenv env t1 - interpret_term cenv env t2.
Proof.
  intros. unfold sub. rewrite interpret_add. rewrite interpret_neg. ring.
Qed.

(* ------------------------------------------------------------------------- *)

(* Environment extension, in de Bruijn style. *)

(* A new variable 0 is introduced; pre-existing variables are shifted. *)

Definition extend (env : environment) (z : num) : environment :=
  fun (y : nat) =>
    match y with
    | O => z
    | S y => env y
    end.

Lemma extend_extensional:
  forall env1 env2,
  enveq env1 env2 ->
  forall z,
  enveq (extend env1 z) (extend env2 z).
Proof.
  unfold enveq. intros ? ? ? ? [ | ]; simpl; eauto.
Qed.

Lemma extend_env_other:
  forall env n1 n2 y,
  (y > 0)%nat ->
  extend env n1 y = extend env n2 y.
Proof.
  intros. destruct y. exfalso; omega. auto.
Qed.

(* If the variable 0 does not occur in the term [t], then the interpretation of
   [t] does not depend upon the interpretation of this variable. *)

Lemma extend_insensitive:
  forall cenv env n1 n2 x t,
  wft x t ->
  (x > 0)%nat ->
  interpret_term cenv (extend env n1) t = interpret_term cenv (extend env n2) t.
Proof.
  induction 1; intros; simpl; auto.
  rewrite IHwft; eauto. erewrite extend_env_other; eauto.
Qed.

(* ------------------------------------------------------------------------- *)

(* Change of variables, in de Bruijn style. *)

(* The variable 0 is scaled down by a factor of [l], that is, the value of the
   new variable represents [l] times the value of the old variable. Other
   variables are unaffected. *)

Definition adjust_env l env : environment :=
  fun (y : nat) =>
    match y with
    | O => l * env O
    | S _ => env y
    end.

Lemma adjust_env_other:
  forall l env y,
  (y > 0)%nat ->
  adjust_env l env y = env y.
Proof.
  intros. destruct y. exfalso; omega. auto.
Qed.

(* If the variable 0 does not occur in the term [t], then the interpretation of
   [t] is not affected by this change of variables. *)

Lemma adjust_insensitive:
  forall cenv l env x t,
  wft x t ->
  (x > 0)%nat ->
  interpret_term cenv (adjust_env l env) t = interpret_term cenv env t.
Proof.
  induction 1; intros; simpl; auto.
  rewrite IHwft; eauto. rewrite adjust_env_other; eauto.
Qed.

(* ------------------------------------------------------------------------- *)

(* An atomic formula is of the form [0 = t], [0 < t], or [c divides t]. On top
   of this, we build a first-order logic. *)

Inductive predicate :=
| Eq: predicate (* 0 = *)
| Lt: predicate (* 0 < *)
| Dv: num -> predicate (* c divides *).

Inductive formula :=
| FAtom: predicate -> term -> formula
| FFalse: formula
| FTrue: formula
| FAnd: formula -> formula -> formula
| FOr: formula -> formula -> formula
| FNot: formula -> formula
| FExists: formula -> formula.

(* The logical interpretation of a formula. *)

Definition interpret_predicate (p : predicate) (t : num) : Prop :=
  match p with
  | Eq =>
      0 = t
  | Lt =>
      0 < t
  | Dv d =>
      (d | t)
  end.

Fixpoint interpret_formula cenv env (f : formula) : Prop :=
  match f with
  | FAtom p t =>
      interpret_predicate p (interpret_term cenv env t)
  | FFalse =>
      False
  | FTrue =>
      True
  | FAnd f1 f2 =>
      interpret_formula cenv env f1 /\ interpret_formula cenv env f2
  | FOr f1 f2 =>
      interpret_formula cenv env f1 \/ interpret_formula cenv env f2
  | FNot f =>
      ~ interpret_formula cenv env f
  | FExists f =>
      exists z, interpret_formula cenv (extend env z) f
  end.

(* A definition of the predicate ``all atoms in the (quantifier-free) formula
   F satisfy the predicate P''. *)

Inductive all (P : predicate -> term -> Prop) : formula -> Prop :=
| all_FAtom:
    forall p t,
    P p t ->
    all P (FAtom p t)
| all_FFalse:
    all P FFalse
| all_FTrue:
    all P FTrue
| all_FAnd:
    forall f1 f2,
    all P f1 ->
    all P f2 ->
    all P (FAnd f1 f2)
| all_FOr:
    forall f1 f2,
    all P f1 ->
    all P f2 ->
    all P (FOr f1 f2)
| all_FNot:
    forall f,
    all P f ->
    all P (FNot f).

(* A characterization of quantifier-free formulae. *)

Notation qf f :=
  (all (fun p t => True) f).

(* A characterization of NNF form: negations are applied only to atoms,
   and negated inequalities are not permitted.
   Our NNF forms are quantifier-free. *)

Inductive nnf : formula -> Prop :=
| nnf_FAtom:
    forall p t,
    nnf (FAtom p t)
| nnf_FNot_FAtom:
    forall p t,
    p <> Lt ->
    nnf (FNot (FAtom p t))
| nnf_FAnd:
    forall f1 f2,
    nnf f1 ->
    nnf f2 ->
    nnf (FAnd f1 f2)
| nnf_FOr:
    forall f1 f2,
    nnf f1 ->
    nnf f2 ->
    nnf (FOr f1 f2)
| nnf_FTrue:
    nnf FTrue
| nnf_FFalse:
    nnf FFalse.

Hint Constructors all nnf.
Hint Extern 1 (_ <> Lt) => congruence.

(* The predicate [all P] is covariant in [P]. *)

Lemma all_covariant:
  forall (P Q : predicate -> term -> Prop),
  (forall p t, P p t -> Q p t) ->
  forall f,
  all P f ->
  all Q f.
Proof.
  induction 2; eauto.
Qed.

(* Well-formed predicates rule out "divisible by 0" atoms *)

Inductive wfp : predicate -> Prop :=
| WfpDv : forall c,
  0 < c -> wfp (Dv c)
| WfpEq :
  wfp Eq
| WfpLt :
  wfp Lt.

Hint Constructors wfp.

(* A characterization of formulae where all terms and predicates are
   well-formed. *)

Notation wff :=
  (all (fun p t => wft 0 t /\ wfp p)).

(* ------------------------------------------------------------------------- *)

(* The interpretation of terms and formulas is compatible with extensional
   equality of environments. *)

Lemma interpret_term_extensional:
  forall cenv env1 env2,
  enveq env1 env2 ->
  forall t,
  interpret_term cenv env1 t = interpret_term cenv env2 t.
Proof.
  induction t; simpl; congruence.
Qed.

Lemma interpret_formula_extensional:
  forall cenv f env1 env2,
  enveq env1 env2 ->
  ( interpret_formula cenv env1 f <-> interpret_formula cenv env2 f ).
Proof.
  induction f; intros; simpl; try tauto.
  (* Case: [FAtom]. *)
  erewrite interpret_term_extensional; [ idtac | eauto ]. tauto.
  (* Case: [FAnd]. *)
  specialize (IHf1 env1 env2).
  specialize (IHf2 env1 env2). tauto.
  (* Case: [FOr]. *)
  specialize (IHf1 env1 env2).
  specialize (IHf2 env1 env2). tauto.
  (* Case: [FNot]. *)
  specialize (IHf env1 env2). tauto.
  (* Case: [FExists]. *)
  split; intros [ z ? ]; exists z; [ rewrite <-IHf | rewrite IHf ];
  eauto using extend_extensional.
Qed.

(* ------------------------------------------------------------------------- *)

(* A tactic that destructs a predicate, if there is one in the assumptions. *)

Ltac predicate :=
  match goal with p: predicate |- _ => destruct p end.

(* A tactic that destructs an all-atoms-satisfy-P assumption. *)

Ltac all :=
  match goal with h: all _ _ |- _ => first [ now depelim h | depelim h;[] ] end.

(* A tactic that destructs a term, distinguishing the TSummand and TConstant
   cases, and in the former case, distinguishing the variable 0 from other
   variables. *)

Ltac term :=
  match goal with t: term |- _ => destruct t as [ ? [ | ? ] ? | ? ] end.

(* A tactic that destructs a [wft] assumption. *)

Ltac wft :=
  match goal with h: wft _ _ |- _ => depelim h end.

Ltac wfp :=
  match goal with h: wfp ?p |- _ => depelim h end.

Ltac wff :=
  match goal with
  | h: wff _ |- _ => depelim h
  | h: wft _ _ /\ wfp _ |- _ => simpl in h; destruct h
  end.

Ltac nnf :=
  match goal with h: nnf _ |- _ => depelim h end.

Ltac classical :=
  match goal with
  | h: ~ ~ _ |- _ => apply NNPP in h
  | h: ~ (_ /\ _) |- _ => apply not_and_or in h
  | h: ~ (_ \/ _) |- _ => apply not_or_and in h
  end.

(* ------------------------------------------------------------------------- *)

(* [wff] and [nnf] both entail that the formula is quantifier-free. *)

Lemma qf_nnf:
  forall f,
  nnf f ->
  qf f.
Proof.
  induction f; intros; simpl in *; nnf; eauto.
Qed.

Lemma qf_wff:
  forall f,
  wff f ->
  qf f.
Proof.
  intros. eapply all_covariant; [|eassumption]. eauto.
Qed.

(* Smart constructors for conjunction, disjunction, and negation. *)

(* Conjunction *)

Definition conjunction f1 f2 :=
  match f1, f2 with
  | FFalse, _
  | _, FFalse =>
      FFalse
  | FTrue, f
  | f, FTrue =>
      f
  | _, _ =>
      FAnd f1 f2
  end.

Lemma interpret_conjunction:
  forall cenv env f1 f2,
  interpret_formula cenv env (conjunction f1 f2) <->
  interpret_formula cenv env f1 /\ interpret_formula cenv env f2.
Proof.
  intros. unfold conjunction. destruct f1; destruct f2; simpl; tauto.
Qed.

Lemma all_conjunction:
  forall f1 f2 P,
  all P f1 ->
  all P f2 ->
  all P (conjunction f1 f2).
Proof.
  intros; destruct f1; destruct f2; simpl in *; eauto.
Qed.

Definition wf_conjunction := all_conjunction.

Lemma nnf_conjunction:
  forall f1 f2,
  nnf f1 ->
  nnf f2 ->
  nnf (conjunction f1 f2).
Proof.
  intros; destruct f1; destruct f2; simpl in *; eauto.
Qed.

(* Disjunction *)

Definition disjunction f1 f2 :=
  match f1, f2 with
  | FTrue, _
  | _, FTrue =>
      FTrue
  | FFalse, f
  | f, FFalse =>
      f
  | _, _ =>
      FOr f1 f2
  end.

Lemma interpret_disjunction:
  forall cenv env f1 f2,
  interpret_formula cenv env (disjunction f1 f2) <->
  interpret_formula cenv env f1 \/ interpret_formula cenv env f2.
Proof.
  intros. unfold disjunction. destruct f1; destruct f2; simpl; tauto.
Qed.

Lemma all_disjunction:
  forall f1 f2 P,
  all P f1 ->
  all P f2 ->
  all P (disjunction f1 f2).
Proof.
  intros; destruct f1; destruct f2; simpl in *; eauto.
Qed.

Definition wf_disjunction := all_disjunction.

Lemma nnf_disjunction:
  forall f1 f2,
  nnf f1 ->
  nnf f2 ->
  nnf (disjunction f1 f2).
Proof.
  intros; destruct f1; destruct f2; simpl in *; eauto.
Qed.

(* Negation *)

Definition negation f :=
  match f with
  | FTrue =>
      FFalse
  | FFalse =>
      FTrue
  | FNot f =>
      f
  | f =>
      FNot f
  end.

Lemma interpret_negation:
  forall cenv env f,
  interpret_formula cenv env (negation f) <-> ~ interpret_formula cenv env f.
Proof.
  (* Note: The elimination of double negation requires classical reasoning. *)
  intros. unfold negation. destruct f; simpl; tauto.
Qed.

Lemma all_negation:
  forall f P,
  all P f ->
  all P (negation f).
Proof.
  intros; destruct f; simpl in *; all; eauto.
Qed.

Definition wf_negation := all_negation.

(* Iterated disjunction, and iterated \/ *)

Definition big_disjunction A (F : A -> formula) (l : list A) : formula :=
  fold_right (fun x Q => disjunction (F x) Q) FFalse l.

Definition big_or A (P : A -> Prop) (l : list A) : Prop :=
  fold_right (fun x Q => P x \/ Q) False l.

Lemma interpret_big_disjunction:
  forall A cenv env (F : A -> formula) l,
  interpret_formula cenv env (big_disjunction F l) <->
  big_or (fun x => interpret_formula cenv env (F x)) l.
Proof.
  induction l; simpl; try tauto.
  rewrite interpret_disjunction. tauto.
Qed.

Lemma all_big_disjunction:
  forall A (F : A -> formula) (l : list A) P,
  (forall x,
   In x l ->
   all P (F x)) ->
  all P (big_disjunction F l).
Proof.
  intros * HH.
  induction l; simpl in *; eauto.
  apply all_disjunction; eauto.
Qed.

Lemma nnf_big_disjunction:
  forall A (F : A -> formula) (l : list A),
  (forall x,
   In x l ->
   nnf (F x)) ->
  nnf (big_disjunction F l).
Proof.
  intros. induction l; simpl in *; eauto.
  apply nnf_disjunction; eauto.
Qed.

Lemma big_or_prove : forall A (P : A -> Prop) l x,
  In x l ->
  P x ->
  big_or P l.
Proof.
  induction l; intros * HIn; inversion HIn.
  - subst. cbn. tauto.
  - intros. simpl. eauto.
Qed.

Lemma big_or_inv : forall A (P : A -> Prop) l,
  big_or P l ->
  exists x, In x l /\ P x.
Proof.
  induction l; intros * H; simpl in H; try tauto.
  firstorder.
Qed.

Lemma big_or_extens : forall A (P1 P2 : A -> Prop) l,
  (forall x, P1 x <-> P2 x) ->
  big_or P1 l <-> big_or P2 l.
Proof.
  intros * E. induction l; intros; simpl in *; try tauto.
  rewrite IHl, E; tauto.
Qed.

Lemma big_or_distr : forall A (P1 P2 : A -> Prop) l,
  big_or (fun x => P1 x \/ P2 x) l <->
  big_or P1 l \/ big_or P2 l.
Proof.
  induction l; intros; simpl in *; tauto.
Qed.

(* Or we could setup rewriting under [big_or]... *)
Lemma interpret_big_disjunction2:
  forall A B cenv env (F : A -> B -> formula) l1 l2,
  interpret_formula cenv env
    (big_disjunction (fun x => big_disjunction (F x) l1) l2) <->
  big_or (fun x => big_or (fun y => interpret_formula cenv env (F x y)) l1) l2.
Proof.
  intros. rewrite interpret_big_disjunction. apply big_or_extens.
  intros. rewrite interpret_big_disjunction. reflexivity.
Qed.

(* Intervals, to use as support for [big_disjunction] and [big_or]. *)
(* TODO: use [seq] instead *)

(* The interval of 0 (included) to n (excluded): [0, n). *)

Fixpoint interval' (n : nat) : list Z :=
  match n with
  | O => []
  | S n' => Z.of_nat n' :: interval' n'
  end.

Definition interval (x : Z) : list Z :=
  interval' (Z.to_nat x).

Lemma In_interval' : forall x n,
  In x (interval' n) <-> 0 <= x < Z.of_nat n.
Proof.
  induction n; intros.
  - simpl. lia.
  - cbn [interval' In]. destruct (Z.eq_dec x (Z.of_nat n)); [ lia |].
    split; intro.
    + intuition lia.
    + rewrite IHn. lia.
Qed.

Lemma In_interval : forall x n,
  In x (interval n) <-> 0 <= x < n.
Proof.
  intros. unfold interval. rewrite In_interval'.
  split; intro; rewrite Z2Nat.id in *; try lia.
  destruct n; simpl in *; lia.
Qed.

(* ------------------------------------------------------------------------- *)

(* Bringing a formula into NNF form. *)

(* This transformation will be applied only to quantifier-free formulae, so
   we are happy to do nothing in the [FExists] case. *)

Fixpoint posnnf (f : formula) : formula :=
  match f with
  | FNot f =>
      negnnf f
  | FAnd f1 f2 =>
      FAnd (posnnf f1) (posnnf f2)
  | FOr f1 f2 =>
      FOr (posnnf f1) (posnnf f2)
  | FTrue
  | FFalse
  | FAtom _ _
  | FExists _
    => f
  end

with negnnf (f : formula) : formula :=
  match f with
  | FNot f =>
      posnnf f
  | FAnd f1 f2 =>
      FOr (negnnf f1) (negnnf f2)
  | FOr f1 f2 =>
      FAnd (negnnf f1) (negnnf f2)
  | FTrue =>
      FFalse
  | FFalse =>
      FTrue
  | FAtom Lt t =>
      (* Negated inequalities are not permitted by our assumptions.
         Reverse them. The atom [~(0 < t)] can be transformed into
         [0 < 1 - t]. *)
      FAtom Lt (sub (TConstant (CGround 1)) t)
  | FAtom _ _
  | FExists _ =>
      FNot f
  end.

Lemma interpret_posnnf:
  forall cenv env f,
  interpret_formula cenv env (posnnf f) <-> interpret_formula cenv env f
with interpret_negnnf:
  forall cenv env f,
  interpret_formula cenv env (negnnf f) <-> ~ interpret_formula cenv env f.
Proof.
  (* Proof of the first lemma. *)
  induction f; simpl; try tauto. auto.
  (* Proof of the second lemma. *)
  induction f; try predicate; simpl; try tauto.
    (* Case: [Lt] atoms. *)
    rewrite interpret_sub.
    simpl (interpret_term cenv env (TConstant (CGround 1))).
    omega. (* cool *)
    (* Case: [FNot]. Again, classical reasoning is required. *)
    split.
    specialize (interpret_posnnf cenv env f). tauto.
    intro. apply <- interpret_posnnf. tauto.
Qed.

Lemma nnf_posnnf:
  forall f,
  qf f ->
  nnf (posnnf f)
with nnf_negnnf:
  forall f,
  qf f ->
  nnf (negnnf f).
Proof.
  (* Proof of the first lemma. *)
  induction f; intros; simpl; try all; eauto.
  (* Proof of the second lemma. *)
  induction f; intros; try predicate; simpl; try all; eauto.
Qed.

Lemma wf_posnnf:
  forall f,
  wff f ->
  wff (posnnf f)
with wf_negnnf:
  forall f,
  wff f ->
  wff (negnnf f).
Proof.
  induction f; intros; simpl; try all; eauto.
  induction f; intros; try predicate; simpl; try all;
    unpack; eauto using wf_sub.
Qed.

(* ------------------------------------------------------------------------- *)

(* Throughout the quantifier elimination procedure, the variable [x] which we
   wish to eliminate is the de Bruijn index [0]. This means that [x] always
   appear in front of a term, if it appears at all. *)

(* ------------------------------------------------------------------------- *)

(* Computing the least common multiple of the coefficients of [x] in a
   quantifier-free formula. *)

(* Collect all coefficients and compute their LCM. *)

Fixpoint formula_lcm (f : formula) : num :=
  match f with
  | FAtom _ (TSummand c 0 _) =>
      Z.abs c
  | FAtom _ (TSummand _ _ _)
  | FAtom _ (TConstant _)
  | FFalse
  | FTrue
  | FExists _ =>
      1
  | FAnd f1 f2
  | FOr f1 f2 =>
      Z.lcm (formula_lcm f1) (formula_lcm f2)
  | FNot f =>
      formula_lcm f
  end.

(* Characterize what is computed: a common multiple of all coefficients
   of [x]. The fact that this is the least common multiple does not seem
   to be required for soundness. *)

(* We write [all (dvx l) f] when all coefficients of [x] in the formula [f]
   divide [l]. *)

Definition dvx (l : num) (p : predicate) (t : term) : Prop :=
  match t with
  | TSummand c 0 _ =>
      (c | l)
  | TSummand _ _ _
  | TConstant _ =>
      True
  end.

Lemma dvx_transitive:
  forall l1 l2 p t,
  dvx l1 p t ->
  (l1 | l2) ->
  dvx l2 p t.
Proof.
  intros; term; simpl in *; eauto using Z.divide_trans.
Qed.

Lemma all_dvx_transitive:
  forall l1 l2 f,
  all (dvx l1) f ->
  (l1 | l2) ->
  all (dvx l2) f.
Proof.
  induction 1; intros; econstructor; eauto using dvx_transitive.
Qed.

Lemma all_dvx_formula_lcm:
  forall f,
  qf f ->
  all (dvx (formula_lcm f)) f.
Proof.
  induction f; intros; try all; simpl; try solve [ econstructor ].
  (* Case: [FAtom]. *)
  econstructor. unfold dvx.
  term; eauto. rewrite Z.divide_abs_r. reflexivity.
  (* Case: [FAnd]. *)
  econstructor; eapply all_dvx_transitive;
    eauto using Z.divide_lcm_l, Z.divide_lcm_r.
  (* Case: [FOr]. *)
  econstructor; eapply all_dvx_transitive;
    eauto using Z.divide_lcm_l, Z.divide_lcm_r.
  (* Case: [FNot]. *)
  econstructor; eauto.
Qed.

Lemma formula_lcm_nonneg:
  forall f,
  wff f ->
  0 < formula_lcm f.
Proof.
  induction 1; simpl; eauto using Zlcm_pos with zarith.
  (* Case: [FAtom]. *)
  term; wff; wft; wfp; lia.
Qed.

Lemma formula_lcm_nonzero:
  forall f,
  wff f ->
  formula_lcm f <> 0.
Proof.
  intros. applyin formula_lcm_nonneg. lia.
Qed.

(* ------------------------------------------------------------------------- *)

(* Adjusting the coefficients of [x] in a quantifier-free formula. *)

(* We assume that the integer [l] has been computed by [formula_lcm] above.
   We multiply each atom by a constant factor, so that the coefficient of [x]
   reaches [l] -- or its opposite. Then, we immediately normalize the
   coefficient of [x] down to [1] or [-1], as we perform a change of variables
   and write [x] for [l.x]. *)

Fixpoint adjust (l : num) (f : formula) : formula :=
  match f with

  | FAtom Eq (TSummand c 0 u) =>

      (* Compute by how much we must multiply. *)
      let m := l / c in
      (* The coefficient of [x] becomes [l], but is renormalized to [1];
         the rest of the term is multiplied by [m]. *)
      FAtom Eq (TSummand 1 0 (mul m u))

  | FAtom Lt (TSummand c 0 u) =>

      (* Compute by how much we must multiply. *)
      let m := l / c in
      (* Make sure that this is a positive factor, as we can't reverse
         the predicate [Lt]. *)
      let am := Z.abs m in
      (* Thus, the coefficient of [x] will be renormalized to either
         [1] or [-1]. *)
      let coeffx := m / am in
      (* The coefficient of [x] is renormalized to [coeffx];
         the rest of the term is multiplied by [am]. *)
      FAtom Lt (TSummand coeffx 0 (mul am u))

  | FAtom (Dv d) (TSummand c 0 u) =>

      (* Compute by how much we must multiply. *)
      let m := l / c in
      (* The coefficient of [x] becomes [l], but is renormalized to [1];
         the rest of the term is multiplied by [m]. The divisor [d] is
         multiplied by [m], but we are careful to keep it positive. *)
      FAtom (Dv (Z.abs m * d)) (TSummand 1 0 (mul m u))

  | FAtom _ (TSummand _ _ _)
  | FAtom _ (TConstant _)
  | FExists _ =>
      f
  | FFalse =>
      FFalse
  | FTrue =>
      FTrue
  | FAnd f1 f2 =>
      FAnd (adjust l f1) (adjust l f2)
  | FOr f1 f2 =>
      FOr (adjust l f1) (adjust l f2)
  | FNot f =>
      FNot (adjust l f)
  end.

(* The following lemmas state that multiplying an atom by a (non-zero)
   constant factor does not affect its meaning. *)

Lemma scale_Eq_atom:
  forall k t u,
  k <> 0 ->
  t = k * u ->
  ( 0 = t <-> 0 = u ).
Proof. intros. nia. Qed.

Lemma scale_Lt_atom:
  forall k t u,
  0 < k ->
  t = k * u ->
  ( 0 < t <-> 0 < u ).
Proof. intros; nia. Qed.

Lemma scale_Dv_atom:
  forall k d1 d2 t1 t2,
  d1 = k * d2 ->
  k <> 0 ->
  t1 = k * t2 ->
  ( (d1 | t1) <-> (d2 | t2) ).
Proof.
  intros. split; intros * h; subst.
  (* Left to right. *)
  destruct h as [ q h ]. exists q.
  assert (i: t2 * k = (q * d2) * k).
  { rewrite Zmult_comm. rewrite h. ring. }
  clear h. rewrite <- (@Z_div_mult_full t2 k); eauto.
  rewrite i.
  rewrite Z_div_mult_full; eauto.
  (* Right to left. *)
  eauto using Zmult_divide_compat_l.
Qed.

Lemma scale_Dv_atom_Zabs:
  forall k d1 d2 t1 t2,
  d1 = Z.abs k * d2 ->
  k <> 0 ->
  t1 = k * t2 ->
  ( (d1 | t1) <-> (d2 | t2) ).
Proof.
  (* Either [Z.abs k] is [-k], or it is [k]. *)
  intro k. Zabs_either.
  (* Sub-case: [-k]. *)
  rewrite <-(Z.divide_opp_l d1). subst.
  eapply scale_Dv_atom; [ idtac | eauto | eauto ].
  ring.
  (* Sub-case: [k]. *)
  eauto using scale_Dv_atom.
Qed.

(* If [l] is indeed a common multiple of all the coefficients of [x], then
   the interpretation of the new formula [adjust l f], in an environment
   where the new [x] stands for [l] times the old [x], coincides with the
   interpretation of the old formula [f]. *)

Opaque Zmult.

Lemma interpret_adjust:
  forall l,
  l <> 0 ->
  forall cenv env f,
  all (dvx l) f ->
  wff f ->
  interpret_formula cenv (adjust_env l env) (adjust l f) <->
  interpret_formula cenv env f.
Proof.
  (* All cases but [FAtom] are trivial. *)
  induction 2; intros; all; simpl; try tauto.
  (* Distinguish several sub-cases, depending upon the predicate and the form of
     the term. *)
  predicate; term; unfold dvx in *; wff; wft; simpl;
  (* Solve the easy sub-cases where [x] does not appear. *)
  try solve [ tauto | erewrite adjust_insensitive; eauto; tauto ];
  (* In each remaining sub-case, [x] does not appear in the tail of the term. *)
  rewrite interpret_mul;
  erewrite adjust_insensitive; eauto;
  (* In each remaining sub-case, the goal can be simplified by replacing the
     quotient [l / z] with an integer meta-variable [q]. *)
  quotient q.

  (* Three interesting sub-cases remain. *)

  (* Sub-case: an equality atom where [x] occurs. *)
  eapply (@scale_Eq_atom q); nia.

  (* Sub-case: an inequality atom where [x] occurs. *)
  eapply (@scale_Lt_atom (Z.abs q)). nia.
  ring_simplify. rewrite sign_multiply_is_Zabs; eauto. ring.

  (* Sub-case: a divisibility atom where [x] occurs. *)
  eapply scale_Dv_atom_Zabs. eauto. nia. ring.
Qed.

Lemma interpret_adjust_formula_lcm:
  forall f,
  wff f ->
  forall cenv env,
  interpret_formula cenv (adjust_env (formula_lcm f) env)
    (adjust (formula_lcm f) f) <->
  interpret_formula cenv env f.
Proof.
  intros.
  eapply interpret_adjust.
  eauto using formula_lcm_nonzero.
  eapply all_dvx_formula_lcm. eauto using all_covariant.
  eassumption.
Qed.

Lemma nnf_adjust:
  forall f l,
  nnf f ->
  nnf (adjust l f).
Proof.
  induction f; intros; simpl in *; nnf; eauto.
  { predicate; term; eauto. }
  { unfold adjust. predicate; term; eauto. }
Qed.

(* After the formula has been transformed using [adjust], all coefficients of
   [x] are 1, except in inequality atoms, where they might be 1 or -1. *)

(* Furthermore, the formula is still well-formed. We combine the two
   properties, as it is easier to establish them together. (For an inequality
   atom, well-formedness requires the coefficient of [x] to be nonzero,
   whereas, for the atom to be normal, the coefficient must be 1 or -1.) *)

Definition normal (p : predicate) (t : term) : Prop :=
  match p with Dv d => 0 < d | _ => True end /\
  match p, t with
  | (Eq | Dv _), TSummand c 0 u =>
      c = 1 /\ wft 1%nat u
  | Lt, TSummand c 0 u =>
      (c = -1 \/ c = 1) /\ wft 1%nat u
  | _, TSummand _ _ _
  | _, TConstant _ =>
      wft 0%nat t
  end.

Lemma wf_normal:
  forall f,
  all normal f ->
  wff f.
Proof.
  induction f; intros; simpl in *; all; eauto.
  unfold normal in *. predicate; term; unpack; eauto.
Qed.

Hint Resolve wf_normal.

Lemma normal_adjust:
  forall l,
  l <> 0 ->
  forall f,
  all (dvx l) f ->
  wff f ->
  all normal (adjust l f).
Proof.
  induction 2; intros; all; simpl; eauto.
  (* Case [FAtom]. *)
  predicate; term; unfold dvx in *; wff; wft; wfp; econstructor; simpl;
    unfold normal; intuition eauto using wf_mul.
  (* Only the sub-case of [Lt] atoms is slightly non-trivial. *)
  { Zabs_either.
    left.
    rewrite Z_div_zero_opp_r; eauto using Z_mod_same_full.
    rewrite Z_div_same_full; eauto using nonzero_quotient.
    right.
    rewrite Z_div_same_full; eauto using nonzero_quotient. }
  { apply Z.mul_pos_pos; [|lia]. apply Z.abs_pos. apply nonzero_quotient; auto. }
Qed.

Lemma normal_adjust_formula_lcm:
  forall f,
  wff f ->
  all normal (adjust (formula_lcm f) f).
Proof.
  intros.
  eapply normal_adjust.
    eauto using formula_lcm_nonzero.
    eapply all_dvx_formula_lcm. eauto using all_covariant.
    eassumption.
Qed.

(* ------------------------------------------------------------------------- *)

(* Making sure that all coefficients of [x] in a quantifier-free formula
   are [1] or [-1]. *)

Definition unity (f : formula) : formula :=

  (* Compute the least common multiple of all coefficients of [x]. *)

  let l := formula_lcm f in

  (* Adjust all coefficients of [x] in the formula to be [1] or [-1].
     This represents a change of variable: the new [x] stands for the
     old [l.x]. *)

  let f := adjust l f in

  (* For the change of variable to make sense, we must add a constraint
     that [l] divides the new [x]. Of course, this is required only if
     [l] is not [1]. *)

  if Z.eq_dec l 1 then
    f
  else
    FAnd
      f
      (FAtom (Dv l) (TSummand 1 0 (TConstant (CGround 0)))).

(* This transformation is meaning-preserving. *)

Lemma interpret_formula_adjust_env_1:
  forall cenv env f,
  interpret_formula cenv env f <-> interpret_formula cenv (adjust_env 1 env) f.
Proof.
  intros. eapply interpret_formula_extensional.
  intros [ | ]; simpl; intros; ring.
Qed.

Lemma exists_equivalence:
  forall (A : Type) (P Q : A -> Prop),
  (forall z, P z <-> Q z) ->
  ( (exists z, P z) <-> (exists z, Q z) ).
Proof. firstorder. Qed.

Lemma interpret_unity:
  forall cenv env f,
  wff f ->
  interpret_formula cenv env (FExists f) <->
  interpret_formula cenv env (FExists (unity f)).
Proof.
  intros. unfold unity. simpl.
  destruct (Z.eq_dec (formula_lcm f) 1) as [ eq | _ ].
  (* Case: [formula_lcm f] is 1. No change of variables is required. *)
  eapply exists_equivalence; intro.
  rewrite (@interpret_formula_adjust_env_1 _ _ (adjust _ _)).
  rewrite <- eq.
  rewrite interpret_adjust_formula_lcm; eauto.
  tauto.
  (* General case. A change of variables is required. We consider the
     two directions of the equivalence separately. *)
  split; intros [ z ? ].
  (* Left to right. *)
  (* The new [x] represents [l] times the old [x]. *)
  exists ((formula_lcm f) * z). simpl. split.
  rewrite interpret_formula_extensional.
  eapply interpret_adjust_formula_lcm; eassumption.
  intros [ | ]; auto.
  exists z. ring.
  (* Right to left. *)
  (* The new [x] is divisible by [l]; the old [x] is the quotient [q]. *)
  simpl in *. unpack.
  replace (1 * z + 0) with z in *; [ idtac | ring ].
  assert (formula_lcm f <> 0). eauto using formula_lcm_nonzero.
  quotient q.
  exists q.
  rewrite <- interpret_adjust_formula_lcm; eauto.
  rewrite interpret_formula_extensional; eauto.
  intros [ | ]; simpl; eauto using Zmult_comm.
Qed.

Lemma normal_unity:
  forall f,
  wff f ->
  all normal (unity f).
Proof.
  intros. unfold unity.
  destruct (Z.eq_dec (formula_lcm f) 1).
  eauto using normal_adjust_formula_lcm.
  econstructor.
    eauto using normal_adjust_formula_lcm.
    econstructor. split; eauto using formula_lcm_nonneg.
Qed.

Lemma wf_unity:
  forall f,
  wff f ->
  wff (unity f).
Proof. eauto using normal_unity. Qed.

Lemma nnf_unity:
  forall f,
  nnf f ->
  nnf (unity f).
Proof.
  induction f; intros; simpl in *; nnf; eauto;
    unfold unity; case_if; eauto using nnf_adjust.
Qed.

(* ------------------------------------------------------------------------- *)

(* A subset of Z either admits arbitrarily large negative elements or admits a
   lower bound. *)

Notation sink P := (forall x, exists y, y < x /\ P y).
Notation lower_bound P := (exists x, forall y, y < x -> ~ P y).
Notation least_element P := (exists x, P x /\ forall y, y < x -> ~ P y).

Lemma sink_or_lower_bound:
  forall P : Z -> Prop,
  sink P \/ lower_bound P.
Proof.
  intro.
  (* Apply the excluded middle. *)
  match goal with |- ?P \/ _ => destruct (classic P) as [ h | h ] end.
  left. assumption.
  right.
  (* Push the negations inwards using de Morgan's laws. *)
  generalize (not_all_ex_not _ _ h); clear h; intros [ x h ].
  exists x; intros.
  generalize (not_ex_all_not _ _ h); clear h; intro h.
  specialize (h y).
  tauto.
Qed.

(* A non-empty subset of Z either that admits a lower bound admits a least
   element. *)

Lemma lower_bound_least_element_preliminary:
  (* For every subset P of Z, *)
  forall P : Z -> Prop,
  (* If P admits a lower bound, *)
  forall floor,
  (forall y, y < floor -> ~ P y) ->
  (* Then, for all y at or above this lower bound, *)
  forall y,
  floor <= y ->
  (* If there is an element of P below y, *)
  (exists x, P x /\ x < y) ->
  (* Then P admits a least element. *)
  (exists x, P x /\ forall y, y < x -> ~ P y).
Proof.
  (* The idea is that [y] sweeps from left to right. In the base case, [y] is
     [floor], and the statement is trivial, because there is no element of [P]
     below floor. If we can prove the inductive case, then we can sweep [y]
     arbitrarily far towards the right, so that the condition ``if there is an
     element of [P] below [y]'' in the limit becomes equivalent to ``if there
     is an element of [P]''. *)
  intros * hfloor.
  (* We prove this by well-founded induction, bounded below by [floor]. *)
  eapply (@Zlt_lower_bound_ind (fun y =>
    (exists x, P x /\ x < y) -> (exists x, P x /\ forall y, y < x -> ~ P y)
  )).
  intros y ih ? [ x [ ? ? ]].
  (* [x] satisfies [P], so it cannot be below [floor]. *)
  assert (~ x < floor). specialize (hfloor x). tauto.
  (* Either [x] is the least element of [P], or there is another solution of [P]
     between [floor] and [x]. Let us refer to it as [sx], for ``a smaller [x]''.
  *)
  destruct (classic (forall y, y < x -> ~ P y)) as [ | hsx ].
  solve [ eauto ].
  generalize (not_all_ex_not _ _ hsx); clear hsx; intros [ sx hsx ].
  generalize (imply_to_and _ _ hsx); clear hsx; intros [ ? hsx ].
  generalize (NNPP _ hsx); clear hsx; intros hsx.
  (* We may now use the induction hypothesis, where [sx] plays the role of [x],
     and [x] plays the role of [y]. *)
  eapply (ih x). omega. eauto.
Qed.

Lemma lower_bound_least_element:
  (* For every subset P of Z, *)
  forall P : Z -> Prop,
  (* If P admits a lower bound, *)
  forall floor,
  (forall y, y < floor -> ~ P y) ->
  (* And P is non-empty, *)
  (exists x, P x) ->
  (* Then P admits a least element. *)
  (exists x, P x /\ forall y, y < x -> ~ P y).
Proof.
  intros * hfloor [ x ? ].
  eapply lower_bound_least_element_preliminary with (y := x + 1).
  eassumption.
  assert (~ x < floor). specialize (hfloor x). tauto. omega.
  exists x. split. assumption. omega.
Qed.

(* A non-empty subset of Z either admits arbitrarily large negative elements or
   admits a least element. *)

Lemma sink_or_least_element:
  forall P : Z -> Prop,
  (exists x, P x) ->
  sink P \/ least_element P.
Proof.
  intros.
  destruct (@sink_or_lower_bound P) as [ | [ floor hfloor ] ].
  left. assumption.
  right. eauto using lower_bound_least_element.
Qed.

(* The reciprocal statement is of course true. *)

Lemma sink_or_least_element_reciprocal:
  forall P : Z -> Prop,
  sink P \/ least_element P ->
  exists x, P x.
Proof.
  intros * [ h | [ x [ ? ? ]]].
  specialize (h 0). unpack. eauto.
  eauto.
Qed.

Lemma exists_equiv_sink_or_least_element:
  forall P : Z -> Prop,
  (exists x, P x) <-> sink P \/ least_element P.
Proof.
  intros; split;
    eauto using sink_or_least_element, sink_or_least_element_reciprocal.
Qed.

(* ------------------------------------------------------------------------- *)

(* Computing the ``minus infinity'' version of a formula P. This new formula
   holds if and only if the original formula admits arbitrarily large negative
   solutions for [x]. As before, we take [x] to be the variable with de Bruijn
   index 0. *)

(* Note that the formula [minusinf f] still depends on [x], because divisibility
   atoms are unchanged and may still refer to [x]. *)

Function minusinf (f : formula) : formula :=
  match f with

  | FAtom Eq (TSummand c 0 _) =>

      (* [c] is 1. We have an equality on [x]. This can't be satisfied by
         arbitrarily small values of [x].  *)

      FFalse

  | FAtom Lt (TSummand c 0 _) =>

      (* [c] is 1 or -1. We have an inequality on [x]. This is satisfied by
         arbitrarily small values of [x] if and only if the coefficient [c] is
         negative. *)

      if Z.eq_dec c 1 then FFalse else FTrue

  | FAtom _ _
  | FExists _ =>

      (* Division atoms are insensitive to translation, so they are
         retained. Atoms that do not mention [x] at all are retained as
         well. *)

      f

  | FFalse =>
      FFalse
  | FTrue =>
      FTrue
  | FAnd f1 f2 =>
      conjunction (minusinf f1) (minusinf f2)
  | FOr f1 f2 =>
      disjunction (minusinf f1) (minusinf f2)
  | FNot f =>
      negation (minusinf f)

  end.

(* For sufficiently large negative [x], [f] and [minusinf f] are equivalent. *)

Lemma interpret_minusinf:
  forall cenv env f,
  all normal f ->
  exists y,
  forall x, x < y ->
  interpret_formula cenv (extend env x) f <->
  interpret_formula cenv (extend env x) (minusinf f).
Proof.
  induction 1; simpl; try solve [ exists 0; tauto ].
  (* Case [FAtom]. *)
  predicate; term; unfold normal in *; unpack;
  try solve [ exists 0; tauto ];
  try match goal with h: ?c = -1 \/ ?c = 1 |- _ => destruct h end;
  subst; simpl.
  (* Sub-case: an atom [0 = x + t]. This equality cannot be satisfied
     as [x] tends towards minus infinity. *)
  exists (- interpret_term cenv (extend env 0) t). intros.
  erewrite extend_insensitive with (n2 := 0). lia. eassumption. lia.
  (* Sub-case: an atom [0 < -x + t]. This equality is satisfied
     as [x] tends towards minus infinity. *)
  exists (interpret_term cenv (extend env 0) t). intros.
  erewrite extend_insensitive with (n2 := 0). lia. eassumption. lia.
  (* Sub-case: an atom [0 < x + t]. This equality cannot be satisfied
     as [x] tends towards minus infinity. *)
  exists (- interpret_term cenv (extend env 0) t). intros.
  erewrite extend_insensitive with (n2 := 0). lia. eassumption. lia.
  (* Case [FAnd]. *)
  destruct IHall1 as [ y1 ih1 ].
  destruct IHall2 as [ y2 ih2 ].
  exists (Z.min y1 y2). intros.
  unpack (Z.le_min_l y1 y2).
  unpack (Z.le_min_r y1 y2).
  rewrite interpret_conjunction.
  rewrite ih1; try omega.
  rewrite ih2; try omega.
  tauto.
  (* Case [FOr]. *)
  destruct IHall1 as [ y1 ih1 ].
  destruct IHall2 as [ y2 ih2 ].
  exists (Z.min y1 y2). intros.
  unpack (Z.le_min_l y1 y2).
  unpack (Z.le_min_r y1 y2).
  rewrite interpret_disjunction.
  rewrite ih1; try omega.
  rewrite ih2; try omega.
  tauto.
  (* Case [FNot]. *)
  destruct IHall as [ y ih ].
  exists y. intros.
  rewrite interpret_negation.
  rewrite ih; try omega.
  tauto.
Qed.

Lemma wf_minusinf:
  forall f,
  wff f ->
  wff (minusinf f).
Proof.
  induction f; intros; simpl in *; wff;
  eauto using wf_conjunction, wf_disjunction, wf_negation.
  wff; wfp; wft; eauto;
  match goal with |- wff (match ?y with _ => _ end) =>
    destruct y
  end; try case_if; eauto.
Qed.

Lemma nnf_minusinf:
  forall f,
  nnf f ->
  nnf (minusinf f).
Proof.
  induction f; intros; nnf; simpl in *;
    eauto using nnf_conjunction, nnf_disjunction.
  { predicate; term; eauto; case_if; eauto. }
  { predicate; term; eauto; simpl in *; eauto; congruence. }
Qed.

Lemma sink_minusinf_equiv:
  forall cenv env f,
  all normal f ->
  sink (fun x => interpret_formula cenv (extend env x) f) <->
  sink (fun x => interpret_formula cenv (extend env x) (minusinf f)).
Proof.
  intros * Hn.
  pose proof (interpret_minusinf cenv env Hn) as [y0 Hy0].
  split.
  { intros H x. destruct (H (Z.min x y0)) as [y' [? ?]].
    exists y'. rewrite <-Hy0 by lia. split; auto. lia. }
  { intros H x. destruct (H (Z.min x y0)) as [y' [? ?]].
    exists  y'. rewrite Hy0 by lia. split; auto. lia. }
Qed.

(* ------------------------------------------------------------------------- *)

(* Compute the least common multiple of the division atoms that involve [x]. *)

Fixpoint divlcm (f : formula) : num :=
  match f with
  | FAtom (Dv d) (TSummand c 0 _) =>
    (* [d] is positive *)
    d
  | FAnd f1 f2
  | FOr f1 f2 =>
    Z.lcm (divlcm f1) (divlcm f2)
  | FNot f =>
    divlcm f
  | _ =>
    1
  end.

(* Characterize what is computed: a common multiple of all division atoms
   involving [x]. The fact that this is the least common multiple does not seem
   to be required for soundness. *)

(* We write [all (dvdvx l) f] when all division atoms involving [x] in the
   formula [f] divide [l]. *)

Definition dvdvx (l : num) (p : predicate) (t : term) : Prop :=
  match p with
  | Dv c =>
    match t with
    | TSummand _ 0 _ => (c | l)
    | _ => True
    end
  | Eq | Lt =>
    True
  end.

Lemma dvdvx_transitive:
  forall l1 l2 p t,
  dvdvx l1 p t ->
  (l1 | l2) ->
  dvdvx l2 p t.
Proof.
  intros. predicate; term; simpl in *; eauto using Z.divide_trans.
Qed.

Lemma all_dvdvx_transitive:
  forall l1 l2 f,
  all (dvdvx l1) f ->
  (l1 | l2) ->
  all (dvdvx l2) f.
Proof.
  induction 1; intros; econstructor; eauto using dvdvx_transitive.
Qed.

Lemma all_dvdvx_divlcm:
  forall f,
  wff f ->
  all (dvdvx (divlcm f)) f.
Proof.
  induction f; intros; try all; simpl; try solve [ econstructor ].
  (* Case: [FAtom]. *)
  { econstructor. unfold dvdvx. predicate; term; eauto using Z.divide_refl. }
  (* Case: [FAnd]. *)
  { econstructor; eapply all_dvdvx_transitive;
    eauto using Z.divide_lcm_l, Z.divide_lcm_r. }
  (* Case: [FOr]. *)
  { econstructor; eapply all_dvdvx_transitive;
    eauto using Z.divide_lcm_l, Z.divide_lcm_r. }
  (* Case: [FNot]. *)
  { econstructor; eauto. }
Qed.

Lemma divlcm_nonneg:
  forall f,
  wff f ->
  0 < divlcm f.
Proof.
  induction 1; simpl; eauto using Zlcm_pos with zarith.
  (* Case: [FAtom]. *)
  term; wff; wft; wfp; try omega.
Qed.

(* [minusinf f] is invariant by changing [x] to [x + k * (divlcm f)] for any
   [k]. *)

Lemma interpret_minusinf_modulo_dvdvx:
  forall cenv env f x k D,
  wff f ->
  all (dvdvx D) f ->
  interpret_formula cenv (extend env x) (minusinf f) <->
  interpret_formula cenv (extend env (x + k * D)) (minusinf f).
Proof.
  intros cenv env f.
  functional induction (minusinf f); intros; simpl; try tauto.
  { predicate; term; wff; wff; wft; simpl in *; try tauto;
    try solve [ erewrite extend_insensitive by eauto; reflexivity ].
    all; simpl in *.
    erewrite extend_insensitive with (n2 := x + k * D) by eauto.
    rewrite Z.mul_add_distr_l.
    rewrite <-Z.add_assoc, (Z.add_comm (z0 * (k * D))), Z.add_assoc.
    split; intro HD.
    - eauto with zarith.
    - rewrite Z.add_comm in HD.
      eapply Z.divide_add_cancel_r; [| apply HD].
      eauto with zarith. }
  { wff. }
  { wff. all. rewrite !interpret_conjunction.
    rewrite (IHf0 x k D), (IHf1 x k D) by auto. tauto. }
  { wff. all. rewrite !interpret_disjunction.
    rewrite (IHf0 x k D), (IHf1 x k D) by auto. tauto. }
  { wff. all. rewrite !interpret_negation.
    rewrite (IHf0 x k D) by auto. tauto. }
Qed.

Lemma interpret_minusinf_modulo_divlcm:
  forall cenv env f x k,
  wff f ->
  interpret_formula cenv (extend env x) (minusinf f) <->
  interpret_formula cenv (extend env (x + k * (divlcm f))) (minusinf f).
Proof.
  intros. eauto using interpret_minusinf_modulo_dvdvx, all_dvdvx_divlcm.
Qed.

(* ------------------------------------------------------------------------- *)

(* If [P] is invariant by translation modulo [D], then [sink P] is equivalent to
   a big disjunction (thus eliminating an existential quantifier). *)

Lemma sink_invariant_modulo_equiv_exists:
  forall P : Z -> Prop,
  forall D : Z,
  0 < D ->
  (forall x k, P x <-> P (x + k * D)) ->
  sink P <-> (exists y, P y).
Proof.
  intros * HD HPinv.
  split.
  { (* the trivial case *)
    intros H. destruct (H 0) as [y [? ?]]. eauto. }
  { intros [y Hy] x. destruct (Z_lt_le_dec y x). now eauto.
    exists (y + ((x - y) / D - 1) * D); split; cycle 1.
    now rewrite <-HPinv. pose proof (Z.mul_div_le (x - y) D); lia. }
Qed.

Lemma invariant_modulo_exists_equiv_big_or:
  forall P : Z -> Prop,
  forall D : Z,
  0 < D ->
  (forall x k, P x <-> P (x + k * D)) ->
  (exists y, P y) <-> big_or P (interval D).
Proof.
  intros * HD HPinv.
  split.
  { intros [y Hy]. apply big_or_prove with (y mod D).
    - pose proof (Z.mod_pos_bound y D). rewrite In_interval. lia.
    - rewrite HPinv with (k := y / D).
      rewrite Z.add_comm, Z.mul_comm, <-Z.div_mod; auto. }
  { intro H. destruct (big_or_inv _ _ H) as [i [H1 H2]]. eauto. }
Qed.

Lemma sink_equiv_big_or:
  forall P : Z -> Prop,
  forall D : Z,
  0 < D ->
  (forall x k, P x <-> P (x + k * D)) ->
  sink P <-> big_or P (interval D).
Proof.
  intros.
  rewrite sink_invariant_modulo_equiv_exists with D by auto.
  apply invariant_modulo_exists_equiv_big_or; auto.
Qed.

(* ------------------------------------------------------------------------- *)

(* Substitution of a term [t] for a variable [x] within a formula. *)

Fixpoint subst (t : term) (f : formula) : formula :=
  match f with
  | FAtom p (TSummand c 0 u) =>
    FAtom p (add (mul c t) u)
  | FNot f =>
    FNot (subst t f)
  | FAnd f1 f2 =>
    FAnd (subst t f1) (subst t f2)
  | FOr f1 f2 =>
    FOr (subst t f1) (subst t f2)
  | _ =>
    f
  end.

Lemma interpret_subst:
  forall cenv env f t u,
  wff f ->
  interpret_formula cenv (extend env u) (subst t f) <->
  interpret_formula cenv (extend env (interpret_term cenv (extend env u) t)) f.
Proof.
  induction 1; simpl; try tauto.
  term; wff; wft; simpl in *.
  rewrite interpret_add, interpret_mul.
  erewrite extend_insensitive with
    (n1:=interpret_term cenv (extend env u) t) (n2:=u) by eauto.
  tauto.
  erewrite extend_insensitive. reflexivity. eauto. eauto.
  tauto.
Qed.

Lemma wf_subst:
  forall f t,
  wft 0 t ->
  wff f ->
  wff (subst t f).
Proof.
  induction f; intros; simpl in *; wff; eauto.
  wff. destruct t; [destruct n|]; wft; eauto .
  constructor. split; auto. apply wf_add. apply wf_mul; auto.
  eapply wft_monotone. eauto. omega.
Qed.

Notation wff1 f := (all (fun p t => wft 1 t /\ wfp p) f).

Lemma wf1_subst:
  forall f t,
  wft 1 t ->
  wff f ->
  wff1 (subst t f).
Proof.
  induction f; intros; simpl in *; wff; eauto.
  wff. destruct t; [destruct n|]; wft; eauto using wf_add, wf_mul.
Qed.

Lemma nnf_subst:
  forall f t,
  nnf f ->
  nnf (subst t f).
Proof.
  induction f; intros; simpl in *; nnf; eauto; simpl;
  repeat
    match goal with |- context [ match ?x with _ => _ end ] => destruct x end;
  eauto.
Qed.

(* ------------------------------------------------------------------------- *)

(* Shifting (down) all the de Bruijn variables of a term. This only makes sense
   if the first variable does not appear in the term. *)

Fixpoint shift_term (t : term) : term :=
  match t with
  | TSummand c (S n) u =>
    TSummand c n (shift_term u)
  | _ =>
    t
  end.

Lemma wf_shift_term:
  forall t n,
  wft (S n) t ->
  wft n (shift_term t).
Proof.
  induction t; intros; wft; simpl; try now constructor.
  destruct n; auto with zarith.
Qed.

Lemma interpret_shift_term:
  forall cenv env t x,
  wft 1 t ->
  interpret_term cenv (extend env x) t = interpret_term cenv env (shift_term t).
Proof.
  induction t; intros; simpl in *; auto.
  wft. rewrite IHt. now destruct n.
  eapply wft_monotone; eauto with zarith.
Qed.

(* Same with a formula. *)

Fixpoint shift (f : formula) : formula :=
  match f with
  | FAtom p t =>
    FAtom p (shift_term t)
  | FNot f =>
    FNot (shift f)
  | FAnd f1 f2 =>
    FAnd (shift f1) (shift f2)
  | FOr f1 f2 =>
    FOr (shift f1) (shift f2)
  | f =>
    f
  end.

Lemma interpret_shift:
  forall cenv env f x,
  wff1 f ->
  interpret_formula cenv env (shift f) <->
  interpret_formula cenv (extend env x) f.
Proof.
  induction 1; simpl in *; try tauto.
  wff. rewrite interpret_shift_term; tauto.
Qed.

Lemma wf_shift:
  forall f,
  wff1 f ->
  wff (shift f).
Proof.
  induction f; intros; simpl in *; all; unpack; eauto using wf_shift_term.
Qed.

Lemma nnf_shift:
  forall f,
  nnf f ->
  nnf (shift f).
Proof.
  induction f; intros; simpl in *; nnf; eauto. constructor. auto.
Qed.

(* ------------------------------------------------------------------------- *)

(* Quantifier elimination for formulas, in the "sink" case. *)

Notation sink_interpret cenv env f :=
  (sink (fun x => interpret_formula cenv (extend env x) f)).

Notation sink_interpret_qe cenv env f := (
  interpret_formula cenv env (
    big_disjunction (fun i => subst (TConstant (CGround i)) (minusinf f))
      (interval (divlcm f))
  )
).

Lemma sink_qe:
  forall cenv env f u,
  all normal f ->
  sink_interpret cenv env f <-> sink_interpret_qe cenv (extend env u) f.
Proof.
  intros. rewrite sink_minusinf_equiv by auto.
  rewrite sink_equiv_big_or with (D := divlcm f); cycle 1.
  now apply divlcm_nonneg; auto.
  now eauto using interpret_minusinf_modulo_divlcm.
  rewrite interpret_big_disjunction. apply big_or_extens.
  intro. rewrite interpret_subst. reflexivity.
  now apply wf_minusinf; auto.
Qed.

(* ------------------------------------------------------------------------- *)
(* We now turn to the other case, where the set of solutions is bounded. *)

(* Constructing the B-set. *)

(* We slightly modify the boundary points returned by [bset] compared to the
   description given e.g. in Harrison's book: in order to have [0 <= j < D]
   instead of [1 <= j <= D] in [bset_correct] below, we have to add 1 to the
   boundary points we return here.

   Having intervals [0, n) instead of [1, n] makes the proofs easier...
 *)

Function bset (f : formula) : list term :=
  match f with
  | FNot (FAtom Eq (TSummand c 0 u)) =>
    (* [c] = 1 *)
    (* The atom is [0 <> x + u]. This changes from true to false when [x] is
       [-u+1]. *)
    [ add (neg u) (TConstant (CGround 1)) ]
  | FAtom Eq (TSummand c 0 u) =>
    (* [c] = 1 *)
    (* The atom is [0 = x + u]. This changes from true to false when [x] is
       [-u]. *)
    [ neg u ]
  | FAtom Lt (TSummand c 0 u) =>
    if Z.eqb c 1 then
      (* The atom is [0 < x + u]. This changes from true to false when [x] is
         [-u+1]. *)
      [ add (neg u) (TConstant (CGround 1)) ]
    else
      (* [c] = -1 *)
      []
  | FNot (FAtom _ _) =>
    []
  | FNot _ =>
    (* Impossible case since [f] is assumed to be in NNF *)
    []
  | FAnd f1 f2
  | FOr f1 f2 =>
    (* TEMPORARY eliminate duplicates, implement sets of terms *)
    bset f1 ++ bset f2
  | _ =>
    []
  end.

(* Terms in [bset f] do not contain the variable [x]. *)

Lemma wf1_bset:
  forall f,
  wff f ->
  Forall (wft 1) (bset f).
Proof.
  induction f; intros; wff; simpl in *; eauto using Forall_app.
  { predicate; term; wff; wft; simpl in *; try case_if;
      eauto using wf_neg, wf_add, wf_neg. }
  { destruct f; eauto. do 2 wff. predicate; term; eauto.
    wft. eauto using wf_add, wf_neg. }
Qed.

Lemma wf1_In_bset:
  forall f t,
  wff f ->
  In t (bset f) ->
  wft 1 t.
Proof.
  intros. applyin wf1_bset. rewrite Forall_forall in *. eauto.
Qed.

Lemma bset_correct:
  forall cenv env f D x u,
  all normal f ->
  nnf f ->
  0 < D ->
  all (dvdvx D) f ->
  interpret_formula cenv (extend env x) f ->
  ~ interpret_formula cenv (extend env (x - D)) f ->
  exists b j,
    x = interpret_term cenv (extend env u) b + j /\
    In b (bset f) /\
    0 <= j < D.
Proof.
  intros cenv env f.
  functional induction (bset f); intros; simpl in *;
    repeat all; unfold normal in *; unpack.
  { (* Atom [0 <> x + u] *)
    subst c. rewrite Z.mul_1_l in *. classical.
    exists (add (neg u) (TConstant (CGround 1))). (* b = -u+1 *)
    exists (D - 1). (* j = D-1 *)
    rewrite interpret_add, interpret_neg. simpl.
    erewrite extend_insensitive with (n2:=x); eauto.
    erewrite extend_insensitive with (n1:=x-D) (n2:=x) in *; eauto.
    eauto with zarith. }
  { (* Atom [0 = x + u] *)
    subst c. rewrite Z.mul_1_l in *.
    exists (neg u). (* b = -u *)
    exists 0. (* j = 0 *)
    erewrite extend_insensitive with (n2:=x); eauto using wf_neg, wf_add.
    rewrite interpret_neg. eauto with zarith. }
  { (* Atom [0 < x + u] *)
    rewrite Z.eqb_eq in *. subst c. rewrite Z.mul_1_l in *.
    exists (add (neg u) (TConstant (CGround 1))). (* b = -u+1 *)
    rewrite <-Z.le_ngt in *.
    erewrite extend_insensitive with (n1:=x-D) (n2:=x) in *; eauto.
    erewrite extend_insensitive with (n2:=x); eauto using wf_add, wf_neg.
    rewrite interpret_add, interpret_neg. simpl.
    set (u' := interpret_term cenv (extend env x) u) in *.
    assert (-u' + 1 <= x <= -u' + D) by lia.
    exists (x + u' - 1). (* j *) eauto with zarith. }
  { (* Atom [0 < - x + u] *)
    rewrite Z.eqb_neq in *. exfalso.
    erewrite extend_insensitive with (n1:=x-D) (n2:=x) in *; eauto.
    nia. }
  { exfalso. predicate; term; nnf; simpl in *; eauto; classical.
    - wft. erewrite extend_insensitive with (n1:=x-D) in *; eauto.
    - unpack. subst. rewrite Z.mul_1_l in *.
      erewrite extend_insensitive with (n1:=x-D) (n2:=x) in *; eauto.
      match goal with h: ~ (_ | _) |- _ => apply h end.
      apply Z.divide_add_cancel_r with (-D).
      auto with zarith.
      rewrite Z.add_assoc, Z.add_opp_l. auto.
    - wft. erewrite extend_insensitive with (n1:=x-D) (n2:=x) in *; eauto. }
  { nnf. exfalso. predicate; term; eauto. }
  { nnf. classical.
    match goal with h: _ \/ _ |- _ => destruct h end; [ spec IHl | spec IHl0 ];
      unpack; do 2 eexists; repeat split; eauto using in_or_app. }
  { nnf. classical. unpack.
    match goal with h: _ \/ _ |- _ => destruct h end; [ spec IHl | spec IHl0 ];
      unpack; do 2 eexists; repeat split; eauto using in_or_app. }
  { exfalso.
    destruct f; simpl in *; eauto; repeat all.
    - predicate; term; eauto; unfold normal in *; unpack; simpl in *.
      + wft. erewrite extend_insensitive with (n1:=x-D) (n2:=x) in *; eauto.
      + wft. erewrite extend_insensitive with (n1:=x-D) (n2:=x) in *; eauto.
      + match goal with h: ~ (_ | _) |- _ => apply h end.
        rewrite Z.mul_sub_distr_l, <-Z.add_sub_swap.
        apply Z.divide_sub_r; eauto with zarith.
        erewrite extend_insensitive with (n1:=x-D) (n2:=x); eauto.
      + wft. erewrite extend_insensitive with (n1:=x-D) (n2:=x) in *; eauto.
    - destruct f; eauto; predicate; term; eauto. }
Qed.

Lemma bset_correct_divlcm:
  forall cenv env f x u,
  all normal f ->
  nnf f ->
  interpret_formula cenv (extend env x) f ->
  ~ interpret_formula cenv (extend env (x - divlcm f)) f ->
  exists b j,
    x = interpret_term cenv (extend env u) b + j /\
    In b (bset f) /\
    0 <= j < divlcm f.
Proof.
  intros.
  apply bset_correct; auto.
  now apply divlcm_nonneg; auto.
  now apply all_dvdvx_divlcm; auto.
Qed.

(* ------------------------------------------------------------------------- *)

(* Quantifier elimination for formulas, in the "least element" case. *)

Notation least_element_interpret cenv env f :=
  (least_element (fun x => interpret_formula cenv (extend env x) f)).

Notation least_element_interpret_qe cenv env f := (
  interpret_formula cenv env (
    big_disjunction (fun i =>
      big_disjunction (fun b =>
        subst (add b (TConstant (CGround i))) f
      ) (bset f)
    ) (interval (divlcm f))
  )
).

Lemma least_element_qe_impl:
  forall cenv env f u,
  all normal f ->
  nnf f ->
  least_element_interpret cenv env f ->
  least_element_interpret_qe cenv (extend env u) f.
Proof.
  intros * ? ? [x [Hf Hnf]]. pose (D := divlcm f).
  specialize (Hnf (x - D)). spec1 Hnf.
  { enough (0 < D) by lia. eauto using divlcm_nonneg. }
  rewrite interpret_big_disjunction2.
  destruct (@bset_correct_divlcm cenv env f x u) as [b [j (Hx&?&?)]]; auto.
  apply big_or_prove with j; auto. rewrite In_interval; auto.
  apply big_or_prove with b; auto.
  rewrite interpret_subst by auto. rewrite interpret_add. simpl.
  rewrite Hx in Hf. apply Hf.
Qed.

(* We do not actually need to prove the equivalence for the final theorem to
   hold. For the reverse direction, we only need to prove this: *)

Lemma least_element_qe_rev:
  forall cenv env f u,
  all normal f ->
  nnf f ->
  least_element_interpret_qe cenv (extend env u) f ->
  exists x, interpret_formula cenv (extend env x) f.
Proof.
  intros ? ? ? ? ? ? Hqe.
  rewrite interpret_big_disjunction in Hqe.
  apply big_or_inv in Hqe. destruct Hqe as [j [? Hqe]].
  rewrite interpret_big_disjunction in Hqe.
  apply big_or_inv in Hqe. destruct Hqe as [b [? Hqe]].
  rewrite interpret_subst, interpret_add in Hqe; eauto using wf_unity.
Qed.

(* ------------------------------------------------------------------------- *)

(* The main function of the implementation. [cooper] eliminates one existential
   quantifier. *)

Definition cooper (f : formula) : formula :=
  let f := unity f in
  let f_inf := minusinf f in
  let bs := bset f in
  let js := interval (divlcm f) in
  let f_element := (fun j b => subst (add b (TConstant (CGround j))) f) in
  let stage := (fun j =>
    disjunction (subst (TConstant (CGround j)) f_inf)
                (big_disjunction (f_element j) bs)
  ) in
  shift (big_disjunction stage js).

(* [cooper f] is equivalent to [FExists f], and is quantifier-free. *)

Lemma interpret_cooper:
  forall cenv env f,
  wff f ->
  nnf f ->
  interpret_formula cenv env (cooper f) <->
  interpret_formula cenv env (FExists f).
Proof.
  intros.
  rewrite interpret_unity by auto. simpl.
  unfold cooper.
  (* 0 is a dummy value, associated in the environment to variable [x],
     which does not happen in the term. *)
  rewrite interpret_shift with (x:=0); cycle 1.
  { apply all_big_disjunction. intros. apply all_disjunction.
    - now apply wf1_subst, wf_minusinf, wf_unity.
    - apply all_big_disjunction. intros. apply wf1_subst.
      + apply wf_add; auto. eapply wf1_In_bset;[|eassumption]. now apply wf_unity.
      + now apply wf_unity. }

  rewrite interpret_big_disjunction.
  erewrite big_or_extens; cycle 1.
  { intro. match goal with |- _ <-> ?x => set (toto := x) end.
    rewrite interpret_disjunction.
    subst toto. apply iff_refl. }
  rewrite big_or_distr.

  rewrite exists_equiv_sink_or_least_element.
  assert (HH: forall (A B C D: Prop),
             A <-> C ->
             (D -> B) ->
             (B -> C \/ D) ->
             A \/ B <-> C \/ D) by tauto.
  apply HH; clear HH.

  { (* QE for the "sink" case. *)
    rewrite sink_qe. rewrite interpret_big_disjunction. reflexivity.
    apply normal_unity; auto. }

  { (* QE for the "least element" case (-> direction). *)
    rewrite <-interpret_big_disjunction.
    apply least_element_qe_impl. now apply normal_unity. now apply nnf_unity. }

  { (* QE for the "least element" case (<- direction). *)
    rewrite <-interpret_big_disjunction.
    rewrite <-exists_equiv_sink_or_least_element.
    apply least_element_qe_rev. now apply normal_unity. now apply nnf_unity. }
Qed.

(* [cooper] preserves well-formedness and the negative normal form *)

Lemma wf_cooper:
  forall f,
  wff f ->
  wff (cooper f).
Proof.
  (* In theory this proof could be a single [eauto using] invocation, but it
     doesn't work for some reason. *)
  intros. unfold cooper.
  apply wf_shift.
  apply all_big_disjunction. intros.
  apply all_disjunction. now eauto using wf1_subst, wf_minusinf, wf_unity.
  apply all_big_disjunction. intros.
  apply wf1_subst. now eauto using wf1_subst, wf_unity, wf_add, wf1_In_bset.
  now apply wf_unity.
Qed.

Lemma nnf_cooper:
  forall f,
  nnf f ->
  nnf (cooper f).
Proof.
  intros. unfold cooper.
  apply nnf_shift, nnf_big_disjunction. intros.
  apply nnf_disjunction.
  now apply nnf_subst, nnf_minusinf, nnf_unity.
  apply nnf_big_disjunction. intros.
  now apply nnf_subst, nnf_unity.
Qed.

(* ------------------------------------------------------------------------- *)
(* A simplification procedure for terms & formulas *)

Fixpoint simpl_term (t : term) : term :=
  match t with
  | TSummand k y u =>
    TSummand k y (simpl_term u)
  | TConstant c =>
    TConstant (simpl_constant c)
  end.

Definition boolf (b : bool) : formula :=
  match b with
  | true => FTrue
  | false => FFalse
  end.

Definition Zdivideb (x y : Z) : bool :=
  if Zdivide_dec x y then true else false.

Function simpl_atom (p : predicate) (t : term) : formula :=
  match t with
  | TConstant (CGround k) =>
    match p with
    | Eq => boolf (Z.eqb 0 k)
    | Lt => boolf (Z.ltb 0 k)
    | Dv z => boolf (Zdivideb z k)
    end
  | _ => FAtom p t
  end.

Fixpoint simpl_formula (f : formula) : formula :=
  match f with
  | FAtom p t =>
    simpl_atom p (simpl_term t)
  | FFalse =>
    FFalse
  | FTrue =>
    FTrue
  | FAnd f1 f2 =>
    conjunction (simpl_formula f1) (simpl_formula f2)
  | FOr f1 f2 =>
    disjunction (simpl_formula f1) (simpl_formula f2)
  | FNot f =>
    negation (simpl_formula f)
  | FExists f =>
    FExists (simpl_formula f)
  end.

Lemma interpret_simpl_term:
  forall cenv env t,
  interpret_term cenv env (simpl_term t) =
  interpret_term cenv env t.
Proof.
  induction t; intros; simpl in *; eauto using interpret_simpl_constant.
Qed.

Lemma wft_simpl_term:
  forall t n,
  wft n t ->
  wft n (simpl_term t).
Proof. induction t; intros; simpl in *; wft; eauto. Qed.

Lemma interpret_simpl_atom:
  forall cenv env p t,
  interpret_formula cenv env (simpl_atom p t) <->
  interpret_formula cenv env (FAtom p t).
Proof.
  intros.
  functional induction (simpl_atom p t); unfold boolf, Zdivideb in *;
    repeat case_if; simpl;
    rewrite ?Z.eqb_eq, ?Z.eqb_neq, ?Z.ltb_lt, ?Z.ltb_ge in *;
    try lia; try tauto; discriminate.
Qed.

Lemma wf_simpl_atom:
  forall p t,
  wft 0 t ->
  wfp p ->
  wff (simpl_atom p t).
Proof.
  intros.
  functional induction (simpl_atom p t); unfold boolf; cbn -[Z.eqb]; eauto;
    case_if; eauto.
Qed.

Lemma interpret_simpl_formula:
  forall cenv f env,
  interpret_formula cenv env (simpl_formula f) <->
  interpret_formula cenv env f.
Proof.
  induction f; intros; simpl in *; eauto; try tauto.
  - now rewrite interpret_simpl_atom; simpl; rewrite interpret_simpl_term.
  - rewrite interpret_conjunction, IHf1, IHf2. tauto.
  - rewrite interpret_disjunction, IHf1, IHf2. tauto.
  - rewrite interpret_negation, IHf. tauto.
  - apply exists_equivalence. eauto.
Qed.

Lemma wf_simpl_formula:
  forall f,
  wff f ->
  wff (simpl_formula f).
Proof.
  induction f; intros; simpl in *; wff; unpack;
    eauto using wft_simpl_term, wf_simpl_atom,
    wf_conjunction, wf_disjunction, wf_negation.
Qed.

(* ------------------------------------------------------------------------- *)

(* The main quantifier elimination algorithm: [qe] turns a formula into an
   equivalent quantifier-free formula. *)

Function map_disjuncts (transform : formula -> formula) (f : formula) :=
  match f with
  | FOr f1 f2 =>
    disjunction (transform f1) (transform f2)
  | FFalse =>
    FFalse
  | _ =>
    transform f
  end.

Fixpoint qe (f : formula) : formula :=
  match f with
  | FAtom _ _ | FFalse | FTrue =>
    f
  | FAnd f1 f2 =>
    conjunction (qe f1) (qe f2)
  | FOr f1 f2 =>
    disjunction (qe f1) (qe f2)
  | FNot f =>
    negation (qe f)
  | FExists f =>
    (* Innermost quantifiers are eliminated first. *)
    let f := qe f in
    (* Bring the body into NNF. *)
    let f := posnnf f in
    (* An existential quantifier can be pushed into a disjunction, so each
       toplevel disjunct can be treated independently. Over each disjunct, apply
       [cooper] to eliminate the existential quantifier. *)
    let f := map_disjuncts cooper f in
    simpl_formula f
  end.

(* ------------------------------------------------------------------------- *)

(* Like [all], but also under exists. *)
Inductive all_under_ex (P : predicate -> term -> Prop) : formula -> Prop :=
| all_under_ex_FAtom:
    forall p t,
    P p t ->
    all_under_ex P (FAtom p t)
| all_under_ex_FFalse:
    all_under_ex P FFalse
| all_under_ex_FTrue:
    all_under_ex P FTrue
| all_under_ex_FAnd:
    forall f1 f2,
    all_under_ex P f1 ->
    all_under_ex P f2 ->
    all_under_ex P (FAnd f1 f2)
| all_under_ex_FOr:
    forall f1 f2,
    all_under_ex P f1 ->
    all_under_ex P f2 ->
    all_under_ex P (FOr f1 f2)
| all_under_ex_FNot:
    forall f,
    all_under_ex P f ->
    all_under_ex P (FNot f)
| all_under_ex_FExists:
    forall f,
    all_under_ex P f ->
    all_under_ex P (FExists f).

Hint Constructors all_under_ex.

Notation wff_ue f := (all_under_ex (fun p t => wft 0 t /\ wfp p) f).

Ltac wff_ue :=
  match goal with h: wff_ue _ |- _ => depelim h end.

(* ------------------------------------------------------------------------- *)
(* [qe f] is equivalent to [f], and does not contain quantifiers. *)

Lemma all_map_disjuncts:
  forall transform f P,
  all P f ->
  (forall x, all P x -> all P (transform x)) ->
  all P (map_disjuncts transform f).
Proof.
  intros. destruct f; simpl; eauto.
  all. apply all_disjunction; eauto.
Qed.

(* This entails that [qe f] is quantifier-free. *)
Lemma wf_qe:
  forall f,
  wff_ue f ->
  wff (qe f).
Proof.
  induction f; intros; simpl in *; wff_ue;
    eauto using wf_conjunction, wf_disjunction, wf_negation.
  apply wf_simpl_formula, all_map_disjuncts; eauto using wf_posnnf, wf_cooper.
Qed.

(* [qe f] is equivalent to [f]. *)

Lemma interpret_qe:
  forall cenv f env,
  wff_ue f ->
  interpret_formula cenv env (qe f) <-> interpret_formula cenv env f.
Proof.
  induction f; intros; wff_ue; simpl in * |-; try tauto;
  [ repeat match goal with
      h: forall e:environment, _ |- _ => specialize (h env)
    end; simpl
  .. | ].
  rewrite interpret_conjunction; tauto.
  rewrite interpret_disjunction; tauto.
  rewrite interpret_negation; tauto.

  (* FExists case *)
  cbn [qe].
  assert (wff (posnnf (qe f))). now apply wf_posnnf, wf_qe.
  assert (nnf (posnnf (qe f))). now apply nnf_posnnf, qf_wff, wf_qe.
  transitivity (interpret_formula cenv env (cooper (posnnf (qe f)))); cycle 1.
  { rewrite interpret_cooper by auto. simpl. apply exists_equivalence.
    intro. rewrite interpret_posnnf. auto. }

  rewrite interpret_simpl_formula.
  functional induction (map_disjuncts cooper (posnnf (qe f))); try tauto;[].
  rewrite interpret_disjunction. wff. nnf.
  rewrite !interpret_cooper by auto.
  simpl. split.
  { intros HH. destruct HH as [[x ?]|[x ?]]; exists x; tauto. }
  { intros HH. destruct HH as [x [?|?]]; [left|right]; exists x; tauto. }
Qed.
