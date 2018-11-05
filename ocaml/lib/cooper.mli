module type Num = sig
  type num

  val zero : num
  val one : num
  val minus_one : num
  val ( + ) : num -> num -> num
  val ( * ) : num -> num -> num
  val ( / ) : num -> num -> num
  val ( > ) : num -> num -> bool
  val ( == ) : num -> num -> bool
  val abs : num -> num
  val gcd : num -> num -> num

  type anum
  module ANum : sig
    val zero : anum
    val one : anum
    val ( + ) : anum -> anum -> anum
    val ( * ) : anum -> anum -> anum
    val of_num : num -> anum
  end
end

module Int : sig
  type num = int

  val zero : num
  val one : num
  val minus_one : num
  val ( + ) : num -> num -> num
  val ( * ) : num -> num -> num
  val ( / ) : num -> num -> num
  val ( > ) : num -> num -> bool
  val ( == ) : num -> num -> bool
  val abs : num -> num
  val gcd : num -> num -> num

  type anum =
  | Num of int
  | Plus of anum * anum
  | Mul of anum * anum

  module ANum : sig
    val zero : anum
    val one : anum
    val ( + ) : anum -> anum -> anum
    val ( * ) : anum -> anum -> anum
    val of_num : num -> anum
  end
end

module Make (Num : Num) : sig
  type var = int

  type term =
    | TSummand of Num.num * var * term
    | TConstant of Num.anum

  type predicate =
    | Eq (* 0 = *)
    | Lt (* 0 < *)
    | Dv of Num.num (* c divides *)

  type formula =
    | FAtom of predicate * term
    | FFalse
    | FTrue
    | FAnd of formula * formula
    | FOr of formula * formula
    | FNot of formula
    | FExists of formula

  val lcm : Num.num -> Num.num -> Num.num
  val mul : Num.num -> term -> term
  val neg : term -> term
  val add : term -> term -> term
  val sub : term -> term -> term
  val formula_lcm : formula -> Num.num
  val adjust : Num.num -> formula -> formula
  val unity : formula -> formula
  val conjunction : formula -> formula -> formula
  val disjunction : formula -> formula -> formula
  val negation : formula -> formula
  val big_disjunction : formula list -> formula
  val map_disjuncts : (formula -> formula) -> formula -> formula
  val minusinf : formula -> formula
  val divlcm : formula -> Num.num
  val bset : formula -> term list
  val subst : term -> formula -> formula
  val interval : Num.num -> Num.num -> Num.num list
  val cooper : formula -> formula
  val nnf : formula -> formula
  val negnnf : formula -> formula
  val decide : formula -> formula
end
