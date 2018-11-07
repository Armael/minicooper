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

module Int (* : Num with type num = int *) = struct
  type num = int
  let zero = 0
  let one = 1
  let minus_one = -1
  let ( + ) = ( + )
  let ( * ) = ( * )
  let ( / ) = ( / )
  let ( > ) = ( > )
  let ( == ) = ( = )
  let abs = abs
  let rec gcd a b = if b = 0 then a else gcd b (a mod b)

  type anum =
    | Num of int
    | Plus of anum * anum
    | Mul of anum * anum

  module ANum = struct
    let of_num x = Num x
    let ( + ) x y =
      if x = Num 0 then y
      else if y = Num 0 then x
      else Plus (x, y)
    let ( * ) x y =
      if x = Num 1 then y
      else if y = Num 1 then x
      else Mul (x, y)
    let zero = Num 0
    let one = Num 1
  end
end

module Make (Num : Num) = struct

  open Num

  (* Define LCM in terms of GCD. *)

  (* By convention, a LCM is nonnegative, just like a GCD. *)

  let lcm n1 n2 = abs (n1 * n2) / gcd n1 n2

  (* Variables are encoded as de Bruijn indices. *)

  type var =
    int

  let (=) (x1 : var) x2 = (x1 = x2) (* to avoid mis-use of generic equality *) (* TEMPORARY *)

  (* A term in canonical form is a sum of terms of the form [kx],
     where [k] is a (nonzero) constant and [x] is a variable, and of a
     final constant. The summands are sorted by increasing de Bruijn
     indices. *)

  (* TEMPORARY when creating terms (substitutiton), should use GCD of coefficients
     to simplify term/atom *)

  type term =
    | TSummand of num * var * term
    | TConstant of anum

  (* Multiplication of a canonical term by a constant. *)

  let rec mul n = function
    | TSummand (k, x, t) ->
	    TSummand (n * k, x, mul n t)
    | TConstant k ->
	    TConstant ANum.(of_num n * k)

  let mul n t =
    if n == zero then
      TConstant ANum.zero
    else
      mul n t

  (* Negation of a canonical term. *)

  let neg t =
    mul minus_one t

  (* Addition of two canonical terms. *)

  (* This is analogous to merging two sorted lists. *)

  let rec add t1 t2 =
    match t1, t2 with
    | TSummand (k1, x1, u1), TSummand (k2, x2, u2) ->
	    if x1 = x2 then
	      let k = k1 + k2 in
	      if k == zero then
	        add u1 u2
	      else
	        TSummand (k, x1, add u1 u2)
	    else if x1 < x2 then
	      TSummand (k1, x1, add u1 t2)
	    else
	      TSummand (k2, x2, add t1 u2)
    | TSummand (k1, x1, u1), TConstant _ ->
	    TSummand (k1, x1, add u1 t2)
    | TConstant _, TSummand (k2, x2, u2) ->
	    TSummand (k2, x2, add t1 u2)
    | TConstant k1, TConstant k2 ->
	    TConstant ANum.(k1 + k2)

  (* Subtraction of two canonical terms. *)

  let sub t1 t2 =
    add t1 (neg t2)

  (* An atomic formula is one of: [0 = t]; [0 < t]; [c divides t], where [c]
     is greater than 1. The rest is first-order logic. Variables range over
     Z. *)

  type predicate =
    | Eq (* 0 = *)
    | Lt (* 0 < *)
    | Dv of num (* c divides *)

  type formula =
    | FAtom of predicate * term
    | FFalse
    | FTrue
    | FAnd of formula * formula
    | FOr of formula * formula
    | FNot of formula
    | FExists of formula

  (* Least common multiple of the coefficients of [x] in a quantifier-free
     formula. We take [x] to be the variable with de Bruijn index [0], so
     [x] always appear in front of a canonical term, if it appears at
     all. *)

  let rec formula_lcm = function
    | FAtom (_, TSummand (c, 0, _)) ->
	    abs c (* by convention, a LCM is nonnegative *)
    | FAtom (_, TSummand _)
    | FAtom (_, TConstant _)
    | FFalse
    | FTrue ->
	    one
    | FAnd (f1, f2)
    | FOr (f1, f2) ->
	    lcm (formula_lcm f1) (formula_lcm f2)
    | FNot f ->
	    formula_lcm f
    | FExists _ ->
	    assert false (* formula must be quantifier-free *)

  (* Adjusting the coefficients of [x] in a quantifier-free formula.  This
     follows the structure of the above code, and at each atom, multiplies
     the coefficient of [x] so as to reach the least common multiple [l] --
     or its opposite. Then, the coefficient of [x] is immediately normalized
     down to [1] or [-1], as we perform a change of variables and write [x]
     for [lx]. *)

  let rec adjust l = function
    | FAtom (Eq, TSummand (c, 0, u)) ->

	    (* Compute by how much we must multiply. *)
	    let m = l / c in
	    (* The coefficient of [x] becomes [l], but is renormalized to [1];
	       the rest of the term is multiplied by [m]. *)
	    FAtom (Eq, TSummand (one, 0, mul m u))

    | FAtom (Lt, TSummand (c, 0, u)) ->

	    (* Compute by how much we must multiply. *)
	    let m = l / c in
	    (* Make sure that this is a positive factor, as we can't reverse
	       the predicate [Lt]. *)
	    let am = abs m in
	    (* Thus, the coefficient of [x] will be renormalized to either
	       [1] or [-1]. *)
	    let coeffx = m / am in
	    (* The coefficient of [x] is renormalized to [coeffx];
	       the rest of the term is multiplied by [am]. *)
	    FAtom (Lt, TSummand (coeffx, 0, mul am u))

    | FAtom (Dv d, TSummand (c, 0, u)) ->

	    (* Compute by how much we must multiply. *)
	    let m = l / c in
	    (* The coefficient of [x] becomes [l], but is renormalized to [1];
	       the rest of the term is multiplied by [m]. The divisor [d] is
	       multiplied by [m], but we are careful to keep it positive. *)
	    FAtom (Dv (abs m * d), TSummand (one, 0, mul m u))

    | FAtom (_, TSummand _)
    | FAtom (_, TConstant _) as f ->
	    f
    | FFalse ->
	    FFalse
    | FTrue ->
	    FTrue
    | FAnd (f1, f2) ->
	    FAnd (adjust l f1, adjust l f2)
    | FOr (f1, f2) ->
	    FOr (adjust l f1, adjust l f2)
    | FNot f ->
	    FNot (adjust l f)
    | FExists _ ->
	    assert false (* formula must be quantifier-free *)

  (* Making sure that all coefficients of [x] in a quantifier-free formula
     are [1] or [-1]. *)

  let unity (f : formula) : formula =

    (* Compute the least common multiple of all coefficients of [x]. *)

    let l = formula_lcm f in

    (* Adjust all coefficients of [x] in the formula to be [1] or [-1].
	     This represents a change of variable: the new [x] stands for the
	     old [lx]. *)

    let f = adjust l f in

    (* For the change of variable to make sense, we must add a constraint
	     that [l] divides the new [x]. Of course, this is required only if
	     [l] is not [1]. *)

    if l == one then
	    f
    else
	    FAnd (
	      f,
	      FAtom (Dv l, TSummand (one, 0, TConstant ANum.zero))
	    )

  (* Smart constructors for conjunction, disjunction, and negation. *)

  let conjunction f1 f2 =
    match f1, f2 with
    | FFalse, _
    | _, FFalse ->
	    FFalse
    | FTrue, f
    | f, FTrue ->
	    f
    | _, _ ->
	    FAnd (f1, f2)

  let disjunction f1 f2 =
    match f1, f2 with
    | FTrue, _
    | _, FTrue ->
	    FTrue
    | FFalse, f
    | f, FFalse ->
	    f
    | _, _ ->
	    FOr (f1, f2)

  let negation = function
    | FTrue ->
	    FFalse
    | FFalse ->
	    FTrue
    | FNot f ->
	    f
    | f ->
	    FNot f

  let big_disjunction fs =
    List.fold_left disjunction FFalse fs

  let map_disjuncts (transform : formula -> formula) = function
    | FOr (f1, f2) ->
	    disjunction (transform f1) (transform f2)
    | FFalse ->
	    FFalse
    | f ->
	    transform f

  (* Computing the ``minus infinity'' version of a formula P. This new
     formula holds if and only if the original formula admits arbitrarily
     small solutions for [x]. As before, we take [x] to be the variable with
     de Bruijn index 0.*)

  let rec minusinf = function
    | FAtom (Eq, TSummand (c, 0, _)) ->
	    assert (c == one);

	    (* We have an equality on [x]. This can't be satisfied by arbitrarily
	       small values of [x]. *)
	    FFalse

    | FAtom (Lt, TSummand (c, 0, _)) ->
	    assert (c == one || c == minus_one);

	    (* We have an inequality on [x]. This is satisfied by arbitrarily
	       small values of [x] if and only if the coefficient [c] is
	       negative. *)

	    if c == one then FFalse else FTrue

    | FAtom (Eq, _)
    | FAtom (Lt, _)
    | FAtom (Dv _, _) as f ->

	    (* Division atoms are insensitive to translation, so they are
	       retained. Atoms that do not mention [x] at all are retained as
	       well. *)

	    f

    | FFalse ->
	    FFalse
    | FTrue ->
	    FTrue
    | FAnd (f1, f2) ->
	    conjunction (minusinf f1) (minusinf f2)
    | FOr (f1, f2) ->
	    disjunction (minusinf f1) (minusinf f2)
    | FNot f ->
	    negation (minusinf f)
    | FExists _ ->
	    assert false (* formula must be quantifier-free *)

  (* Least common multiple of the division atoms that involve [x]. *)

  let rec divlcm = function
    | FAtom (Dv d, TSummand (c, 0, _)) ->
	    assert (c == one);
	    assert (d == abs d); (* [d] is positive *)
	    d
    | FAnd (f1, f2)
    | FOr (f1, f2) ->
	    lcm (divlcm f1) (divlcm f2)
    | FNot f ->
	    divlcm f
    | _ ->
	    one

  (* Constructing the B-set. *)

  let rec bset = function
    | FNot (FAtom (Eq, TSummand (c, 0, u))) ->
	    assert (c == one);
	    (* The atom is [0 <> x + u]. This changes from true to false when
	       [x] is [-u]. *)
	    [ neg u ]
    | FAtom (Eq, TSummand (c, 0, u)) ->
	    assert (c == one);
	    (* The atom is [0 = x + u]. This changes from true to false when
	       [x] is [-u-1]. *)
	    [ neg (add u (TConstant ANum.one)) ]
    | FAtom (Lt, TSummand (c, 0, u)) ->
	    assert (c == one); (* BUG ! [c] could also be -1 (see the Coq implem) *)
	    (* The atom is [0 < x + u]. This changes from true to false when
	       [x] is [-u]. *)
	    [ neg u ]
    | FNot f ->
	    (* We are probably assuming the formula to be in NNF, so [f] here
	       is an atom. Clear this up. *)
	    bset f
    | FAnd (f1, f2)
    | FOr (f1, f2) ->
	    bset f1 @ bset f2 (* TEMPORARY eliminate duplicates, implement sets of terms *)
    | _ ->
	    []

  (* Substitution of a term [t] for a variable [x] within a formula. *)

  let rec subst t = function
    | FAtom (predicate, TSummand (c, 0, u)) ->
	    FAtom (predicate, add (mul c t) u)
	  (* TEMPORARY should check whether atom becomes trivial / can be simplified *)
    | FNot f ->
	    FNot (subst t f)
    | FAnd (f1, f2) ->
	    FAnd (subst t f1, subst t f2)
    | FOr (f1, f2) ->
	    FOr (subst t f1, subst t f2)
    | f ->
	    f

  (* TEMPORARY understand where [x] is eliminated and unshift the remaining variables *)
  (* TEMPORARY if all variables were represented in terms, with possibly null coefficients,
     then there would be no need to keep track of variable numbers, and unshifting would be automatic *)

  (* The interval of [m] to [n], inclusive. *)

  let rec interval m n =
    if m > n then [] else m :: interval (m + one) n

  (* Quantifier elimination. The formula [f] is assumed to be the body
     of an existential quantifier, which we wish to eliminate. The
     formula is assumed to be in NNF. *)

  let cooper f =
    let f = unity f in
    let f_inf = minusinf f
    and bs = bset f
    and js = interval one (divlcm f) in
    let f_element j b =
	    subst (add b (TConstant j)) f
    in
    let stage j =
      let j = ANum.of_num j in
	    big_disjunction (subst (TConstant j) f_inf :: List.map (f_element j) bs)
    in
    big_disjunction (List.map stage js)

  (* TEMPORARY remains to do:
     evaluation of constant atoms (smart constructor for atoms?)
     think about adding iff, or a more general form of sub-formula sharing *)

  (* Bringing a quantifier-free formula into NNF form. *)

  let rec nnf = function
    | FAtom _
    | FTrue
    | FFalse as f ->
	    f
    | FNot f ->
	    negnnf f
    | FAnd (f1, f2) ->
	    FAnd (nnf f1, nnf f2)
    | FOr (f1, f2) ->
	    FOr (nnf f1, nnf f2)
    | FExists _ ->
	    assert false

  and negnnf = function
    | FAtom (Lt, t) ->
	    (* Negated inequalities are not permitted by our assumptions.
	       Reverse them. The atom [~(0 < t)] can be transformed into
	       [0 < 1 - t]. *)
	    FAtom (Lt, sub (TConstant ANum.one) t)
    | FAtom _ as f ->
	    FNot f
    | FTrue ->
	    FFalse
    | FFalse ->
	    FTrue
    | FNot f ->
	    nnf f
    | FAnd (f1, f2) ->
	    FOr (negnnf f1, negnnf f2)
    | FOr (f1, f2) ->
	    FAnd (negnnf f1, negnnf f2)
    | FExists _ ->
	    assert false

  (* [decide] turns a formula into an equivalent quantifier-free formula. If
     the initial formula is closed, the result formula is either [FTrue] or
     [FFalse]. *)

  let rec decide f =
    match f with
    | FAtom _
    | FFalse
    | FTrue ->
	    f
    | FAnd (f1, f2) ->
	    conjunction (decide f1) (decide f2)
    | FOr (f1, f2) ->
	    disjunction (decide f1) (decide f2)
    | FNot f ->
	    negation (decide f)
    | FExists f ->
	    (* Simplify the body. Innermost quantifiers are eliminated first. *)
	    let f = decide f in
	    (* Bring the body into NNF form. *)
	    let f = nnf f in
	    (* An existential quantifier can be pushed into a disjunction, so
	       each toplevel disjunct can be treated independently. Over each
	       disjunct, apply [cooper] to eliminate the existential quantifier. *)
	    map_disjuncts cooper f

end
