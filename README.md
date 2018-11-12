MiniCooper
-----------

A formally verified implementation of Cooper's quantifier elimination procedure,
as a reflexive tactic for Coq.

### What does it do?

The library provides a `qe` tactic that turns a first-order formula on linear
arithmetic into an equivalent *quantifier-free* formula.

```coq
Goal forall a b,
  (exists x, 2 * a - 3 * b + 1 <= x /\ (x < a + b \/ x < 2 * a)).

  (* Abstract constants are allowed *)
  intros a b.

  (* eliminate x *)
  qe.

(*
  a, b : Z
  ============================
  0 < 4 * b - a - 1 \/ 0 < 3 * b - 1
*)
```

### Usage

Install the library using opam:
```
opam install coq-minicooper
```

Then, import it using:
```
Require Import MiniCooper.Tactic.
```

### Limitations / possible improvements

- *Axioms:* the library currently relies on the excluded middle. It should be
  possible to get rid of this.

- The tactic currently only works on expressions in `Z`. It would be easy to
  make it work on `nat` or `N`, either by implementing support directly in the
  library, or maybe by extending `zify` to handle quantifiers.

- Support for more operators (e.g. `Z.max`, `Z.min`) is easy to add by
  translating them at the surface syntax level. It would be interesting to
  consider implementing a mechanism to allow extending the tactic from the
  outside in a generic way.

- Quantifier eliminations can produce goal containing divisibility atoms `(k |
  t)` (with `k` an explicit constant). It should be doable to extend `zify` to
  eliminate them.

- On the following "intuitively easy" goal, `qe` produces a formula that makes
  `lia` explode:

  ```coq
  Goal forall a b c,
    exists x y z,
    0 <= x /\ 0 <= y /\ 0 <= z /\
    a <= x /\ b <= y /\ c <= z.
  Proof.
    intros *. qe.
    Time lia. (* 6s *)
  Qed.
  ```
