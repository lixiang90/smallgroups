# smallgroups

Formalizing the classification of small finite groups in **Lean 4 + Mathlib**.

## Goal

For each small order `n`, a *full classification* of groups of order `n` consists of three
theorems:

1. **Exhaustiveness** — exhibit all possible isomorphism classes and prove every group of
   order `n` is one of them.
2. **Counting** — count the isomorphism classes.
3. **Distinctness** — prove the listed classes are pairwise non-isomorphic.

## Layout

* `Smallgroups/UsefulTheorems/` — reusable tools for classification.
  * `PrimeOrderCyclic.lean` — a finite group of prime order is cyclic
    (`Smallgroups.isCyclic_of_card_eq_prime`).
  * `PrimeOrderClassification.lean` — the shared engine for single-class (cyclic) orders:
    `CyclicRep n = ℤ/n`, `cyclicRep_classification`, `prime_classification`, `prime_unique`,
    and the `singleReps` distinctness scaffolding.
  * `PrimeSqClassification.lean` — the engine for orders `p²`: `prime_sq_mul_comm` (such groups
    are abelian), `prime_sq_classification` (every group of order `p²` is `ℤ/p²` or
    `ElemAbelianRep p = ℤ/p × ℤ/p`, proved via the `ℤ/p`-vector space structure of the non-cyclic
    case), and `prime_sq_distinct` (the two are non-isomorphic).
  * `Counting.lean` — turns exhaustiveness + distinctness into a *counting* statement. `IsClassif N
    rep` says `rep : Fin k → Type` is a complete, non-redundant list of representatives of the
    groups of order `N`; `IsClassif.card_unique` proves the length `k` is well defined, so
    exhibiting such a list of length `k` proves "there are exactly `k` isomorphism classes".
    `isClassif_one` / `isClassif_two` are the constructors used by the per-order files.
* `Smallgroups/Classifications/` — one file per order, grouped into decade subfolders
  `Classifications_1_to_10`, `Classifications_11_to_20`, …, `Classifications_91_to_100`.
  Each `OrderN.lean` proves the three classification theorems for order `N` in namespace
  `Smallgroups.Classifications.OrderN`:
  * `classification` — (1) exhaustiveness: every group of order `N` is isomorphic to a listed
    representative;
  * `distinct` — (2) distinctness: the representatives are pairwise non-isomorphic;
  * `isClassif` / `numIsoClasses_eq` — (3) counting: the count of isomorphism classes, *proved*
    from (1) and (2) via the `Counting.lean` framework (`numIsoClasses_eq` shows any complete
    non-redundant representative list has the stated length).

  Done so far: order `1` (trivial group); every prime order `≤ 100` (`2, 3, 5, 7, …, 97`), each
  the single class `ℤ/N`; and the prime-square orders `4, 9, 25, 49`, each with two classes
  `ℤ/N` and `ℤ/p × ℤ/p`.

## Building

```sh
lake exe cache get   # fetch the prebuilt Mathlib cache
lake build
```
