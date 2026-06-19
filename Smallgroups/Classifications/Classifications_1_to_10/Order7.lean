/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PrimeOrderClassification
import Smallgroups.UsefulTheorems.Counting
import Mathlib.Tactic.NormNum.Prime

/-!
# Classification of groups of order 7

`7` is prime, so there is a unique group of order `7` up to isomorphism: the cyclic
group `ℤ/7`.

* `classification` — (1) exhaustiveness: every group of order `7` is isomorphic to `ℤ/7`.
* `distinct` — (2) distinctness: vacuous, as there is a single class.
* `isClassif` / `numIsoClasses_eq` — (3) counting: there is exactly one isomorphism class,
  proved from exhaustiveness and distinctness.
-/

namespace Smallgroups.Classifications.Order7

open Smallgroups.UsefulTheorems

variable {G : Type*} [Group G]

/-- `7` is prime. -/
theorem prime_p : Nat.Prime 7 := by norm_num

/-- The unique isomorphism class of groups of order `7`: the cyclic group `ℤ/7`. -/
abbrev Rep : Type := CyclicRep 7

/-- The representative has order `7`. -/
theorem card_Rep : Nat.card Rep = 7 := card_cyclicRep (by norm_num)

/-- **(1) Exhaustiveness.** Every group of order `7` is isomorphic to `ℤ/7`. -/
theorem classification (h : Nat.card G = 7) : Nonempty (G ≃* Rep) :=
  prime_classification prime_p h

/-- A group of order `7` is cyclic. -/
theorem isCyclic_of_card (h : Nat.card G = 7) : IsCyclic G :=
  prime_isCyclic prime_p h

/-- **(2) Distinctness.** With a single class the distinctness statement holds vacuously. -/
theorem distinct {i j : Fin 1} (hij : i ≠ j) :
    ¬ Nonempty (singleReps Rep i ≃* singleReps Rep j) :=
  singleReps_distinct Rep hij

/-- Any two groups of order `7` are isomorphic. -/
theorem unique {H : Type*} [Group H] (hG : Nat.card G = 7) (hH : Nat.card H = 7) :
    Nonempty (G ≃* H) :=
  prime_unique prime_p hG hH

/-- **(3) Counting.** The one-element list `[ℤ/7]` is a complete, non-redundant list of
representatives of the groups of order `7` — assembled from exhaustiveness (`classification`)
and the (vacuous) distinctness. -/
theorem isClassif : IsClassif 7 (rep1 Rep) :=
  isClassif_one _ card_Rep (fun _ _ hG => classification hG)

/-- **The number of isomorphism classes of groups of order `7` is exactly `1`:** any complete
list of pairwise non-isomorphic representatives has length `1`. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 7 rep) : k = 1 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order7
