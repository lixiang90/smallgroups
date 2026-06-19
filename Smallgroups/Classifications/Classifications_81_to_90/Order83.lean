/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PrimeOrderClassification
import Smallgroups.UsefulTheorems.Counting
import Mathlib.Tactic.NormNum.Prime

/-!
# Classification of groups of order 83

`83` is prime, so there is a unique group of order `83` up to isomorphism: the cyclic
group `ℤ/83`.

* `classification` — (1) exhaustiveness: every group of order `83` is isomorphic to `ℤ/83`.
* `distinct` — (2) distinctness: vacuous, as there is a single class.
* `isClassif` / `numIsoClasses_eq` — (3) counting: there is exactly one isomorphism class,
  proved from exhaustiveness and distinctness.
-/

namespace Smallgroups.Classifications.Order83

open Smallgroups.UsefulTheorems

variable {G : Type*} [Group G]

/-- `83` is prime. -/
theorem prime_p : Nat.Prime 83 := by norm_num

/-- The unique isomorphism class of groups of order `83`: the cyclic group `ℤ/83`. -/
abbrev Rep : Type := CyclicRep 83

/-- The representative has order `83`. -/
theorem card_Rep : Nat.card Rep = 83 := card_cyclicRep (by norm_num)

/-- **(1) Exhaustiveness.** Every group of order `83` is isomorphic to `ℤ/83`. -/
theorem classification (h : Nat.card G = 83) : Nonempty (G ≃* Rep) :=
  prime_classification prime_p h

/-- A group of order `83` is cyclic. -/
theorem isCyclic_of_card (h : Nat.card G = 83) : IsCyclic G :=
  prime_isCyclic prime_p h

/-- **(2) Distinctness.** With a single class the distinctness statement holds vacuously. -/
theorem distinct {i j : Fin 1} (hij : i ≠ j) :
    ¬ Nonempty (singleReps Rep i ≃* singleReps Rep j) :=
  singleReps_distinct Rep hij

/-- Any two groups of order `83` are isomorphic. -/
theorem unique {H : Type*} [Group H] (hG : Nat.card G = 83) (hH : Nat.card H = 83) :
    Nonempty (G ≃* H) :=
  prime_unique prime_p hG hH

/-- **(3) Counting.** The one-element list `[ℤ/83]` is a complete, non-redundant list of
representatives of the groups of order `83` — assembled from exhaustiveness (`classification`)
and the (vacuous) distinctness. -/
theorem isClassif : IsClassif 83 (rep1 Rep) :=
  isClassif_one _ card_Rep (fun _ _ hG => classification hG)

/-- **The number of isomorphism classes of groups of order `83` is exactly `1`:** any complete
list of pairwise non-isomorphic representatives has length `1`. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 83 rep) : k = 1 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order83
