/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PrimePairCyclic
import Smallgroups.UsefulTheorems.Counting
import Mathlib.Tactic.NormNum.Prime

/-!
# Classification of groups of order 35

`35 = 7 * 5` with 7 > 5 distinct primes and `5 ∤ 7 - 1`, so every group of
order `35` is cyclic: there is a unique isomorphism class, `ℤ/35`.

* `classification` — (1) exhaustiveness: every group of order `35` is isomorphic to `ℤ/35`.
* `distinct` — (2) distinctness: vacuous, as there is a single class.
* `isClassif` / `numIsoClasses_eq` — (3) counting: there is exactly one isomorphism class.
-/

namespace Smallgroups.Classifications.Order35

open Smallgroups.UsefulTheorems

variable {G : Type*} [Group G]

/-- `7` is prime. -/
theorem prime_p : Nat.Prime 7 := by norm_num

/-- `5` is prime. -/
theorem prime_q : Nat.Prime 5 := by norm_num

/-- The unique isomorphism class of groups of order `35`: the cyclic group `ℤ/35`. -/
abbrev Rep : Type := CyclicRep 35

/-- The representative has order `35`. -/
theorem card_Rep : Nat.card Rep = 35 := card_cyclicRep (by norm_num)

/-- A group of order `35` is cyclic (Sylow 7 and Sylow 5 are both normal since
`5 ∤ 7 - 1`). -/
theorem isCyclic_of_card (h : Nat.card G = 35) : IsCyclic G :=
  isCyclic_of_card_eq_prime_mul prime_p prime_q (by norm_num) (by norm_num) (h.trans (by norm_num))

/-- **(1) Exhaustiveness.** Every group of order `35` is isomorphic to `ℤ/35`. -/
theorem classification (h : Nat.card G = 35) : Nonempty (G ≃* Rep) := by
  haveI := isCyclic_of_card h
  exact cyclicRep_classification (by norm_num) h

/-- **(2) Distinctness.** With a single class the distinctness statement holds vacuously. -/
theorem distinct {i j : Fin 1} (hij : i ≠ j) :
    ¬ Nonempty (singleReps Rep i ≃* singleReps Rep j) :=
  singleReps_distinct Rep hij

/-- **(3) Counting.** The one-element list `[ℤ/35]` is a complete, non-redundant list of
representatives of the groups of order `35` — assembled from exhaustiveness (`classification`)
and the (vacuous) distinctness. -/
theorem isClassif : IsClassif 35 (rep1 Rep) :=
  isClassif_one _ card_Rep (fun _ _ hG => classification hG)

/-- **The number of isomorphism classes of groups of order `35` is exactly `1`:** any complete
list of pairwise non-isomorphic representatives has length `1`. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 35 rep) : k = 1 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order35
