/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order2PQ
import Smallgroups.UsefulTheorems.Counting
import Mathlib.Tactic.NormNum.Prime

/-!
# Classification of groups of order 30

`30 = 2 * 3 * 5` with `2 < 3 < 5` and `¬ (3 ∣ 5 - 1)`, so there are exactly **four** groups of
order `30` up to isomorphism (the `4`-class case of the order-`2pq` classification):

* Type I: `ℤ/30` (cyclic)
* Type II: `D₁₅` (dihedral of order `30`)
* Type III: `ℤ/5 × D₃`
* Type IV: `ℤ/3 × D₅`
-/

namespace Smallgroups.Classifications.Order30

open Smallgroups.UsefulTheorems

/-- `3` is prime. -/
theorem prime_p : Nat.Prime 3 := by norm_num

/-- `5` is prime. -/
theorem prime_q : Nat.Prime 5 := by norm_num

/-- **(1) Exhaustiveness.** Every group of order `30` is isomorphic to one of the four types
`ℤ/30`, `D₁₅`, `ℤ/5 × D₃`, `ℤ/3 × D₅`. -/
theorem classification {G : Type*} [Group G] (h : Nat.card G = 30) :
    Nonempty (G ≃* twoPQ_I 3 5) ∨ Nonempty (G ≃* twoPQ_II 3 5) ∨
    Nonempty (G ≃* twoPQ_III 3 5) ∨ Nonempty (G ≃* twoPQ_IV 3 5) := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  exact twoPQ_classification_4 3 5 prime_p prime_q (by norm_num) (by norm_num) (by decide) h

/-- **(2) Distinctness.** The four types are pairwise non-isomorphic. -/
theorem distinct :
    PairwiseNonMulEquiv (rep4 (twoPQ_I 3 5) (twoPQ_II 3 5) (twoPQ_III 3 5) (twoPQ_IV 3 5)) :=
  twoPQ_pairwiseDistinct_4 3 5 prime_p prime_q (by norm_num) (by norm_num)

/-- **(3) Counting.** The four types form a complete, non-redundant list of representatives of the
groups of order `30`. -/
theorem isClassif :
    IsClassif 30
      (rep4 (twoPQ_I 3 5) (twoPQ_II 3 5) (twoPQ_III 3 5) (twoPQ_IV 3 5)) :=
  twoPQ_isClassif_4 3 5 prime_p prime_q (by norm_num) (by norm_num) (by decide)

/-- **The number of isomorphism classes of groups of order `30` is exactly `4`.** -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 30 rep) : k = 4 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order30
