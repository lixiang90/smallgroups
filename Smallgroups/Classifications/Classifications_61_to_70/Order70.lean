/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order2PQ
import Smallgroups.UsefulTheorems.Counting
import Mathlib.Tactic.NormNum.Prime

/-!
# Classification of groups of order 70

`70 = 2 * 5 * 7` with `2 < 5 < 7` and `¬ (5 ∣ 7 - 1)`, so there are exactly **four** groups of
order `70` up to isomorphism (the `4`-class case of the order-`2pq` classification):

* Type I: `ℤ/70` (cyclic)
* Type II: `D₃₅` (dihedral of order `70`)
* Type III: `ℤ/7 × D₅`
* Type IV: `ℤ/5 × D₇`
-/

namespace Smallgroups.Classifications.Order70

open Smallgroups.UsefulTheorems

/-- `5` is prime. -/
theorem prime_p : Nat.Prime 5 := by norm_num

/-- `7` is prime. -/
theorem prime_q : Nat.Prime 7 := by norm_num

/-- **(1) Exhaustiveness.** Every group of order `70` is isomorphic to one of the four types
`ℤ/70`, `D₃₅`, `ℤ/7 × D₅`, `ℤ/5 × D₇`. -/
theorem classification {G : Type*} [Group G] (h : Nat.card G = 70) :
    Nonempty (G ≃* twoPQ_I 5 7) ∨ Nonempty (G ≃* twoPQ_II 5 7) ∨
    Nonempty (G ≃* twoPQ_III 5 7) ∨ Nonempty (G ≃* twoPQ_IV 5 7) := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  exact twoPQ_classification_4 5 7 prime_p prime_q (by norm_num) (by norm_num) (by decide) h

/-- **(2) Distinctness.** The four types are pairwise non-isomorphic. -/
theorem distinct :
    PairwiseNonMulEquiv (rep4 (twoPQ_I 5 7) (twoPQ_II 5 7) (twoPQ_III 5 7) (twoPQ_IV 5 7)) :=
  twoPQ_pairwiseDistinct_4 5 7 prime_p prime_q (by norm_num) (by norm_num)

/-- **(3) Counting.** The four types form a complete, non-redundant list of representatives of the
groups of order `70`. -/
theorem isClassif :
    IsClassif 70
      (rep4 (twoPQ_I 5 7) (twoPQ_II 5 7) (twoPQ_III 5 7) (twoPQ_IV 5 7)) :=
  twoPQ_isClassif_4 5 7 prime_p prime_q (by norm_num) (by norm_num) (by decide)

/-- **The number of isomorphism classes of groups of order `70` is exactly `4`.** -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 70 rep) : k = 4 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order70
