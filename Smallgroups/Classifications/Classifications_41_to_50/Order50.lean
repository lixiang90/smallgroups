/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order2PSqElem
import Mathlib.Tactic.NormNum.Prime

/-!
# Classification of groups of order 50

`50 = 2 · 5²`, so there are exactly **five** groups of order `50` up to isomorphism: the cyclic
group `ℤ/50`, `ℤ/5 × ℤ/10`, the dihedral group `D₂₅`, `D₅ × ℤ/5`, and the generalized dihedral group
`(ℤ/5)² ⋊₋₁ ℤ/2`. This is the `p = 5` instance of the order-`2p²` classification in
`Smallgroups.UsefulTheorems.Order2PSqElem`.
-/

namespace Smallgroups.Classifications.Order50

open Smallgroups.UsefulTheorems

/-- `ℤ/50`. -/
abbrev RA : Type := R1 5
/-- `ℤ/5 × ℤ/10`. -/
abbrev RB : Type := R2 5
/-- The dihedral group `D₂₅`. -/
abbrev RC : Type := R3 5
/-- `D₅ × ℤ/5`. -/
abbrev RD : Type := R4 5
/-- The generalized dihedral group `(ℤ/5)² ⋊₋₁ ℤ/2`. -/
abbrev RE : Type := R5 5

variable {G : Type*} [Group G]

/-- **(1) Exhaustiveness.** Every group of order `50` is isomorphic to one of the five groups. -/
theorem classification (h : Nat.card G = 50) :
    Nonempty (G ≃* RA) ∨ Nonempty (G ≃* RB) ∨ Nonempty (G ≃* RC) ∨ Nonempty (G ≃* RD) ∨
      Nonempty (G ≃* RE) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  exact order2psq_classification (p := 5) (by norm_num) (h.trans (by norm_num))

private theorem classif_bundle : IsClassif 50 (rep5 RA RB RC RD RE) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact order2psq_isClassif (p := 5) (by norm_num) (by norm_num)

/-- **(2) Distinctness.** The five groups are pairwise non-isomorphic. -/
theorem distinct : ∀ i j, Nonempty (rep5 RA RB RC RD RE i ≃* rep5 RA RB RC RD RE j) → i = j :=
  classif_bundle.distinct

/-- **(3) Counting.** The five groups are a complete, non-redundant list of
representatives of the groups of order `50`. -/
theorem isClassif : IsClassif 50 (rep5 RA RB RC RD RE) := classif_bundle

/-- **The number of isomorphism classes of groups of order `50` is exactly `5`.** -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 50 rep) : k = 5 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order50
