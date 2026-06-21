/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order2PSqElem
import Mathlib.Tactic.NormNum.Prime

/-!
# Classification of groups of order 98

`98 = 2 · 7²`, so there are exactly **five** groups of order `98` up to isomorphism: the cyclic
group `ℤ/98`, `ℤ/7 × ℤ/14`, the dihedral group `D₄₉`, `D₇ × ℤ/7`, and the generalized dihedral group
`(ℤ/7)² ⋊₋₁ ℤ/2`. This is the `p = 7` instance of the order-`2p²` classification in
`Smallgroups.UsefulTheorems.Order2PSqElem`.
-/

namespace Smallgroups.Classifications.Order98

open Smallgroups.UsefulTheorems

/-- `ℤ/98`. -/
abbrev RA : Type := R1 7
/-- `ℤ/7 × ℤ/14`. -/
abbrev RB : Type := R2 7
/-- The dihedral group `D₄₉`. -/
abbrev RC : Type := R3 7
/-- `D₇ × ℤ/7`. -/
abbrev RD : Type := R4 7
/-- The generalized dihedral group `(ℤ/7)² ⋊₋₁ ℤ/2`. -/
abbrev RE : Type := R5 7

variable {G : Type*} [Group G]

/-- **(1) Exhaustiveness.** Every group of order `98` is isomorphic to one of the five groups. -/
theorem classification (h : Nat.card G = 98) :
    Nonempty (G ≃* RA) ∨ Nonempty (G ≃* RB) ∨ Nonempty (G ≃* RC) ∨ Nonempty (G ≃* RD) ∨
      Nonempty (G ≃* RE) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  exact order2psq_classification (p := 7) (by norm_num) (h.trans (by norm_num))

/-- **(2) Distinctness & (3) Counting.** The five groups are a complete, non-redundant list of
representatives of the groups of order `98`. -/
theorem isClassif : IsClassif 98 (rep5 RA RB RC RD RE) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact order2psq_isClassif (p := 7) (by norm_num) (by norm_num)

/-- **The number of isomorphism classes of groups of order `98` is exactly `5`.** -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 98 rep) : k = 5 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order98
