/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order4P
import Mathlib.Tactic.NormNum.Prime

/-!
# Classification of groups of order 44

`44 = 4 · 11`, so there are exactly **four** groups of order `44` up to isomorphism:
the cyclic group `ℤ/44`, `ℤ/2 × ℤ/22`, `ℤ/11 ⋊_{-1} ℤ/4`, and `ℤ/2 × D₂₂`.
This is the `p = 11` (p ≡ 3 mod 4) instance of the order-`4p` classification in
`Smallgroups.UsefulTheorems.Order4P`.
-/

namespace Smallgroups.Classifications.Order44

open Smallgroups.UsefulTheorems

/-- `ℤ/44`. -/
abbrev RA : Type := fourP_I 11
/-- `ℤ/2 × ℤ/22`. -/
abbrev RB : Type := fourP_II 11
/-- `ℤ/11 ⋊_{-1} ℤ/4`. -/
abbrev RC : Type := fourP_III 11
/-- `ℤ/2 × D₂₂`. -/
abbrev RD : Type := fourP_V 11

variable {G : Type*} [Group G]

/-- **(1) Exhaustiveness.** Every group of order `44` is isomorphic to one of the four groups. -/
theorem classification (h : Nat.card G = 44) :
    Nonempty (G ≃* RA) ∨ Nonempty (G ≃* RB) ∨ Nonempty (G ≃* RC) ∨
    Nonempty (G ≃* RD) := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  simpa [RA, RB, RC, RD, show (4 : ℕ) * 11 = 44 by norm_num] using
    fourP_classification_mod3 (by norm_num : Nat.Prime 11) (by omega)
      (by norm_num : 11 % 4 = 3) (h.trans (by norm_num))

private theorem classif_bundle : IsClassif 44 (rep4 RA RB RC RD) := by
  simpa [RA, RB, RC, RD, show (4 : ℕ) * 11 = 44 by norm_num] using
    fourP_isClassif_mod3 (by norm_num : Nat.Prime 11) (by omega)
      (by norm_num : 11 % 4 = 3)

/-- **(2) Distinctness.** The four groups are pairwise non-isomorphic. -/
theorem distinct : ∀ i j, Nonempty (rep4 RA RB RC RD i ≃* rep4 RA RB RC RD j) → i = j :=
  classif_bundle.distinct

/-- **(3) Counting.** The four groups are a complete, non-redundant list of
representatives of the groups of order `44`. -/
theorem isClassif : IsClassif 44 (rep4 RA RB RC RD) := classif_bundle

/-- **The number of isomorphism classes of groups of order `44` is exactly `4`.** -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 44 rep) : k = 4 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order44
