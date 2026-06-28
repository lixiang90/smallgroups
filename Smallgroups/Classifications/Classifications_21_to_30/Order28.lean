/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order4P
import Mathlib.Tactic.NormNum.Prime

/-!
# Classification of groups of order 28

`28 = 4 · 7`, so there are exactly **four** groups of order `28` up to isomorphism:
the cyclic group `ℤ/28`, `ℤ/2 × ℤ/14`, `ℤ/7 ⋊_{-1} ℤ/4`, and `ℤ/2 × D₁₄`.
This is the `p = 7` (p ≡ 3 mod 4) instance of the order-`4p` classification in
`Smallgroups.UsefulTheorems.Order4P`.
-/

namespace Smallgroups.Classifications.Order28

open Smallgroups.UsefulTheorems

/-- `ℤ/28`. -/
abbrev RA : Type := fourP_I 7
/-- `ℤ/2 × ℤ/14`. -/
abbrev RB : Type := fourP_II 7
/-- `ℤ/7 ⋊_{-1} ℤ/4`. -/
abbrev RC : Type := fourP_III 7
/-- `ℤ/2 × D₁₄`. -/
abbrev RD : Type := fourP_V 7

variable {G : Type*} [Group G]

/-- **(1) Exhaustiveness.** Every group of order `28` is isomorphic to one of the four groups. -/
theorem classification (h : Nat.card G = 28) :
    Nonempty (G ≃* RA) ∨ Nonempty (G ≃* RB) ∨ Nonempty (G ≃* RC) ∨
    Nonempty (G ≃* RD) := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  simpa [RA, RB, RC, RD, show (4 : ℕ) * 7 = 28 by norm_num] using
    fourP_classification_mod3 (by norm_num : Nat.Prime 7) (by omega)
      (by norm_num : 7 % 4 = 3) (h.trans (by norm_num))

private theorem classif_bundle : IsClassif 28 (rep4 RA RB RC RD) := by
  simpa [RA, RB, RC, RD, show (4 : ℕ) * 7 = 28 by norm_num] using
    fourP_isClassif_mod3 (by norm_num : Nat.Prime 7) (by omega)
      (by norm_num : 7 % 4 = 3)

/-- **(2) Distinctness.** The four groups are pairwise non-isomorphic. -/
theorem distinct : ∀ i j, Nonempty (rep4 RA RB RC RD i ≃* rep4 RA RB RC RD j) → i = j :=
  classif_bundle.distinct

/-- **(3) Counting.** The four groups are a complete, non-redundant list of
representatives of the groups of order `28`. -/
theorem isClassif : IsClassif 28 (rep4 RA RB RC RD) := classif_bundle

/-- **The number of isomorphism classes of groups of order `28` is exactly `4`.** -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 28 rep) : k = 4 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order28
