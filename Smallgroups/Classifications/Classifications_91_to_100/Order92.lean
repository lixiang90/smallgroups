/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order4P
import Mathlib.Tactic.NormNum.Prime

/-!
# Classification of groups of order 92

`92 = 4 · 23`, so there are exactly **four** groups of order `92` up to isomorphism:
the cyclic group `ℤ/92`, `ℤ/2 × ℤ/46`, `ℤ/23 ⋊_{-1} ℤ/4`, and `ℤ/2 × D₄₆`.
This is the `p = 23` (p ≡ 3 mod 4) instance of the order-`4p` classification in
`Smallgroups.UsefulTheorems.Order4P`.
-/

namespace Smallgroups.Classifications.Order92

open Smallgroups.UsefulTheorems

/-- `ℤ/92`. -/
abbrev RA : Type := fourP_I 23
/-- `ℤ/2 × ℤ/46`. -/
abbrev RB : Type := fourP_II 23
/-- `ℤ/23 ⋊_{-1} ℤ/4`. -/
abbrev RC : Type := fourP_III 23
/-- `ℤ/2 × D₄₆`. -/
abbrev RD : Type := fourP_V 23

variable {G : Type*} [Group G]

/-- **(1) Exhaustiveness.** Every group of order `92` is isomorphic to one of the four groups. -/
theorem classification (h : Nat.card G = 92) :
    Nonempty (G ≃* RA) ∨ Nonempty (G ≃* RB) ∨ Nonempty (G ≃* RC) ∨
    Nonempty (G ≃* RD) := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  simpa [RA, RB, RC, RD, show (4 : ℕ) * 23 = 92 by norm_num] using
    fourP_classification_mod3 (by norm_num : Nat.Prime 23) (by omega)
      (by norm_num : 23 % 4 = 3) (h.trans (by norm_num))

/-- **(2) Distinctness & (3) Counting.** The four groups are a complete, non-redundant list of
representatives of the groups of order `92`. -/
theorem isClassif : IsClassif 92 (rep4 RA RB RC RD) := by
  simpa [RA, RB, RC, RD, show (4 : ℕ) * 23 = 92 by norm_num] using
    fourP_isClassif_mod3 (by norm_num : Nat.Prime 23) (by omega)
      (by norm_num : 23 % 4 = 3)

/-- **The number of isomorphism classes of groups of order `92` is exactly `4`.** -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 92 rep) : k = 4 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order92
