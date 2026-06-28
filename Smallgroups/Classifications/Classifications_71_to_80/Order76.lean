/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order4P
import Mathlib.Tactic.NormNum.Prime

/-!
# Classification of groups of order 76

`76 = 4 · 19`, so there are exactly **four** groups of order `76` up to isomorphism:
the cyclic group `ℤ/76`, `ℤ/2 × ℤ/38`, `ℤ/19 ⋊_{-1} ℤ/4`, and `ℤ/2 × D₃₈`.
This is the `p = 19` (p ≡ 3 mod 4) instance of the order-`4p` classification in
`Smallgroups.UsefulTheorems.Order4P`.
-/

namespace Smallgroups.Classifications.Order76

open Smallgroups.UsefulTheorems

/-- `ℤ/76`. -/
abbrev RA : Type := fourP_I 19
/-- `ℤ/2 × ℤ/38`. -/
abbrev RB : Type := fourP_II 19
/-- `ℤ/19 ⋊_{-1} ℤ/4`. -/
abbrev RC : Type := fourP_III 19
/-- `ℤ/2 × D₃₈`. -/
abbrev RD : Type := fourP_V 19

variable {G : Type*} [Group G]

/-- **(1) Exhaustiveness.** Every group of order `76` is isomorphic to one of the four groups. -/
theorem classification (h : Nat.card G = 76) :
    Nonempty (G ≃* RA) ∨ Nonempty (G ≃* RB) ∨ Nonempty (G ≃* RC) ∨
    Nonempty (G ≃* RD) := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  simpa [RA, RB, RC, RD, show (4 : ℕ) * 19 = 76 by norm_num] using
    fourP_classification_mod3 (by norm_num : Nat.Prime 19) (by omega)
      (by norm_num : 19 % 4 = 3) (h.trans (by norm_num))

/-- **(2) Distinctness & (3) Counting.** The four groups are a complete, non-redundant list of
representatives of the groups of order `76`. -/
theorem isClassif : IsClassif 76 (rep4 RA RB RC RD) := by
  simpa [RA, RB, RC, RD, show (4 : ℕ) * 19 = 76 by norm_num] using
    fourP_isClassif_mod3 (by norm_num : Nat.Prime 19) (by omega)
      (by norm_num : 19 % 4 = 3)

/-- **The number of isomorphism classes of groups of order `76` is exactly `4`.** -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 76 rep) : k = 4 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order76
