/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order4P
import Mathlib.Tactic.NormNum.Prime

/-!
# Classification of groups of order 68

`68 = 4 · 17`, so there are exactly **five** groups of order `68` up to isomorphism:
the cyclic group `ℤ/68`, `ℤ/2 × ℤ/34`, `ℤ/17 ⋊_{-1} ℤ/4`,
`ℤ/17 ⋊_c ℤ/4` (where `c² = -1` in `(ℤ/17)ˣ`), and `ℤ/2 × D₃₄`.
This is the `p = 17` (p ≡ 1 mod 4) instance of the order-`4p` classification in
`Smallgroups.UsefulTheorems.Order4P`.
-/

namespace Smallgroups.Classifications.Order68

open Smallgroups.UsefulTheorems

private instance fact_prime_17 : Fact (Nat.Prime 17) := ⟨by norm_num⟩

private def c17 : (ZMod 17)ˣ :=
  Units.mk0 (4 : ZMod 17) (by decide)

private theorem hcsq17 : c17 ^ 2 = (-1 : (ZMod 17)ˣ) := by
  unfold c17; decide

/-- `ℤ/68`. -/
abbrev RA : Type := fourP_I 17
/-- `ℤ/2 × ℤ/34`. -/
abbrev RB : Type := fourP_II 17
/-- `ℤ/17 ⋊_{-1} ℤ/4`. -/
abbrev RC : Type := fourP_III 17
/-- `ℤ/17 ⋊_c ℤ/4` where `c² = -1` in `(ℤ/17)ˣ`. -/
abbrev RD : Type := fourP_IV 17 c17 (by
  rw [show (4 : ℕ) = 2 * 2 from by ring, pow_mul, hcsq17, neg_one_sq])
/-- `ℤ/2 × D₃₄`. -/
abbrev RE : Type := fourP_V 17

variable {G : Type*} [Group G]

/-- **(1) Exhaustiveness.** Every group of order `68` is isomorphic to one of the five groups. -/
theorem classification (h : Nat.card G = 68) :
    Nonempty (G ≃* RA) ∨ Nonempty (G ≃* RB) ∨ Nonempty (G ≃* RC) ∨
    Nonempty (G ≃* RD) ∨ Nonempty (G ≃* RE) := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  simpa [RA, RB, RC, RD, RE, show (4 : ℕ) * 17 = 68 by norm_num] using
    fourP_classification_mod1 (by norm_num : Nat.Prime 17) (by norm_num : 17 % 4 = 1)
      c17 hcsq17 (h.trans (by norm_num))

/-- **(2) Distinctness & (3) Counting.** The five groups are a complete, non-redundant list of
representatives of the groups of order `68`. -/
theorem isClassif : IsClassif 68 (rep5 RA RB RC RD RE) := by
  simpa [RA, RB, RC, RD, RE, show (4 : ℕ) * 17 = 68 by norm_num] using
    fourP_isClassif_mod1 (by norm_num : Nat.Prime 17) (by norm_num : 17 % 4 = 1) c17 hcsq17

/-- **The number of isomorphism classes of groups of order `68` is exactly `5`.** -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 68 rep) : k = 5 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order68
