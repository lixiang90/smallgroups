/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order4P
import Mathlib.Tactic.NormNum.Prime

/-!
# Classification of groups of order 52

`52 = 4 · 13`, so there are exactly **five** groups of order `52` up to isomorphism:
the cyclic group `ℤ/52`, `ℤ/2 × ℤ/26`, `ℤ/13 ⋊_{-1} ℤ/4`,
`ℤ/13 ⋊_c ℤ/4` (where `c² = -1` in `(ℤ/13)ˣ`), and `ℤ/2 × D₂₆`.
This is the `p = 13` (p ≡ 1 mod 4) instance of the order-`4p` classification in
`Smallgroups.UsefulTheorems.Order4P`.
-/

namespace Smallgroups.Classifications.Order52

open Smallgroups.UsefulTheorems

private instance fact_prime_13 : Fact (Nat.Prime 13) := ⟨by norm_num⟩

private def c13 : (ZMod 13)ˣ :=
  Units.mk0 (5 : ZMod 13) (by decide)

private theorem hcsq13 : c13 ^ 2 = (-1 : (ZMod 13)ˣ) := by
  unfold c13; decide

/-- `ℤ/52`. -/
abbrev RA : Type := fourP_I 13
/-- `ℤ/2 × ℤ/26`. -/
abbrev RB : Type := fourP_II 13
/-- `ℤ/13 ⋊_{-1} ℤ/4`. -/
abbrev RC : Type := fourP_III 13
/-- `ℤ/13 ⋊_c ℤ/4` where `c² = -1` in `(ℤ/13)ˣ`. -/
abbrev RD : Type := fourP_IV 13 c13 (by
  rw [show (4 : ℕ) = 2 * 2 from by ring, pow_mul, hcsq13, neg_one_sq])
/-- `ℤ/2 × D₂₆`. -/
abbrev RE : Type := fourP_V 13

variable {G : Type*} [Group G]

/-- **(1) Exhaustiveness.** Every group of order `52` is isomorphic to one of the five groups. -/
theorem classification (h : Nat.card G = 52) :
    Nonempty (G ≃* RA) ∨ Nonempty (G ≃* RB) ∨ Nonempty (G ≃* RC) ∨
    Nonempty (G ≃* RD) ∨ Nonempty (G ≃* RE) := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  simpa [RA, RB, RC, RD, RE, show (4 : ℕ) * 13 = 52 by norm_num] using
    fourP_classification_mod1 (by norm_num : Nat.Prime 13) (by norm_num : 13 % 4 = 1)
      c13 hcsq13 (h.trans (by norm_num))

/-- **(2) Distinctness & (3) Counting.** The five groups are a complete, non-redundant list of
representatives of the groups of order `52`. -/
theorem isClassif : IsClassif 52 (rep5 RA RB RC RD RE) := by
  simpa [RA, RB, RC, RD, RE, show (4 : ℕ) * 13 = 52 by norm_num] using
    fourP_isClassif_mod1 (by norm_num : Nat.Prime 13) (by norm_num : 13 % 4 = 1) c13 hcsq13

/-- **The number of isomorphism classes of groups of order `52` is exactly `5`.** -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 52 rep) : k = 5 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order52
