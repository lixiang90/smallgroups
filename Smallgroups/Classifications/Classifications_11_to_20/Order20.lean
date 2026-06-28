/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order4P
import Mathlib.Tactic.NormNum.Prime

/-!
# Classification of groups of order 20

`20 = 4 · 5`, so there are exactly **five** groups of order `20` up to isomorphism:
the cyclic group `ℤ/20`, `ℤ/2 × ℤ/10`, `ℤ/5 ⋊_{-1} ℤ/4`, `ℤ/5 ⋊_c ℤ/4` (where `c² = -1`
in `(ℤ/5)ˣ`), and `ℤ/2 × D₁₀`.  This is the `p = 5` instance of the order-`4p`
classification in `Smallgroups.UsefulTheorems.Order4P`.
-/

namespace Smallgroups.Classifications.Order20

open Smallgroups.UsefulTheorems

private instance fact_prime_5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

private def c20 : (ZMod 5)ˣ :=
  Units.mk0 (2 : ZMod 5) (by decide)

private theorem hcsq20 : c20 ^ 2 = (-1 : (ZMod 5)ˣ) := by
  unfold c20; decide

/-- `ℤ/20`. -/
abbrev RA : Type := fourP_I 5
/-- `ℤ/2 × ℤ/10`. -/
abbrev RB : Type := fourP_II 5
/-- `ℤ/5 ⋊_{-1} ℤ/4`. -/
abbrev RC : Type := fourP_III 5
/-- `ℤ/5 ⋊_c ℤ/4` where `c² = -1` in `(ℤ/5)ˣ`. -/
abbrev RD : Type := fourP_IV 5 c20 (by
  rw [show (4 : ℕ) = 2 * 2 from by ring, pow_mul, hcsq20, neg_one_sq])
/-- `ℤ/2 × D₁₀`. -/
abbrev RE : Type := fourP_V 5

variable {G : Type*} [Group G]

/-- **(1) Exhaustiveness.** Every group of order `20` is isomorphic to one of the five groups. -/
theorem classification (h : Nat.card G = 20) :
    Nonempty (G ≃* RA) ∨ Nonempty (G ≃* RB) ∨ Nonempty (G ≃* RC) ∨
    Nonempty (G ≃* RD) ∨ Nonempty (G ≃* RE) := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  simpa [RA, RB, RC, RD, RE, show (4 : ℕ) * 5 = 20 by norm_num] using
    fourP_classification_mod1 (by norm_num : Nat.Prime 5) (by norm_num : 5 % 4 = 1)
      c20 hcsq20 (h.trans (by norm_num))

/-- **(2) Distinctness & (3) Counting.** The five groups are a complete, non-redundant list of
representatives of the groups of order `20`. -/
theorem isClassif : IsClassif 20 (rep5 RA RB RC RD RE) := by
  simpa [RA, RB, RC, RD, RE, show (4 : ℕ) * 5 = 20 by norm_num] using
    fourP_isClassif_mod1 (by norm_num : Nat.Prime 5) (by norm_num : 5 % 4 = 1) c20 hcsq20

/-- **The number of isomorphism classes of groups of order `20` is exactly `5`.** -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 20 rep) : k = 5 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order20
