/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PGroupGeneration.GF2Certificate

/-!
# Packed GF(2) synthesis certificates

Kernel reduction of a dense `225 × 225` matrix through function-valued vectors is
unnecessarily expensive.  This module proves once that synthesis of bit-packed columns
is the same as XORing their natural-number masks.  Generated certificates can therefore
check the large calculation with efficient `Nat.xor`, while the theorem below connects
that calculation back to the mathematical `F₂` linear map.
-/

namespace Smallgroups.UsefulTheorems.GF2Certificate

/-- XOR the selected bit-packed columns, reading the coefficient vector from low to high. -/
def xorSynthesize : {k : ℕ} → (Fin k → ℕ) → (Fin k → F2) → ℕ
  | 0, _, _ => 0
  | _ + 1, columns, coefficients =>
      (if coefficients 0 = 1 then columns 0 else 0) ^^^
        (xorSynthesize (fun i => columns i.succ) (fun i => coefficients i.succ))

/-- Pure natural-number specialization used when the coefficient vector is itself a mask. -/
def xorSynthesizeMask : {k : ℕ} → (Fin k → ℕ) → ℕ → ℕ
  | 0, _, _ => 0
  | _ + 1, columns, selection =>
      (if selection.testBit 0 then columns 0 else 0) ^^^
        xorSynthesizeMask (fun i => columns i.succ) (selection >>> 1)

theorem xorSynthesize_coeffMask {k : ℕ} (columns : Fin k → ℕ) (selection : ℕ) :
    xorSynthesize columns (coeffMask k selection) = xorSynthesizeMask columns selection := by
  induction k generalizing selection with
  | zero => rfl
  | succ k ih =>
      rw [xorSynthesize, xorSynthesizeMask]
      have htail :
          (fun i => coeffMask (k + 1) selection i.succ) =
            coeffMask k (selection >>> 1) := by
        funext i
        simp [coeffMask, Nat.testBit_shiftRight, Nat.add_comm]
      rw [htail, ih]
      cases h : selection.testBit 0 <;> simp [coeffMask, h]

theorem twoMask_xor (a b : ℕ) :
    twoMask (a ^^^ b) = twoMask a + twoMask b := by
  ext p
  simp only [twoMask, Pi.add_apply]
  rw [Nat.testBit_xor]
  generalize a.testBit (twoIndex p) = x
  generalize b.testBit (twoIndex p) = y
  cases x <;> cases y <;> decide

private theorem coefficient_mul_twoMask (x : F2) (mask : ℕ) :
    (fun p => x * twoMask mask p) = twoMask (if x = 1 then mask else 0) := by
  by_cases hx : x = 1
  · subst x
    ext p
    simp [twoMask]
  · have hx0 : x = 0 := by
      apply (ZMod.val_eq_zero x).mp
      have hlt : x.val < 2 := ZMod.val_lt x
      have hne : x.val ≠ 1 := by
        intro hval
        apply hx
        apply ZMod.val_injective
        exact hval.trans (by decide)
      omega
    subst x
    ext p
    simp [twoMask]

/-- Linear synthesis agrees with XOR synthesis of the packed columns. -/
theorem synthesizeTwo_coeffMask_eq_twoMask_xorSynthesize {k : ℕ}
    (columns : Fin k → ℕ) (coefficients : Fin k → F2) :
    synthesizeTwo columns coefficients = twoMask (xorSynthesize columns coefficients) := by
  induction k with
  | zero =>
      ext p
      simp [synthesizeTwo, xorSynthesize, twoMask]
  | succ k ih =>
      rw [show synthesizeTwo columns coefficients =
          (fun p => coefficients 0 * twoMask (columns 0) p) +
            synthesizeTwo (fun i => columns i.succ) (fun i => coefficients i.succ) by
        ext p
        simp [synthesizeTwo, Fin.sum_univ_succ]]
      rw [coefficient_mul_twoMask]
      rw [ih]
      rw [← twoMask_xor]
      rfl

end Smallgroups.UsefulTheorems.GF2Certificate
