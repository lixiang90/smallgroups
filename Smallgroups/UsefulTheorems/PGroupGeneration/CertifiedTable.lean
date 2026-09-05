/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PGroupGeneration.CocycleGroup
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Kernel-checked finite group tables and encoded cocycles

External generators may emit multiplication/inverse tables and bit-packed cocycles.
This module turns them into groups only after Lean checks the group laws, and turns a
bit mask into a `ZMod 2` cochain whose cocycle property is again decidable in Lean.

The identity is fixed at index `0`; this matches
`Scripts/generate_order32_cohomology.py` and removes the normalized cochain row and
column at `0` from the bit encoding.
-/

namespace Smallgroups.UsefulTheorems

/-- A finite group table with identity at `0`, carrying all laws needed by `Group`. -/
structure CertifiedGroupTable (n : ℕ) [NeZero n] where
  mul : Fin n → Fin n → Fin n
  inv : Fin n → Fin n
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  zero_mul : ∀ a, mul 0 a = a
  mul_zero : ∀ a, mul a 0 = a
  inv_mul_cancel : ∀ a, mul (inv a) a = 0

/-- The carrier of a certified finite group table.  It retains `T` in the type, so
different tables of the same size cannot acquire conflicting group instances. -/
@[ext]
structure CertifiedTableGroup {n : ℕ} [NeZero n] (T : CertifiedGroupTable n) where
  val : Fin n
deriving DecidableEq

namespace CertifiedTableGroup

variable {n : ℕ} [NeZero n] (T : CertifiedGroupTable n)

def equivFin : CertifiedTableGroup T ≃ Fin n where
  toFun := CertifiedTableGroup.val
  invFun := CertifiedTableGroup.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (CertifiedTableGroup T) :=
  Fintype.ofEquiv (Fin n) (equivFin T).symm

@[simp] theorem fintype_card : Fintype.card (CertifiedTableGroup T) = n :=
  by simpa using Fintype.card_congr (equivFin T)

instance : Mul (CertifiedTableGroup T) :=
  ⟨fun a b => ⟨T.mul a.val b.val⟩⟩
instance : One (CertifiedTableGroup T) := ⟨⟨0⟩⟩
instance : Inv (CertifiedTableGroup T) := ⟨fun a => ⟨T.inv a.val⟩⟩

instance : Group (CertifiedTableGroup T) where
  mul_assoc a b c := by
    apply CertifiedTableGroup.ext
    exact T.mul_assoc a.val b.val c.val
  one_mul a := by
    apply CertifiedTableGroup.ext
    exact T.zero_mul a.val
  mul_one a := by
    apply CertifiedTableGroup.ext
    exact T.mul_zero a.val
  inv_mul_cancel a := by
    apply CertifiedTableGroup.ext
    exact T.inv_mul_cancel a.val

/-- Index of a normalized two-cochain coordinate.  It is used only when both inputs
are nonzero, giving the compact `(n-1)²` layout used by the generator. -/
def normalizedCocycleIndex (a b : CertifiedTableGroup T) : ℕ :=
  (a.val.val - 1) * (n - 1) + (b.val.val - 1)

/-- Decode a bit-packed normalized `ZMod 2` two-cochain. -/
def encodedCocycle (mask : ℕ) :
    CertifiedTableGroup T → CertifiedTableGroup T → ZMod 2 :=
  fun a b =>
    if a = 1 ∨ b = 1 then 0
    else if mask.testBit (normalizedCocycleIndex T a b) then 1 else 0

@[simp] theorem encodedCocycle_one_left (mask : ℕ) (a : CertifiedTableGroup T) :
    encodedCocycle T mask 1 a = 0 := by
  simp [encodedCocycle]

@[simp] theorem encodedCocycle_one_right (mask : ℕ) (a : CertifiedTableGroup T) :
    encodedCocycle T mask a 1 = 0 := by
  simp [encodedCocycle]

end CertifiedTableGroup

/-- Enumeration index of a central `ZMod 2` extension over a certified table.  The
coefficient bit is the low bit, matching the generated multiplication tables. -/
def certifiedExtensionIndex {n : ℕ} [NeZero n] {T : CertifiedGroupTable n}
    {f : CertifiedTableGroup T → CertifiedTableGroup T → ZMod 2}
    {hf : IsCentralCocycle f} (x : CocycleGroup f hf) : Fin (2 * n) :=
  ⟨2 * x.snd.val.val + x.fst.val, by
    have hs := x.snd.val.isLt
    have hf := ZMod.val_lt x.fst
    omega⟩

/-! A tiny regression certificate for the table checker and bit decoder. -/

private def certifiedC2Table : CertifiedGroupTable 2 where
  mul a b := ⟨(a.val + b.val) % 2, Nat.mod_lt _ (by decide)⟩
  inv a := a
  mul_assoc := by decide
  zero_mul := by decide
  mul_zero := by decide
  inv_mul_cancel := by decide

example : IsCentralCocycle (CertifiedTableGroup.encodedCocycle certifiedC2Table 1) := by
  decide +kernel

end Smallgroups.UsefulTheorems
