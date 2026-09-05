/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PGroupGeneration.CertifiedTable
import Smallgroups.UsefulTheorems.PGroupGeneration.FiniteCohomology
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Data.BitVec

/-!
# Kernel-checked GF(2) certificates for central extensions of a group of order 16

The external generator represents a normalized two-cochain by its `15 * 15` nonidentity
entries.  This file supplies the trusted interpretation of those bit vectors and small
linear maps used by generated certificates.  A generated basis/coordinate certificate is
checked as an equality of linear maps on the standard basis; no enumeration of the
`2^225` ambient vectors is involved.
-/

namespace Smallgroups.UsefulTheorems.GF2Certificate

open scoped BigOperators

abbrev F2 := ZMod 2
abbrev OneVec := Fin 15 → F2
abbrev TwoIndex := Fin 15 × Fin 15
abbrev TwoVec := TwoIndex → F2

/-- Row-major index of a normalized two-cochain coordinate. -/
def twoIndex (p : TwoIndex) : ℕ := 15 * p.1.val + p.2.val

/-- Decode a natural-number bit mask as a normalized one-cochain vector. -/
def oneMask (mask : ℕ) : OneVec := fun i =>
  if mask.testBit i.val then 1 else 0

/-- Decode a natural-number bit mask as a normalized two-cochain vector. -/
def twoMask (mask : ℕ) : TwoVec := fun p =>
  if mask.testBit (twoIndex p) then 1 else 0

/-- Coefficient vector encoded by the low `k` bits of a natural number. -/
def coeffMask (k : ℕ) (mask : ℕ) : Fin k → F2 := fun i =>
  if mask.testBit i.val then 1 else 0

/-- A standard basis vector in normalized two-cochain coordinates. -/
def unitTwo (p : TwoIndex) : TwoVec := fun q => if q = p then 1 else 0

theorem basisFun_eq_unitTwo (p : TwoIndex) :
    (Pi.basisFun F2 TwoIndex) p = unitTwo p := by
  rw [Pi.basisFun_apply]
  ext q
  simp [unitTwo, Pi.single_apply]

/-- Binary index of an `F₂` vector.  `BitVec.ofNat` supplies the bound proof. -/
def vecIndex (k : ℕ) (v : Fin k → F2) : Fin (2 ^ k) :=
  (BitVec.ofNat k (∑ i, (v i).val * 2 ^ i.val)).toFin

/-- Linear synthesis from bit-packed columns. -/
def synthesizeTwo {k : ℕ} (columns : Fin k → ℕ) :
    (Fin k → F2) →ₗ[F2] TwoVec where
  toFun c := fun p => ∑ i, c i * twoMask (columns i) p
  map_add' x y := by
    classical
    ext p
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r x := by
    classical
    ext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Linear analysis by bit-packed row vectors. -/
def analyzeTwo {k : ℕ} (rows : Fin k → ℕ) :
    TwoVec →ₗ[F2] (Fin k → F2) where
  toFun v := fun i => ∑ p, twoMask (rows i) p * v p
  map_add' x y := by
    classical
    ext i
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    classical
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    calc
      ∑ p, twoMask (rows i) p * (r * x p) =
          ∑ p, (twoMask (rows i) p * x p) * r := by
            apply Finset.sum_congr rfl
            intro p _
            ring
      _ = (∑ p, twoMask (rows i) p * x p) * r := by rw [Finset.sum_mul]
      _ = r * ∑ p, twoMask (rows i) p * x p := by ring

/-- Linear synthesis of normalized one-cochains from bit-packed columns. -/
def synthesizeOne {k : ℕ} (columns : Fin k → ℕ) :
    (Fin k → F2) →ₗ[F2] OneVec where
  toFun c := fun p => ∑ i, c i * oneMask (columns i) p
  map_add' x y := by
    classical
    ext p
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r x := by
    classical
    ext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

namespace Order16Table

variable (T : CertifiedGroupTable 16)

abbrev Q := CertifiedTableGroup T

/-- The group element with a specified table index. -/
def elem (i : Fin 16) : Q T := ⟨i⟩

/-- Interpret a 15-vector as a normalized one-cochain on the certified group table. -/
def decodeOne (d : OneVec) : Q T → F2 := fun a =>
  if h : a.val = 0 then 0 else d (a.val.pred h)

/-- Interpret a 225-vector as a normalized two-cochain on the certified group table. -/
def decodeTwo (v : TwoVec) : Q T → Q T → F2 := fun a b =>
  if ha : a.val = 0 then 0
  else if hb : b.val = 0 then 0
  else v (a.val.pred ha, b.val.pred hb)

/-- Restrict a two-cochain to its nonidentity entries. -/
def encodeTwo (f : Q T → Q T → F2) : TwoVec := fun p =>
  f (elem T p.1.succ) (elem T p.2.succ)

@[simp] theorem decodeOne_zero (d : OneVec) : decodeOne T d 1 = 0 := by
  rfl

theorem decodeOne_add (d e : OneVec) (a : Q T) :
    decodeOne T (d + e) a = decodeOne T d a + decodeOne T e a := by
  by_cases ha : a.val = 0 <;> simp [decodeOne, ha]

theorem decodeOne_smul (r : F2) (d : OneVec) (a : Q T) :
    decodeOne T (r • d) a = r * decodeOne T d a := by
  by_cases ha : a.val = 0 <;> simp [decodeOne, ha]

theorem decodeTwo_add (v w : TwoVec) (a b : Q T) :
    decodeTwo T (v + w) a b = decodeTwo T v a b + decodeTwo T w a b := by
  by_cases ha : a.val = 0 <;> by_cases hb : b.val = 0 <;> simp [decodeTwo, ha, hb]

theorem decodeTwo_smul (r : F2) (v : TwoVec) (a b : Q T) :
    decodeTwo T (r • v) a b = r * decodeTwo T v a b := by
  by_cases ha : a.val = 0 <;> by_cases hb : b.val = 0 <;> simp [decodeTwo, ha, hb]

theorem decodeTwo_encodeTwo {f : Q T → Q T → F2} (hf : IsCentralCocycle f) :
    decodeTwo T (encodeTwo T f) = f := by
  funext a b
  by_cases ha : a.val = 0
  · have ha1 : a = 1 := by
      apply CertifiedTableGroup.ext
      change a.val = 0
      exact ha
    rw [decodeTwo, dif_pos ha]
    change 0 = f a b
    rw [ha1, hf.one_left]
  · by_cases hb : b.val = 0
    · have hb1 : b = 1 := by
        apply CertifiedTableGroup.ext
        change b.val = 0
        exact hb
      rw [decodeTwo, dif_neg ha, dif_pos hb]
      change 0 = f a b
      rw [hb1, hf.one_right]
    · rw [decodeTwo, dif_neg ha, dif_neg hb]
      change f (elem T (a.val.pred ha).succ) (elem T (b.val.pred hb).succ) = f a b
      congr 2
      · exact Fin.succ_pred _ _
      · exact Fin.succ_pred _ _

/-- Coboundary on normalized vector coordinates. -/
def coboundaryVec : OneVec →ₗ[F2] TwoVec where
  toFun d := encodeTwo T (centralCoboundary (Q T) F2 (decodeOne T d))
  map_add' d e := by
    ext p
    simp only [encodeTwo, centralCoboundary, Pi.add_apply, decodeOne_add]
    ring
  map_smul' r d := by
    ext p
    simp only [encodeTwo, centralCoboundary, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, decodeOne_smul]
    ring

theorem decodeTwo_coboundaryVec (d : OneVec) :
    decodeTwo T (coboundaryVec T d) = centralCoboundary (Q T) F2 (decodeOne T d) := by
  change decodeTwo T (encodeTwo T (centralCoboundary (Q T) F2 (decodeOne T d))) = _
  apply decodeTwo_encodeTwo T
  exact isCentralCocycle_centralCoboundary (Q T) F2 _ (decodeOne_zero T d)

/-- A selected independent list of cocycle equations. -/
def equationMap {r : ℕ} (triples : Fin r → Fin 16 × Fin 16 × Fin 16) :
    TwoVec →ₗ[F2] (Fin r → F2) where
  toFun v := fun i =>
    let a := elem T (triples i).1
    let b := elem T (triples i).2.1
    let c := elem T (triples i).2.2
    decodeTwo T v a b + decodeTwo T v (a * b) c -
      decodeTwo T v b c - decodeTwo T v a (b * c)
  map_add' x y := by
    ext i
    simp only [Pi.add_apply, decodeTwo_add]
    ring
  map_smul' s x := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, decodeTwo_smul]
    ring

theorem equationMap_eq_zero_of_cocycle {r : ℕ}
    (triples : Fin r → Fin 16 × Fin 16 × Fin 16) {v : TwoVec}
    (hv : IsCentralCocycle (decodeTwo T v)) : equationMap T triples v = 0 := by
  funext i
  simp only [equationMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
  let a := elem T (triples i).1
  let b := elem T (triples i).2.1
  let c := elem T (triples i).2.2
  rw [hv.cocycle a b c]
  ring

end Order16Table

end Smallgroups.UsefulTheorems.GF2Certificate
