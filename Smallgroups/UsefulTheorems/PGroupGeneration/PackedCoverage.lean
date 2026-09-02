/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PGroupGeneration.PackedGF2Certificate

/-! Generic lifting of packed matrix certificates to cocycle-equation reductions. -/

namespace Smallgroups.UsefulTheorems.GF2Certificate

namespace Order16Table

/-- Row-major decoding of a `Fin 225` coordinate into the normalized 15-by-15 table. -/
def fin225ToTwoIndex (q : Fin 225) : TwoIndex :=
  (⟨q.val / 15, by omega⟩, ⟨q.val % 15, Nat.mod_lt _ (by omega)⟩)

/-- All four inexpensive checks needed for every column of a packed reduction matrix. -/
def PackedCoverageCertificate (T : CertifiedGroupTable 16) {k r : ℕ}
    (basis : Fin k → ℕ) (rows : Fin k → ℕ)
    (triples : Fin r → Fin 16 × Fin 16 × Fin 16) (corrections : Fin r → ℕ)
    (coordinateMasks equationMasks : Fin 225 → ℕ) : Prop :=
  ∀ q : Fin 225,
    (∀ i : Fin k, (rows i).testBit (twoIndex (fin225ToTwoIndex q)) =
      (coordinateMasks q).testBit i.val) ∧
    equationMap T triples (unitTwo (fin225ToTwoIndex q)) = coeffMask r (equationMasks q) ∧
    xorSynthesizeMask basis (coordinateMasks q) ^^^
        xorSynthesizeMask corrections (equationMasks q) =
      1 <<< twoIndex (fin225ToTwoIndex q)

theorem analyzeTwo_unitTwo_apply {k : ℕ} (rows : Fin k → ℕ)
    (p : TwoIndex) (i : Fin k) :
    analyzeTwo rows (unitTwo p) i =
      if (rows i).testBit (twoIndex p) then 1 else 0 := by
  classical
  change (∑ x, twoMask (rows i) x * (if x = p then 1 else 0)) = _
  rw [Finset.sum_eq_single p]
  · simp [twoMask]
  · intro b _ hbp
    simp [hbp]
  · simp

theorem analyzeTwo_unitTwo_eq_coeffMask {k : ℕ} (rows : Fin k → ℕ)
    (p : TwoIndex) (coordinateMask : ℕ)
    (hrows : ∀ i : Fin k, (rows i).testBit (twoIndex p) =
      coordinateMask.testBit i.val) :
    analyzeTwo rows (unitTwo p) = coeffMask k coordinateMask := by
  ext i
  rw [analyzeTwo_unitTwo_apply]
  simp only [coeffMask]
  rw [hrows i]

theorem twoIndex_injective : Function.Injective twoIndex := by
  intro p q h
  apply Prod.ext
  · apply Fin.ext
    simp only [twoIndex] at h
    omega
  · apply Fin.ext
    simp only [twoIndex] at h
    omega

theorem twoMask_singleton (p : TwoIndex) :
    twoMask (1 <<< twoIndex p) = unitTwo p := by
  ext q
  simp [twoMask, unitTwo, Nat.one_shiftLeft, Nat.testBit_two_pow,
    twoIndex_injective.eq_iff, eq_comm]

/-- Lift efficient coordinate, equation, and XOR checks to a column of a cocycle-space
reduction.  This is independent of a particular order-16 multiplication table. -/
theorem reductionColumnOfPacked (T : CertifiedGroupTable 16) {k r : ℕ}
    (basis : Fin k → ℕ) (rows : Fin k → ℕ)
    (triples : Fin r → Fin 16 × Fin 16 × Fin 16) (corrections : Fin r → ℕ)
    (p : TwoIndex) (coordinateMask equationMask : ℕ)
    (hcoordinate : analyzeTwo rows (unitTwo p) = coeffMask k coordinateMask)
    (hequation : equationMap T triples (unitTwo p) = coeffMask r equationMask)
    (hpacked :
      xorSynthesize basis (coeffMask k coordinateMask) ^^^
        xorSynthesize corrections (coeffMask r equationMask) = 1 <<< twoIndex p)
    (hsingle : twoMask (1 <<< twoIndex p) = unitTwo p) :
    ((synthesizeTwo basis).comp (analyzeTwo rows) +
      (synthesizeTwo corrections).comp (equationMap T triples)) (unitTwo p) = unitTwo p := by
  rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    hcoordinate, hequation, synthesizeTwo_coeffMask_eq_twoMask_xorSynthesize,
    synthesizeTwo_coeffMask_eq_twoMask_xorSynthesize, ← twoMask_xor, hpacked, hsingle]

/-- A single finite packed certificate establishes the full reduction-map identity. -/
theorem reductionIdentityOfPackedCertificate (T : CertifiedGroupTable 16) {k r : ℕ}
    (basis : Fin k → ℕ) (rows : Fin k → ℕ)
    (triples : Fin r → Fin 16 × Fin 16 × Fin 16) (corrections : Fin r → ℕ)
    (coordinateMasks equationMasks : Fin 225 → ℕ)
    (hcert : PackedCoverageCertificate T basis rows triples corrections
      coordinateMasks equationMasks) :
    (synthesizeTwo basis).comp (analyzeTwo rows) +
        (synthesizeTwo corrections).comp (equationMap T triples) = LinearMap.id := by
  apply (Pi.basisFun F2 TwoIndex).ext
  intro p
  rw [basisFun_eq_unitTwo]
  let q : Fin 225 := ⟨twoIndex p, by
    simp only [twoIndex]
    omega⟩
  have hpq : fin225ToTwoIndex q = p := by
    ext
    · simp [q, fin225ToTwoIndex, twoIndex]
      omega
    · simp [q, fin225ToTwoIndex, twoIndex]
  rw [← hpq]
  exact reductionColumnOfPacked T basis rows triples corrections
    (fin225ToTwoIndex q) (coordinateMasks q) (equationMasks q)
    (analyzeTwo_unitTwo_eq_coeffMask rows (fin225ToTwoIndex q) (coordinateMasks q)
      (hcert q).1)
    (hcert q).2.1 (by
      simpa only [xorSynthesize_coeffMask] using (hcert q).2.2)
    (twoMask_singleton (fin225ToTwoIndex q))

end Order16Table

end Smallgroups.UsefulTheorems.GF2Certificate
