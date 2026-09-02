/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PGroupGeneration.GF2Certificate

/-!
# Turning checked GF(2) reductions into cocycle decompositions

This file contains no generated data.  It converts a checked reduction identity and
checked coboundary preimages into the statement needed by p-group generation: every
normalized central cocycle is a coboundary plus selected `H²` coordinates.
-/

namespace Smallgroups.UsefulTheorems.GF2Certificate

def leftCoeffs {m n : ℕ} (c : Fin (m + n) → F2) : Fin m → F2 :=
  fun i => c (Fin.castAdd n i)

def rightCoeffs {m n : ℕ} (c : Fin (m + n) → F2) : Fin n → F2 :=
  fun i => c (Fin.natAdd m i)

theorem synthesizeTwo_append {m n : ℕ} (left : Fin m → ℕ) (right : Fin n → ℕ)
    (c : Fin (m + n) → F2) :
    synthesizeTwo (Fin.append left right) c =
      synthesizeTwo left (leftCoeffs c) + synthesizeTwo right (rightCoeffs c) := by
  ext p
  simp [synthesizeTwo, leftCoeffs, rightCoeffs, Fin.sum_univ_add]

namespace Order16Table

/-- A checked complementary basis for cocycles yields explicit `B² ⊕ H²` coordinates
for every normalized central cocycle. -/
theorem decomposeCocycle (T : CertifiedGroupTable 16) {b h r : ℕ}
    (bBasis : Fin b → ℕ) (dBasis : Fin b → ℕ) (hBasis : Fin h → ℕ)
    (coordinateRows : Fin (b + h) → ℕ)
    (equationTriples : Fin r → Fin 16 × Fin 16 × Fin 16)
    (correctionColumns : Fin r → ℕ)
    (hidentity :
      (synthesizeTwo (Fin.append bBasis hBasis)).comp (analyzeTwo coordinateRows) +
        (synthesizeTwo correctionColumns).comp (equationMap T equationTriples) =
          LinearMap.id)
    (hcoboundary :
      (coboundaryVec T).comp (synthesizeOne dBasis) = synthesizeTwo bBasis)
    (v : TwoVec) (hv : IsCentralCocycle (decodeTwo T v)) :
    ∃ d : OneVec, ∃ q : Fin h → F2,
      v = coboundaryVec T d + synthesizeTwo hBasis q := by
  let c := analyzeTwo coordinateRows v
  let cb : Fin b → F2 := leftCoeffs c
  let ch : Fin h → F2 := rightCoeffs c
  let d : OneVec := synthesizeOne dBasis cb
  refine ⟨d, ch, ?_⟩
  have heq : equationMap T equationTriples v = 0 :=
    equationMap_eq_zero_of_cocycle T equationTriples hv
  have hreduce := LinearMap.congr_fun hidentity v
  change ((synthesizeTwo (Fin.append bBasis hBasis)).comp (analyzeTwo coordinateRows) +
    (synthesizeTwo correctionColumns).comp (equationMap T equationTriples)) v = v at hreduce
  rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    heq, map_zero, add_zero] at hreduce
  rw [← hreduce, synthesizeTwo_append]
  change synthesizeTwo bBasis cb + synthesizeTwo hBasis ch =
    coboundaryVec T d + synthesizeTwo hBasis ch
  congr 1
  rw [← LinearMap.comp_apply, hcoboundary]

end Order16Table

end Smallgroups.UsefulTheorems.GF2Certificate
