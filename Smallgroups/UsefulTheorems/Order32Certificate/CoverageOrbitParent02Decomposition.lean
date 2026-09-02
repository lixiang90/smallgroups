/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent02BatchIdentity
import Smallgroups.UsefulTheorems.PGroupGeneration.CohomologyDecomposition
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent01Reduction

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP2_decompose_cocycle (v : TwoVec)
    (hv : IsCentralCocycle (Order16Table.decodeTwo parent2Table v)) :
    ∃ d : OneVec, ∃ q : Fin 3 → F2,
      v = Order16Table.coboundaryVec parent2Table d +
        synthesizeTwo coverageP2HBasis q := by
  apply Order16Table.decomposeCocycle parent2Table coverageP2BBasis
    coverageP2DBasis coverageP2HBasis coverageP2CoordinateRows
    coverageP2EquationTriples coverageP2CorrectionColumns
  · simpa [coverageP2ReductionMap, coverageP2TotalBasis] using
      coverageP2_reduction_identity_batched
  · exact coverageP2_coboundary_basis
  · exact hv

end Smallgroups.UsefulTheorems.Order32Certificate
