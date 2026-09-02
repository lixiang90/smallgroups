/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent05BatchIdentity
import Smallgroups.UsefulTheorems.PGroupGeneration.CohomologyDecomposition
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent04Reduction

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP5_decompose_cocycle (v : TwoVec)
    (hv : IsCentralCocycle (Order16Table.decodeTwo parent5Table v)) :
    ∃ d : OneVec, ∃ q : Fin 3 → F2,
      v = Order16Table.coboundaryVec parent5Table d +
        synthesizeTwo coverageP5HBasis q := by
  apply Order16Table.decomposeCocycle parent5Table coverageP5BBasis
    coverageP5DBasis coverageP5HBasis coverageP5CoordinateRows
    coverageP5EquationTriples coverageP5CorrectionColumns
  · simpa [coverageP5ReductionMap, coverageP5TotalBasis] using
      coverageP5_reduction_identity_batched
  · exact coverageP5_coboundary_basis
  · exact hv

end Smallgroups.UsefulTheorems.Order32Certificate
