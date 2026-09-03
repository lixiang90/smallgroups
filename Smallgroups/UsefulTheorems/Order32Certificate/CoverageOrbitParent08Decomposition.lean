/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent08BatchIdentity
import Smallgroups.UsefulTheorems.PGroupGeneration.CohomologyDecomposition

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP8_decompose_cocycle (v : TwoVec)
    (hv : IsCentralCocycle (Order16Table.decodeTwo parent8Table v)) :
    ∃ d : OneVec, ∃ q : Fin 2 → F2,
      v = Order16Table.coboundaryVec parent8Table d +
        synthesizeTwo coverageP8HBasis q := by
  apply Order16Table.decomposeCocycle parent8Table coverageP8BBasis
    coverageP8DBasis coverageP8HBasis coverageP8CoordinateRows
    coverageP8EquationTriples coverageP8CorrectionColumns
  · simpa [coverageP8ReductionMap, coverageP8TotalBasis] using
      coverageP8_reduction_identity_batched
  · exact coverageP8_coboundary_basis
  · exact hv

end Smallgroups.UsefulTheorems.Order32Certificate
