/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent06BatchIdentity
import Smallgroups.UsefulTheorems.PGroupGeneration.CohomologyDecomposition

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP6_decompose_cocycle (v : TwoVec)
    (hv : IsCentralCocycle (Order16Table.decodeTwo parent6Table v)) :
    ∃ d : OneVec, ∃ q : Fin 2 → F2,
      v = Order16Table.coboundaryVec parent6Table d +
        synthesizeTwo coverageP6HBasis q := by
  apply Order16Table.decomposeCocycle parent6Table coverageP6BBasis
    coverageP6DBasis coverageP6HBasis coverageP6CoordinateRows
    coverageP6EquationTriples coverageP6CorrectionColumns
  · simpa [coverageP6ReductionMap, coverageP6TotalBasis] using
      coverageP6_reduction_identity_batched
  · exact coverageP6_coboundary_basis
  · exact hv

end Smallgroups.UsefulTheorems.Order32Certificate
