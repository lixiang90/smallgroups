/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent04BatchIdentity
import Smallgroups.UsefulTheorems.PGroupGeneration.CohomologyDecomposition

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP4_decompose_cocycle (v : TwoVec)
    (hv : IsCentralCocycle (Order16Table.decodeTwo parent4Table v)) :
    ∃ d : OneVec, ∃ q : Fin 3 → F2,
      v = Order16Table.coboundaryVec parent4Table d +
        synthesizeTwo coverageP4HBasis q := by
  apply Order16Table.decomposeCocycle parent4Table coverageP4BBasis
    coverageP4DBasis coverageP4HBasis coverageP4CoordinateRows
    coverageP4EquationTriples coverageP4CorrectionColumns
  · simpa [coverageP4ReductionMap, coverageP4TotalBasis] using
      coverageP4_reduction_identity_batched
  · exact coverageP4_coboundary_basis
  · exact hv

end Smallgroups.UsefulTheorems.Order32Certificate
