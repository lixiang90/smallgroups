/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent10BatchIdentity
import Smallgroups.UsefulTheorems.PGroupGeneration.CohomologyDecomposition
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent09Reduction

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP10_decompose_cocycle (v : TwoVec)
    (hv : IsCentralCocycle (Order16Table.decodeTwo parent10Table v)) :
    ∃ d : OneVec, ∃ q : Fin 6 → F2,
      v = Order16Table.coboundaryVec parent10Table d +
        synthesizeTwo coverageP10HBasis q := by
  apply Order16Table.decomposeCocycle parent10Table coverageP10BBasis
    coverageP10DBasis coverageP10HBasis coverageP10CoordinateRows
    coverageP10EquationTriples coverageP10CorrectionColumns
  · simpa [coverageP10ReductionMap, coverageP10TotalBasis] using
      coverageP10_reduction_identity_batched
  · exact coverageP10_coboundary_basis
  · exact hv

end Smallgroups.UsefulTheorems.Order32Certificate
