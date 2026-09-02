/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent07BatchIdentity
import Smallgroups.UsefulTheorems.PGroupGeneration.CohomologyDecomposition

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP7_decompose_cocycle (v : TwoVec)
    (hv : IsCentralCocycle (Order16Table.decodeTwo parent7Table v)) :
    ∃ d : OneVec, ∃ q : Fin 3 → F2,
      v = Order16Table.coboundaryVec parent7Table d +
        synthesizeTwo coverageP7HBasis q := by
  apply Order16Table.decomposeCocycle parent7Table coverageP7BBasis
    coverageP7DBasis coverageP7HBasis coverageP7CoordinateRows
    coverageP7EquationTriples coverageP7CorrectionColumns
  · simpa [coverageP7ReductionMap, coverageP7TotalBasis] using
      coverageP7_reduction_identity_batched
  · exact coverageP7_coboundary_basis
  · exact hv

end Smallgroups.UsefulTheorems.Order32Certificate
