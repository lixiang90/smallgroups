/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent03BatchIdentity
import Smallgroups.UsefulTheorems.PGroupGeneration.CohomologyDecomposition
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent02Reduction

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP3_decompose_cocycle (v : TwoVec)
    (hv : IsCentralCocycle (Order16Table.decodeTwo parent3Table v)) :
    ∃ d : OneVec, ∃ q : Fin 4 → F2,
      v = Order16Table.coboundaryVec parent3Table d +
        synthesizeTwo coverageP3HBasis q := by
  apply Order16Table.decomposeCocycle parent3Table coverageP3BBasis
    coverageP3DBasis coverageP3HBasis coverageP3CoordinateRows
    coverageP3EquationTriples coverageP3CorrectionColumns
  · simpa [coverageP3ReductionMap, coverageP3TotalBasis] using
      coverageP3_reduction_identity_batched
  · exact coverageP3_coboundary_basis
  · exact hv

end Smallgroups.UsefulTheorems.Order32Certificate
