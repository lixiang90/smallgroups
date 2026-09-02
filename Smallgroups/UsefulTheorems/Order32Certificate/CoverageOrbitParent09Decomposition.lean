/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent09BatchIdentity
import Smallgroups.UsefulTheorems.PGroupGeneration.CohomologyDecomposition
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent08Reduction

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP9_decompose_cocycle (v : TwoVec)
    (hv : IsCentralCocycle (Order16Table.decodeTwo parent9Table v)) :
    ∃ d : OneVec, ∃ q : Fin 2 → F2,
      v = Order16Table.coboundaryVec parent9Table d +
        synthesizeTwo coverageP9HBasis q := by
  apply Order16Table.decomposeCocycle parent9Table coverageP9BBasis
    coverageP9DBasis coverageP9HBasis coverageP9CoordinateRows
    coverageP9EquationTriples coverageP9CorrectionColumns
  · simpa [coverageP9ReductionMap, coverageP9TotalBasis] using
      coverageP9_reduction_identity_batched
  · exact coverageP9_coboundary_basis
  · exact hv

end Smallgroups.UsefulTheorems.Order32Certificate
