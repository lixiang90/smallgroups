/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent01BatchIdentity
import Smallgroups.UsefulTheorems.PGroupGeneration.CohomologyDecomposition

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP1_decompose_cocycle (v : TwoVec)
    (hv : IsCentralCocycle (Order16Table.decodeTwo parent1Table v)) :
    ∃ d : OneVec, ∃ q : Fin 1 → F2,
      v = Order16Table.coboundaryVec parent1Table d +
        synthesizeTwo coverageP1HBasis q := by
  apply Order16Table.decomposeCocycle parent1Table coverageP1BBasis
    coverageP1DBasis coverageP1HBasis coverageP1CoordinateRows
    coverageP1EquationTriples coverageP1CorrectionColumns
  · simpa [coverageP1ReductionMap, coverageP1TotalBasis] using
      coverageP1_reduction_identity_batched
  · exact coverageP1_coboundary_basis
  · exact hv

end Smallgroups.UsefulTheorems.Order32Certificate
