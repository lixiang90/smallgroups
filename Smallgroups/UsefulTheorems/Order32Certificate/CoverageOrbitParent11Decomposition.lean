/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent11BatchIdentity
import Smallgroups.UsefulTheorems.PGroupGeneration.CohomologyDecomposition

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP11_decompose_cocycle (v : TwoVec)
    (hv : IsCentralCocycle (Order16Table.decodeTwo parent11Table v)) :
    ∃ d : OneVec, ∃ q : Fin 6 → F2,
      v = Order16Table.coboundaryVec parent11Table d +
        synthesizeTwo coverageP11HBasis q := by
  apply Order16Table.decomposeCocycle parent11Table coverageP11BBasis
    coverageP11DBasis coverageP11HBasis coverageP11CoordinateRows
    coverageP11EquationTriples coverageP11CorrectionColumns
  · simpa [coverageP11ReductionMap, coverageP11TotalBasis] using
      coverageP11_reduction_identity_batched
  · exact coverageP11_coboundary_basis
  · exact hv

end Smallgroups.UsefulTheorems.Order32Certificate
