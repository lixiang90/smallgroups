/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent12BatchIdentity
import Smallgroups.UsefulTheorems.PGroupGeneration.CohomologyDecomposition
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11Reduction

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP12_decompose_cocycle (v : TwoVec)
    (hv : IsCentralCocycle (Order16Table.decodeTwo parent12Table v)) :
    ∃ d : OneVec, ∃ q : Fin 5 → F2,
      v = Order16Table.coboundaryVec parent12Table d +
        synthesizeTwo coverageP12HBasis q := by
  apply Order16Table.decomposeCocycle parent12Table coverageP12BBasis
    coverageP12DBasis coverageP12HBasis coverageP12CoordinateRows
    coverageP12EquationTriples coverageP12CorrectionColumns
  · simpa [coverageP12ReductionMap, coverageP12TotalBasis] using
      coverageP12_reduction_identity_batched
  · exact coverageP12_coboundary_basis
  · exact hv

end Smallgroups.UsefulTheorems.Order32Certificate
