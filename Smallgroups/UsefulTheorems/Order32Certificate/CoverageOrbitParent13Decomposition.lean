/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent13BatchIdentity
import Smallgroups.UsefulTheorems.PGroupGeneration.CohomologyDecomposition
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent12Reduction

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP13_decompose_cocycle (v : TwoVec)
    (hv : IsCentralCocycle (Order16Table.decodeTwo parent13Table v)) :
    ∃ d : OneVec, ∃ q : Fin 5 → F2,
      v = Order16Table.coboundaryVec parent13Table d +
        synthesizeTwo coverageP13HBasis q := by
  apply Order16Table.decomposeCocycle parent13Table coverageP13BBasis
    coverageP13DBasis coverageP13HBasis coverageP13CoordinateRows
    coverageP13EquationTriples coverageP13CorrectionColumns
  · simpa [coverageP13ReductionMap, coverageP13TotalBasis] using
      coverageP13_reduction_identity_batched
  · exact coverageP13_coboundary_basis
  · exact hv

end Smallgroups.UsefulTheorems.Order32Certificate
