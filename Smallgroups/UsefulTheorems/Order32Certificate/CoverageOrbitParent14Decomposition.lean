/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent14BatchIdentity
import Smallgroups.UsefulTheorems.PGroupGeneration.CohomologyDecomposition

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_decompose_cocycle (v : TwoVec)
    (hv : IsCentralCocycle (Order16Table.decodeTwo parent14Table v)) :
    ∃ d : OneVec, ∃ q : Fin 10 → F2,
      v = Order16Table.coboundaryVec parent14Table d +
        synthesizeTwo parent14HBasis q := by
  apply Order16Table.decomposeCocycle parent14Table parent14BBasis
    parent14DBasis parent14HBasis parent14CoordinateRows
    parent14EquationTriples parent14CorrectionColumns
  · simpa [parent14ReductionMap, parent14TotalBasis] using
      parent14_reduction_identity_batched
  · exact parent14_coboundary_basis
  · exact hv

end Smallgroups.UsefulTheorems.Order32Certificate
