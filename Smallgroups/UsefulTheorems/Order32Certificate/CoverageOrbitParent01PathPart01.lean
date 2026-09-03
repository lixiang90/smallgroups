/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent01Core

set_option maxRecDepth 100000

/-! Checked short orbit paths for parent 1; generated part 1. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP1_path_endpoint_0 :
    Order16Table.applyOrbitPath orbitP1ActionColumns []
      (orbitP1RepresentativeCoeff 0) = orbitP1TargetCoeff 0 := by
  decide +kernel

noncomputable def orbitP1NormalizeEquiv0 :
    CocycleGroup (orbitP1SelectedCocycle (orbitP1Index 0))
        (orbitP1SelectedCocycle_consistent (orbitP1Index 0)) ≃*
      CocycleGroup (orbitP1TargetCocycle 0)
        (orbitP1TargetCocycle_consistent 0) := by
  let e := Order16Table.orbitPathEquiv parent1Table coverageP1HBasis
    orbitP1ActionColumns orbitP1CorrectionColumns orbitP1_hbasis_cocycle
    orbitP1Aut orbitP1_action_linear [] (orbitP1RepresentativeCoeff 0)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent1Table coverageP1HBasis)
      orbitP1_path_endpoint_0))

theorem orbitP1_path_endpoint_1 :
    Order16Table.applyOrbitPath orbitP1ActionColumns []
      (orbitP1RepresentativeCoeff 1) = orbitP1TargetCoeff 1 := by
  decide +kernel

noncomputable def orbitP1NormalizeEquiv1 :
    CocycleGroup (orbitP1SelectedCocycle (orbitP1Index 1))
        (orbitP1SelectedCocycle_consistent (orbitP1Index 1)) ≃*
      CocycleGroup (orbitP1TargetCocycle 1)
        (orbitP1TargetCocycle_consistent 1) := by
  let e := Order16Table.orbitPathEquiv parent1Table coverageP1HBasis
    orbitP1ActionColumns orbitP1CorrectionColumns orbitP1_hbasis_cocycle
    orbitP1Aut orbitP1_action_linear [] (orbitP1RepresentativeCoeff 1)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent1Table coverageP1HBasis)
      orbitP1_path_endpoint_1))

end Smallgroups.UsefulTheorems.Order32Certificate
