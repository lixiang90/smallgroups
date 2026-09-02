/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent08Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent07PathPart01

set_option maxRecDepth 100000

/-! Checked short orbit paths for parent 8; generated part 1. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP8_path_endpoint_0 :
    Order16Table.applyOrbitPath orbitP8ActionColumns []
      (orbitP8RepresentativeCoeff 0) = orbitP8TargetCoeff 0 := by
  decide +kernel

noncomputable def orbitP8NormalizeEquiv0 :
    CocycleGroup (orbitP8SelectedCocycle (orbitP8Index 0))
        (orbitP8SelectedCocycle_consistent (orbitP8Index 0)) ≃*
      CocycleGroup (orbitP8TargetCocycle 0)
        (orbitP8TargetCocycle_consistent 0) := by
  let e := Order16Table.orbitPathEquiv parent8Table coverageP8HBasis
    orbitP8ActionColumns orbitP8CorrectionColumns orbitP8_hbasis_cocycle
    orbitP8Aut orbitP8_action_linear [] (orbitP8RepresentativeCoeff 0)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent8Table coverageP8HBasis)
      orbitP8_path_endpoint_0))

theorem orbitP8_path_endpoint_1 :
    Order16Table.applyOrbitPath orbitP8ActionColumns []
      (orbitP8RepresentativeCoeff 1) = orbitP8TargetCoeff 1 := by
  decide +kernel

noncomputable def orbitP8NormalizeEquiv1 :
    CocycleGroup (orbitP8SelectedCocycle (orbitP8Index 1))
        (orbitP8SelectedCocycle_consistent (orbitP8Index 1)) ≃*
      CocycleGroup (orbitP8TargetCocycle 1)
        (orbitP8TargetCocycle_consistent 1) := by
  let e := Order16Table.orbitPathEquiv parent8Table coverageP8HBasis
    orbitP8ActionColumns orbitP8CorrectionColumns orbitP8_hbasis_cocycle
    orbitP8Aut orbitP8_action_linear [] (orbitP8RepresentativeCoeff 1)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent8Table coverageP8HBasis)
      orbitP8_path_endpoint_1))

theorem orbitP8_path_endpoint_2 :
    Order16Table.applyOrbitPath orbitP8ActionColumns []
      (orbitP8RepresentativeCoeff 2) = orbitP8TargetCoeff 2 := by
  decide +kernel

noncomputable def orbitP8NormalizeEquiv2 :
    CocycleGroup (orbitP8SelectedCocycle (orbitP8Index 2))
        (orbitP8SelectedCocycle_consistent (orbitP8Index 2)) ≃*
      CocycleGroup (orbitP8TargetCocycle 2)
        (orbitP8TargetCocycle_consistent 2) := by
  let e := Order16Table.orbitPathEquiv parent8Table coverageP8HBasis
    orbitP8ActionColumns orbitP8CorrectionColumns orbitP8_hbasis_cocycle
    orbitP8Aut orbitP8_action_linear [] (orbitP8RepresentativeCoeff 2)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent8Table coverageP8HBasis)
      orbitP8_path_endpoint_2))

theorem orbitP8_path_endpoint_3 :
    Order16Table.applyOrbitPath orbitP8ActionColumns []
      (orbitP8RepresentativeCoeff 3) = orbitP8TargetCoeff 3 := by
  decide +kernel

noncomputable def orbitP8NormalizeEquiv3 :
    CocycleGroup (orbitP8SelectedCocycle (orbitP8Index 3))
        (orbitP8SelectedCocycle_consistent (orbitP8Index 3)) ≃*
      CocycleGroup (orbitP8TargetCocycle 3)
        (orbitP8TargetCocycle_consistent 3) := by
  let e := Order16Table.orbitPathEquiv parent8Table coverageP8HBasis
    orbitP8ActionColumns orbitP8CorrectionColumns orbitP8_hbasis_cocycle
    orbitP8Aut orbitP8_action_linear [] (orbitP8RepresentativeCoeff 3)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent8Table coverageP8HBasis)
      orbitP8_path_endpoint_3))

end Smallgroups.UsefulTheorems.Order32Certificate
