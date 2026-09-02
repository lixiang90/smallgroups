/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent09Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent08PathPart01

set_option maxRecDepth 100000

/-! Checked short orbit paths for parent 9; generated part 1. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP9_path_endpoint_0 :
    Order16Table.applyOrbitPath orbitP9ActionColumns []
      (orbitP9RepresentativeCoeff 0) = orbitP9TargetCoeff 0 := by
  decide +kernel

noncomputable def orbitP9NormalizeEquiv0 :
    CocycleGroup (orbitP9SelectedCocycle (orbitP9Index 0))
        (orbitP9SelectedCocycle_consistent (orbitP9Index 0)) ≃*
      CocycleGroup (orbitP9TargetCocycle 0)
        (orbitP9TargetCocycle_consistent 0) := by
  let e := Order16Table.orbitPathEquiv parent9Table coverageP9HBasis
    orbitP9ActionColumns orbitP9CorrectionColumns orbitP9_hbasis_cocycle
    orbitP9Aut orbitP9_action_linear [] (orbitP9RepresentativeCoeff 0)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent9Table coverageP9HBasis)
      orbitP9_path_endpoint_0))

theorem orbitP9_path_endpoint_1 :
    Order16Table.applyOrbitPath orbitP9ActionColumns []
      (orbitP9RepresentativeCoeff 1) = orbitP9TargetCoeff 1 := by
  decide +kernel

noncomputable def orbitP9NormalizeEquiv1 :
    CocycleGroup (orbitP9SelectedCocycle (orbitP9Index 1))
        (orbitP9SelectedCocycle_consistent (orbitP9Index 1)) ≃*
      CocycleGroup (orbitP9TargetCocycle 1)
        (orbitP9TargetCocycle_consistent 1) := by
  let e := Order16Table.orbitPathEquiv parent9Table coverageP9HBasis
    orbitP9ActionColumns orbitP9CorrectionColumns orbitP9_hbasis_cocycle
    orbitP9Aut orbitP9_action_linear [] (orbitP9RepresentativeCoeff 1)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent9Table coverageP9HBasis)
      orbitP9_path_endpoint_1))

theorem orbitP9_path_endpoint_2 :
    Order16Table.applyOrbitPath orbitP9ActionColumns []
      (orbitP9RepresentativeCoeff 2) = orbitP9TargetCoeff 2 := by
  decide +kernel

noncomputable def orbitP9NormalizeEquiv2 :
    CocycleGroup (orbitP9SelectedCocycle (orbitP9Index 2))
        (orbitP9SelectedCocycle_consistent (orbitP9Index 2)) ≃*
      CocycleGroup (orbitP9TargetCocycle 2)
        (orbitP9TargetCocycle_consistent 2) := by
  let e := Order16Table.orbitPathEquiv parent9Table coverageP9HBasis
    orbitP9ActionColumns orbitP9CorrectionColumns orbitP9_hbasis_cocycle
    orbitP9Aut orbitP9_action_linear [] (orbitP9RepresentativeCoeff 2)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent9Table coverageP9HBasis)
      orbitP9_path_endpoint_2))

theorem orbitP9_path_endpoint_3 :
    Order16Table.applyOrbitPath orbitP9ActionColumns [0]
      (orbitP9RepresentativeCoeff 3) = orbitP9TargetCoeff 3 := by
  decide +kernel

noncomputable def orbitP9NormalizeEquiv3 :
    CocycleGroup (orbitP9SelectedCocycle (orbitP9Index 3))
        (orbitP9SelectedCocycle_consistent (orbitP9Index 3)) ≃*
      CocycleGroup (orbitP9TargetCocycle 3)
        (orbitP9TargetCocycle_consistent 3) := by
  let e := Order16Table.orbitPathEquiv parent9Table coverageP9HBasis
    orbitP9ActionColumns orbitP9CorrectionColumns orbitP9_hbasis_cocycle
    orbitP9Aut orbitP9_action_linear [0] (orbitP9RepresentativeCoeff 3)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent9Table coverageP9HBasis)
      orbitP9_path_endpoint_3))

end Smallgroups.UsefulTheorems.Order32Certificate
