/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent07Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent06PathIdentity

set_option maxRecDepth 100000

/-! Checked short orbit paths for parent 7; generated part 1. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP7_path_endpoint_0 :
    Order16Table.applyOrbitPath orbitP7ActionColumns []
      (orbitP7RepresentativeCoeff 0) = orbitP7TargetCoeff 0 := by
  decide +kernel

noncomputable def orbitP7NormalizeEquiv0 :
    CocycleGroup (orbitP7SelectedCocycle (orbitP7Index 0))
        (orbitP7SelectedCocycle_consistent (orbitP7Index 0)) ≃*
      CocycleGroup (orbitP7TargetCocycle 0)
        (orbitP7TargetCocycle_consistent 0) := by
  let e := Order16Table.orbitPathEquiv parent7Table coverageP7HBasis
    orbitP7ActionColumns orbitP7CorrectionColumns orbitP7_hbasis_cocycle
    orbitP7Aut orbitP7_action_linear [] (orbitP7RepresentativeCoeff 0)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent7Table coverageP7HBasis)
      orbitP7_path_endpoint_0))

theorem orbitP7_path_endpoint_1 :
    Order16Table.applyOrbitPath orbitP7ActionColumns []
      (orbitP7RepresentativeCoeff 1) = orbitP7TargetCoeff 1 := by
  decide +kernel

noncomputable def orbitP7NormalizeEquiv1 :
    CocycleGroup (orbitP7SelectedCocycle (orbitP7Index 1))
        (orbitP7SelectedCocycle_consistent (orbitP7Index 1)) ≃*
      CocycleGroup (orbitP7TargetCocycle 1)
        (orbitP7TargetCocycle_consistent 1) := by
  let e := Order16Table.orbitPathEquiv parent7Table coverageP7HBasis
    orbitP7ActionColumns orbitP7CorrectionColumns orbitP7_hbasis_cocycle
    orbitP7Aut orbitP7_action_linear [] (orbitP7RepresentativeCoeff 1)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent7Table coverageP7HBasis)
      orbitP7_path_endpoint_1))

theorem orbitP7_path_endpoint_2 :
    Order16Table.applyOrbitPath orbitP7ActionColumns []
      (orbitP7RepresentativeCoeff 2) = orbitP7TargetCoeff 2 := by
  decide +kernel

noncomputable def orbitP7NormalizeEquiv2 :
    CocycleGroup (orbitP7SelectedCocycle (orbitP7Index 2))
        (orbitP7SelectedCocycle_consistent (orbitP7Index 2)) ≃*
      CocycleGroup (orbitP7TargetCocycle 2)
        (orbitP7TargetCocycle_consistent 2) := by
  let e := Order16Table.orbitPathEquiv parent7Table coverageP7HBasis
    orbitP7ActionColumns orbitP7CorrectionColumns orbitP7_hbasis_cocycle
    orbitP7Aut orbitP7_action_linear [] (orbitP7RepresentativeCoeff 2)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent7Table coverageP7HBasis)
      orbitP7_path_endpoint_2))

theorem orbitP7_path_endpoint_3 :
    Order16Table.applyOrbitPath orbitP7ActionColumns [0]
      (orbitP7RepresentativeCoeff 3) = orbitP7TargetCoeff 3 := by
  decide +kernel

noncomputable def orbitP7NormalizeEquiv3 :
    CocycleGroup (orbitP7SelectedCocycle (orbitP7Index 3))
        (orbitP7SelectedCocycle_consistent (orbitP7Index 3)) ≃*
      CocycleGroup (orbitP7TargetCocycle 3)
        (orbitP7TargetCocycle_consistent 3) := by
  let e := Order16Table.orbitPathEquiv parent7Table coverageP7HBasis
    orbitP7ActionColumns orbitP7CorrectionColumns orbitP7_hbasis_cocycle
    orbitP7Aut orbitP7_action_linear [0] (orbitP7RepresentativeCoeff 3)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent7Table coverageP7HBasis)
      orbitP7_path_endpoint_3))

theorem orbitP7_path_endpoint_4 :
    Order16Table.applyOrbitPath orbitP7ActionColumns []
      (orbitP7RepresentativeCoeff 4) = orbitP7TargetCoeff 4 := by
  decide +kernel

noncomputable def orbitP7NormalizeEquiv4 :
    CocycleGroup (orbitP7SelectedCocycle (orbitP7Index 4))
        (orbitP7SelectedCocycle_consistent (orbitP7Index 4)) ≃*
      CocycleGroup (orbitP7TargetCocycle 4)
        (orbitP7TargetCocycle_consistent 4) := by
  let e := Order16Table.orbitPathEquiv parent7Table coverageP7HBasis
    orbitP7ActionColumns orbitP7CorrectionColumns orbitP7_hbasis_cocycle
    orbitP7Aut orbitP7_action_linear [] (orbitP7RepresentativeCoeff 4)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent7Table coverageP7HBasis)
      orbitP7_path_endpoint_4))

theorem orbitP7_path_endpoint_5 :
    Order16Table.applyOrbitPath orbitP7ActionColumns []
      (orbitP7RepresentativeCoeff 5) = orbitP7TargetCoeff 5 := by
  decide +kernel

noncomputable def orbitP7NormalizeEquiv5 :
    CocycleGroup (orbitP7SelectedCocycle (orbitP7Index 5))
        (orbitP7SelectedCocycle_consistent (orbitP7Index 5)) ≃*
      CocycleGroup (orbitP7TargetCocycle 5)
        (orbitP7TargetCocycle_consistent 5) := by
  let e := Order16Table.orbitPathEquiv parent7Table coverageP7HBasis
    orbitP7ActionColumns orbitP7CorrectionColumns orbitP7_hbasis_cocycle
    orbitP7Aut orbitP7_action_linear [] (orbitP7RepresentativeCoeff 5)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent7Table coverageP7HBasis)
      orbitP7_path_endpoint_5))

theorem orbitP7_path_endpoint_6 :
    Order16Table.applyOrbitPath orbitP7ActionColumns []
      (orbitP7RepresentativeCoeff 6) = orbitP7TargetCoeff 6 := by
  decide +kernel

noncomputable def orbitP7NormalizeEquiv6 :
    CocycleGroup (orbitP7SelectedCocycle (orbitP7Index 6))
        (orbitP7SelectedCocycle_consistent (orbitP7Index 6)) ≃*
      CocycleGroup (orbitP7TargetCocycle 6)
        (orbitP7TargetCocycle_consistent 6) := by
  let e := Order16Table.orbitPathEquiv parent7Table coverageP7HBasis
    orbitP7ActionColumns orbitP7CorrectionColumns orbitP7_hbasis_cocycle
    orbitP7Aut orbitP7_action_linear [] (orbitP7RepresentativeCoeff 6)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent7Table coverageP7HBasis)
      orbitP7_path_endpoint_6))

theorem orbitP7_path_endpoint_7 :
    Order16Table.applyOrbitPath orbitP7ActionColumns [0]
      (orbitP7RepresentativeCoeff 7) = orbitP7TargetCoeff 7 := by
  decide +kernel

noncomputable def orbitP7NormalizeEquiv7 :
    CocycleGroup (orbitP7SelectedCocycle (orbitP7Index 7))
        (orbitP7SelectedCocycle_consistent (orbitP7Index 7)) ≃*
      CocycleGroup (orbitP7TargetCocycle 7)
        (orbitP7TargetCocycle_consistent 7) := by
  let e := Order16Table.orbitPathEquiv parent7Table coverageP7HBasis
    orbitP7ActionColumns orbitP7CorrectionColumns orbitP7_hbasis_cocycle
    orbitP7Aut orbitP7_action_linear [0] (orbitP7RepresentativeCoeff 7)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent7Table coverageP7HBasis)
      orbitP7_path_endpoint_7))

end Smallgroups.UsefulTheorems.Order32Certificate
