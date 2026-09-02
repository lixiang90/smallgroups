/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent05Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent04PathPart01

set_option maxRecDepth 100000

/-! Checked short orbit paths for parent 5; generated part 1. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP5_path_endpoint_0 :
    Order16Table.applyOrbitPath orbitP5ActionColumns []
      (orbitP5RepresentativeCoeff 0) = orbitP5TargetCoeff 0 := by
  decide +kernel

noncomputable def orbitP5NormalizeEquiv0 :
    CocycleGroup (orbitP5SelectedCocycle (orbitP5Index 0))
        (orbitP5SelectedCocycle_consistent (orbitP5Index 0)) ≃*
      CocycleGroup (orbitP5TargetCocycle 0)
        (orbitP5TargetCocycle_consistent 0) := by
  let e := Order16Table.orbitPathEquiv parent5Table coverageP5HBasis
    orbitP5ActionColumns orbitP5CorrectionColumns orbitP5_hbasis_cocycle
    orbitP5Aut orbitP5_action_linear [] (orbitP5RepresentativeCoeff 0)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent5Table coverageP5HBasis)
      orbitP5_path_endpoint_0))

theorem orbitP5_path_endpoint_1 :
    Order16Table.applyOrbitPath orbitP5ActionColumns []
      (orbitP5RepresentativeCoeff 1) = orbitP5TargetCoeff 1 := by
  decide +kernel

noncomputable def orbitP5NormalizeEquiv1 :
    CocycleGroup (orbitP5SelectedCocycle (orbitP5Index 1))
        (orbitP5SelectedCocycle_consistent (orbitP5Index 1)) ≃*
      CocycleGroup (orbitP5TargetCocycle 1)
        (orbitP5TargetCocycle_consistent 1) := by
  let e := Order16Table.orbitPathEquiv parent5Table coverageP5HBasis
    orbitP5ActionColumns orbitP5CorrectionColumns orbitP5_hbasis_cocycle
    orbitP5Aut orbitP5_action_linear [] (orbitP5RepresentativeCoeff 1)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent5Table coverageP5HBasis)
      orbitP5_path_endpoint_1))

theorem orbitP5_path_endpoint_2 :
    Order16Table.applyOrbitPath orbitP5ActionColumns []
      (orbitP5RepresentativeCoeff 2) = orbitP5TargetCoeff 2 := by
  decide +kernel

noncomputable def orbitP5NormalizeEquiv2 :
    CocycleGroup (orbitP5SelectedCocycle (orbitP5Index 2))
        (orbitP5SelectedCocycle_consistent (orbitP5Index 2)) ≃*
      CocycleGroup (orbitP5TargetCocycle 2)
        (orbitP5TargetCocycle_consistent 2) := by
  let e := Order16Table.orbitPathEquiv parent5Table coverageP5HBasis
    orbitP5ActionColumns orbitP5CorrectionColumns orbitP5_hbasis_cocycle
    orbitP5Aut orbitP5_action_linear [] (orbitP5RepresentativeCoeff 2)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent5Table coverageP5HBasis)
      orbitP5_path_endpoint_2))

theorem orbitP5_path_endpoint_3 :
    Order16Table.applyOrbitPath orbitP5ActionColumns []
      (orbitP5RepresentativeCoeff 3) = orbitP5TargetCoeff 3 := by
  decide +kernel

noncomputable def orbitP5NormalizeEquiv3 :
    CocycleGroup (orbitP5SelectedCocycle (orbitP5Index 3))
        (orbitP5SelectedCocycle_consistent (orbitP5Index 3)) ≃*
      CocycleGroup (orbitP5TargetCocycle 3)
        (orbitP5TargetCocycle_consistent 3) := by
  let e := Order16Table.orbitPathEquiv parent5Table coverageP5HBasis
    orbitP5ActionColumns orbitP5CorrectionColumns orbitP5_hbasis_cocycle
    orbitP5Aut orbitP5_action_linear [] (orbitP5RepresentativeCoeff 3)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent5Table coverageP5HBasis)
      orbitP5_path_endpoint_3))

theorem orbitP5_path_endpoint_4 :
    Order16Table.applyOrbitPath orbitP5ActionColumns []
      (orbitP5RepresentativeCoeff 4) = orbitP5TargetCoeff 4 := by
  decide +kernel

noncomputable def orbitP5NormalizeEquiv4 :
    CocycleGroup (orbitP5SelectedCocycle (orbitP5Index 4))
        (orbitP5SelectedCocycle_consistent (orbitP5Index 4)) ≃*
      CocycleGroup (orbitP5TargetCocycle 4)
        (orbitP5TargetCocycle_consistent 4) := by
  let e := Order16Table.orbitPathEquiv parent5Table coverageP5HBasis
    orbitP5ActionColumns orbitP5CorrectionColumns orbitP5_hbasis_cocycle
    orbitP5Aut orbitP5_action_linear [] (orbitP5RepresentativeCoeff 4)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent5Table coverageP5HBasis)
      orbitP5_path_endpoint_4))

theorem orbitP5_path_endpoint_5 :
    Order16Table.applyOrbitPath orbitP5ActionColumns [3]
      (orbitP5RepresentativeCoeff 5) = orbitP5TargetCoeff 5 := by
  decide +kernel

noncomputable def orbitP5NormalizeEquiv5 :
    CocycleGroup (orbitP5SelectedCocycle (orbitP5Index 5))
        (orbitP5SelectedCocycle_consistent (orbitP5Index 5)) ≃*
      CocycleGroup (orbitP5TargetCocycle 5)
        (orbitP5TargetCocycle_consistent 5) := by
  let e := Order16Table.orbitPathEquiv parent5Table coverageP5HBasis
    orbitP5ActionColumns orbitP5CorrectionColumns orbitP5_hbasis_cocycle
    orbitP5Aut orbitP5_action_linear [3] (orbitP5RepresentativeCoeff 5)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent5Table coverageP5HBasis)
      orbitP5_path_endpoint_5))

theorem orbitP5_path_endpoint_6 :
    Order16Table.applyOrbitPath orbitP5ActionColumns []
      (orbitP5RepresentativeCoeff 6) = orbitP5TargetCoeff 6 := by
  decide +kernel

noncomputable def orbitP5NormalizeEquiv6 :
    CocycleGroup (orbitP5SelectedCocycle (orbitP5Index 6))
        (orbitP5SelectedCocycle_consistent (orbitP5Index 6)) ≃*
      CocycleGroup (orbitP5TargetCocycle 6)
        (orbitP5TargetCocycle_consistent 6) := by
  let e := Order16Table.orbitPathEquiv parent5Table coverageP5HBasis
    orbitP5ActionColumns orbitP5CorrectionColumns orbitP5_hbasis_cocycle
    orbitP5Aut orbitP5_action_linear [] (orbitP5RepresentativeCoeff 6)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent5Table coverageP5HBasis)
      orbitP5_path_endpoint_6))

theorem orbitP5_path_endpoint_7 :
    Order16Table.applyOrbitPath orbitP5ActionColumns [3]
      (orbitP5RepresentativeCoeff 7) = orbitP5TargetCoeff 7 := by
  decide +kernel

noncomputable def orbitP5NormalizeEquiv7 :
    CocycleGroup (orbitP5SelectedCocycle (orbitP5Index 7))
        (orbitP5SelectedCocycle_consistent (orbitP5Index 7)) ≃*
      CocycleGroup (orbitP5TargetCocycle 7)
        (orbitP5TargetCocycle_consistent 7) := by
  let e := Order16Table.orbitPathEquiv parent5Table coverageP5HBasis
    orbitP5ActionColumns orbitP5CorrectionColumns orbitP5_hbasis_cocycle
    orbitP5Aut orbitP5_action_linear [3] (orbitP5RepresentativeCoeff 7)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent5Table coverageP5HBasis)
      orbitP5_path_endpoint_7))

end Smallgroups.UsefulTheorems.Order32Certificate
