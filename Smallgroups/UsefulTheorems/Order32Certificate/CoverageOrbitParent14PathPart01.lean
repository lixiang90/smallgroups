/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13PathPart02

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 1. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_0 :
    Order16Table.applyOrbitPath orbitP14ActionColumns []
      (orbitP14RepresentativeCoeff 0) = orbitP14TargetCoeff 0 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv0 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 0))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 0)) ≃*
      CocycleGroup (orbitP14TargetCocycle 0)
        (orbitP14TargetCocycle_consistent 0) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [] (orbitP14RepresentativeCoeff 0)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_0))

theorem orbitP14_path_endpoint_1 :
    Order16Table.applyOrbitPath orbitP14ActionColumns []
      (orbitP14RepresentativeCoeff 1) = orbitP14TargetCoeff 1 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv1 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 1))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 1)) ≃*
      CocycleGroup (orbitP14TargetCocycle 1)
        (orbitP14TargetCocycle_consistent 1) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [] (orbitP14RepresentativeCoeff 1)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_1))

theorem orbitP14_path_endpoint_2 :
    Order16Table.applyOrbitPath orbitP14ActionColumns []
      (orbitP14RepresentativeCoeff 2) = orbitP14TargetCoeff 2 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv2 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 2))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 2)) ≃*
      CocycleGroup (orbitP14TargetCocycle 2)
        (orbitP14TargetCocycle_consistent 2) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [] (orbitP14RepresentativeCoeff 2)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_2))

theorem orbitP14_path_endpoint_3 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1]
      (orbitP14RepresentativeCoeff 3) = orbitP14TargetCoeff 3 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv3 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 3))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 3)) ≃*
      CocycleGroup (orbitP14TargetCocycle 3)
        (orbitP14TargetCocycle_consistent 3) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1] (orbitP14RepresentativeCoeff 3)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_3))

theorem orbitP14_path_endpoint_4 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0]
      (orbitP14RepresentativeCoeff 4) = orbitP14TargetCoeff 4 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv4 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 4))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 4)) ≃*
      CocycleGroup (orbitP14TargetCocycle 4)
        (orbitP14TargetCocycle_consistent 4) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0] (orbitP14RepresentativeCoeff 4)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_4))

theorem orbitP14_path_endpoint_5 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 0]
      (orbitP14RepresentativeCoeff 5) = orbitP14TargetCoeff 5 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv5 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 5))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 5)) ≃*
      CocycleGroup (orbitP14TargetCocycle 5)
        (orbitP14TargetCocycle_consistent 5) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 0] (orbitP14RepresentativeCoeff 5)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_5))

theorem orbitP14_path_endpoint_6 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 6) = orbitP14TargetCoeff 6 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv6 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 6))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 6)) ≃*
      CocycleGroup (orbitP14TargetCocycle 6)
        (orbitP14TargetCocycle_consistent 6) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 6)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_6))

theorem orbitP14_path_endpoint_7 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 1, 1, 2]
      (orbitP14RepresentativeCoeff 7) = orbitP14TargetCoeff 7 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv7 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 7))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 7)) ≃*
      CocycleGroup (orbitP14TargetCocycle 7)
        (orbitP14TargetCocycle_consistent 7) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 1, 1, 2] (orbitP14RepresentativeCoeff 7)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_7))

theorem orbitP14_path_endpoint_8 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2]
      (orbitP14RepresentativeCoeff 8) = orbitP14TargetCoeff 8 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv8 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 8))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 8)) ≃*
      CocycleGroup (orbitP14TargetCocycle 8)
        (orbitP14TargetCocycle_consistent 8) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2] (orbitP14RepresentativeCoeff 8)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_8))

theorem orbitP14_path_endpoint_9 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2]
      (orbitP14RepresentativeCoeff 9) = orbitP14TargetCoeff 9 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv9 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 9))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 9)) ≃*
      CocycleGroup (orbitP14TargetCocycle 9)
        (orbitP14TargetCocycle_consistent 9) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2] (orbitP14RepresentativeCoeff 9)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_9))

theorem orbitP14_path_endpoint_10 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 0, 1]
      (orbitP14RepresentativeCoeff 10) = orbitP14TargetCoeff 10 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv10 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 10))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 10)) ≃*
      CocycleGroup (orbitP14TargetCocycle 10)
        (orbitP14TargetCocycle_consistent 10) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 0, 1] (orbitP14RepresentativeCoeff 10)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_10))

theorem orbitP14_path_endpoint_11 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 2, 1]
      (orbitP14RepresentativeCoeff 11) = orbitP14TargetCoeff 11 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv11 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 11))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 11)) ≃*
      CocycleGroup (orbitP14TargetCocycle 11)
        (orbitP14TargetCocycle_consistent 11) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 2, 1] (orbitP14RepresentativeCoeff 11)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_11))

theorem orbitP14_path_endpoint_12 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 1, 1]
      (orbitP14RepresentativeCoeff 12) = orbitP14TargetCoeff 12 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv12 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 12))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 12)) ≃*
      CocycleGroup (orbitP14TargetCocycle 12)
        (orbitP14TargetCocycle_consistent 12) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 1, 1] (orbitP14RepresentativeCoeff 12)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_12))

theorem orbitP14_path_endpoint_13 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 2, 1, 0]
      (orbitP14RepresentativeCoeff 13) = orbitP14TargetCoeff 13 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv13 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 13))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 13)) ≃*
      CocycleGroup (orbitP14TargetCocycle 13)
        (orbitP14TargetCocycle_consistent 13) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 2, 1, 0] (orbitP14RepresentativeCoeff 13)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_13))

theorem orbitP14_path_endpoint_14 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 0, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 14) = orbitP14TargetCoeff 14 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv14 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 14))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 14)) ≃*
      CocycleGroup (orbitP14TargetCocycle 14)
        (orbitP14TargetCocycle_consistent 14) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 0, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 14)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_14))

theorem orbitP14_path_endpoint_15 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 15) = orbitP14TargetCoeff 15 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv15 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 15))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 15)) ≃*
      CocycleGroup (orbitP14TargetCocycle 15)
        (orbitP14TargetCocycle_consistent 15) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 15)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_15))

end Smallgroups.UsefulTheorems.Order32Certificate
