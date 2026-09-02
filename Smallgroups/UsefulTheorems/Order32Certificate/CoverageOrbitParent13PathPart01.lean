/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent12PathIdentity

set_option maxRecDepth 100000

/-! Checked short orbit paths for parent 13; generated part 1. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP13_path_endpoint_0 :
    Order16Table.applyOrbitPath orbitP13ActionColumns []
      (orbitP13RepresentativeCoeff 0) = orbitP13TargetCoeff 0 := by
  decide +kernel

noncomputable def orbitP13NormalizeEquiv0 :
    CocycleGroup (orbitP13SelectedCocycle (orbitP13Index 0))
        (orbitP13SelectedCocycle_consistent (orbitP13Index 0)) ≃*
      CocycleGroup (orbitP13TargetCocycle 0)
        (orbitP13TargetCocycle_consistent 0) := by
  let e := Order16Table.orbitPathEquiv parent13Table coverageP13HBasis
    orbitP13ActionColumns orbitP13CorrectionColumns orbitP13_hbasis_cocycle
    orbitP13Aut orbitP13_action_linear [] (orbitP13RepresentativeCoeff 0)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent13Table coverageP13HBasis)
      orbitP13_path_endpoint_0))

theorem orbitP13_path_endpoint_1 :
    Order16Table.applyOrbitPath orbitP13ActionColumns []
      (orbitP13RepresentativeCoeff 1) = orbitP13TargetCoeff 1 := by
  decide +kernel

noncomputable def orbitP13NormalizeEquiv1 :
    CocycleGroup (orbitP13SelectedCocycle (orbitP13Index 1))
        (orbitP13SelectedCocycle_consistent (orbitP13Index 1)) ≃*
      CocycleGroup (orbitP13TargetCocycle 1)
        (orbitP13TargetCocycle_consistent 1) := by
  let e := Order16Table.orbitPathEquiv parent13Table coverageP13HBasis
    orbitP13ActionColumns orbitP13CorrectionColumns orbitP13_hbasis_cocycle
    orbitP13Aut orbitP13_action_linear [] (orbitP13RepresentativeCoeff 1)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent13Table coverageP13HBasis)
      orbitP13_path_endpoint_1))

theorem orbitP13_path_endpoint_2 :
    Order16Table.applyOrbitPath orbitP13ActionColumns []
      (orbitP13RepresentativeCoeff 2) = orbitP13TargetCoeff 2 := by
  decide +kernel

noncomputable def orbitP13NormalizeEquiv2 :
    CocycleGroup (orbitP13SelectedCocycle (orbitP13Index 2))
        (orbitP13SelectedCocycle_consistent (orbitP13Index 2)) ≃*
      CocycleGroup (orbitP13TargetCocycle 2)
        (orbitP13TargetCocycle_consistent 2) := by
  let e := Order16Table.orbitPathEquiv parent13Table coverageP13HBasis
    orbitP13ActionColumns orbitP13CorrectionColumns orbitP13_hbasis_cocycle
    orbitP13Aut orbitP13_action_linear [] (orbitP13RepresentativeCoeff 2)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent13Table coverageP13HBasis)
      orbitP13_path_endpoint_2))

theorem orbitP13_path_endpoint_3 :
    Order16Table.applyOrbitPath orbitP13ActionColumns []
      (orbitP13RepresentativeCoeff 3) = orbitP13TargetCoeff 3 := by
  decide +kernel

noncomputable def orbitP13NormalizeEquiv3 :
    CocycleGroup (orbitP13SelectedCocycle (orbitP13Index 3))
        (orbitP13SelectedCocycle_consistent (orbitP13Index 3)) ≃*
      CocycleGroup (orbitP13TargetCocycle 3)
        (orbitP13TargetCocycle_consistent 3) := by
  let e := Order16Table.orbitPathEquiv parent13Table coverageP13HBasis
    orbitP13ActionColumns orbitP13CorrectionColumns orbitP13_hbasis_cocycle
    orbitP13Aut orbitP13_action_linear [] (orbitP13RepresentativeCoeff 3)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent13Table coverageP13HBasis)
      orbitP13_path_endpoint_3))

theorem orbitP13_path_endpoint_4 :
    Order16Table.applyOrbitPath orbitP13ActionColumns []
      (orbitP13RepresentativeCoeff 4) = orbitP13TargetCoeff 4 := by
  decide +kernel

noncomputable def orbitP13NormalizeEquiv4 :
    CocycleGroup (orbitP13SelectedCocycle (orbitP13Index 4))
        (orbitP13SelectedCocycle_consistent (orbitP13Index 4)) ≃*
      CocycleGroup (orbitP13TargetCocycle 4)
        (orbitP13TargetCocycle_consistent 4) := by
  let e := Order16Table.orbitPathEquiv parent13Table coverageP13HBasis
    orbitP13ActionColumns orbitP13CorrectionColumns orbitP13_hbasis_cocycle
    orbitP13Aut orbitP13_action_linear [] (orbitP13RepresentativeCoeff 4)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent13Table coverageP13HBasis)
      orbitP13_path_endpoint_4))

theorem orbitP13_path_endpoint_5 :
    Order16Table.applyOrbitPath orbitP13ActionColumns [0, 1]
      (orbitP13RepresentativeCoeff 5) = orbitP13TargetCoeff 5 := by
  decide +kernel

noncomputable def orbitP13NormalizeEquiv5 :
    CocycleGroup (orbitP13SelectedCocycle (orbitP13Index 5))
        (orbitP13SelectedCocycle_consistent (orbitP13Index 5)) ≃*
      CocycleGroup (orbitP13TargetCocycle 5)
        (orbitP13TargetCocycle_consistent 5) := by
  let e := Order16Table.orbitPathEquiv parent13Table coverageP13HBasis
    orbitP13ActionColumns orbitP13CorrectionColumns orbitP13_hbasis_cocycle
    orbitP13Aut orbitP13_action_linear [0, 1] (orbitP13RepresentativeCoeff 5)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent13Table coverageP13HBasis)
      orbitP13_path_endpoint_5))

theorem orbitP13_path_endpoint_6 :
    Order16Table.applyOrbitPath orbitP13ActionColumns [0]
      (orbitP13RepresentativeCoeff 6) = orbitP13TargetCoeff 6 := by
  decide +kernel

noncomputable def orbitP13NormalizeEquiv6 :
    CocycleGroup (orbitP13SelectedCocycle (orbitP13Index 6))
        (orbitP13SelectedCocycle_consistent (orbitP13Index 6)) ≃*
      CocycleGroup (orbitP13TargetCocycle 6)
        (orbitP13TargetCocycle_consistent 6) := by
  let e := Order16Table.orbitPathEquiv parent13Table coverageP13HBasis
    orbitP13ActionColumns orbitP13CorrectionColumns orbitP13_hbasis_cocycle
    orbitP13Aut orbitP13_action_linear [0] (orbitP13RepresentativeCoeff 6)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent13Table coverageP13HBasis)
      orbitP13_path_endpoint_6))

theorem orbitP13_path_endpoint_7 :
    Order16Table.applyOrbitPath orbitP13ActionColumns [0]
      (orbitP13RepresentativeCoeff 7) = orbitP13TargetCoeff 7 := by
  decide +kernel

noncomputable def orbitP13NormalizeEquiv7 :
    CocycleGroup (orbitP13SelectedCocycle (orbitP13Index 7))
        (orbitP13SelectedCocycle_consistent (orbitP13Index 7)) ≃*
      CocycleGroup (orbitP13TargetCocycle 7)
        (orbitP13TargetCocycle_consistent 7) := by
  let e := Order16Table.orbitPathEquiv parent13Table coverageP13HBasis
    orbitP13ActionColumns orbitP13CorrectionColumns orbitP13_hbasis_cocycle
    orbitP13Aut orbitP13_action_linear [0] (orbitP13RepresentativeCoeff 7)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent13Table coverageP13HBasis)
      orbitP13_path_endpoint_7))

theorem orbitP13_path_endpoint_8 :
    Order16Table.applyOrbitPath orbitP13ActionColumns []
      (orbitP13RepresentativeCoeff 8) = orbitP13TargetCoeff 8 := by
  decide +kernel

noncomputable def orbitP13NormalizeEquiv8 :
    CocycleGroup (orbitP13SelectedCocycle (orbitP13Index 8))
        (orbitP13SelectedCocycle_consistent (orbitP13Index 8)) ≃*
      CocycleGroup (orbitP13TargetCocycle 8)
        (orbitP13TargetCocycle_consistent 8) := by
  let e := Order16Table.orbitPathEquiv parent13Table coverageP13HBasis
    orbitP13ActionColumns orbitP13CorrectionColumns orbitP13_hbasis_cocycle
    orbitP13Aut orbitP13_action_linear [] (orbitP13RepresentativeCoeff 8)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent13Table coverageP13HBasis)
      orbitP13_path_endpoint_8))

theorem orbitP13_path_endpoint_9 :
    Order16Table.applyOrbitPath orbitP13ActionColumns [1, 0]
      (orbitP13RepresentativeCoeff 9) = orbitP13TargetCoeff 9 := by
  decide +kernel

noncomputable def orbitP13NormalizeEquiv9 :
    CocycleGroup (orbitP13SelectedCocycle (orbitP13Index 9))
        (orbitP13SelectedCocycle_consistent (orbitP13Index 9)) ≃*
      CocycleGroup (orbitP13TargetCocycle 9)
        (orbitP13TargetCocycle_consistent 9) := by
  let e := Order16Table.orbitPathEquiv parent13Table coverageP13HBasis
    orbitP13ActionColumns orbitP13CorrectionColumns orbitP13_hbasis_cocycle
    orbitP13Aut orbitP13_action_linear [1, 0] (orbitP13RepresentativeCoeff 9)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent13Table coverageP13HBasis)
      orbitP13_path_endpoint_9))

theorem orbitP13_path_endpoint_10 :
    Order16Table.applyOrbitPath orbitP13ActionColumns []
      (orbitP13RepresentativeCoeff 10) = orbitP13TargetCoeff 10 := by
  decide +kernel

noncomputable def orbitP13NormalizeEquiv10 :
    CocycleGroup (orbitP13SelectedCocycle (orbitP13Index 10))
        (orbitP13SelectedCocycle_consistent (orbitP13Index 10)) ≃*
      CocycleGroup (orbitP13TargetCocycle 10)
        (orbitP13TargetCocycle_consistent 10) := by
  let e := Order16Table.orbitPathEquiv parent13Table coverageP13HBasis
    orbitP13ActionColumns orbitP13CorrectionColumns orbitP13_hbasis_cocycle
    orbitP13Aut orbitP13_action_linear [] (orbitP13RepresentativeCoeff 10)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent13Table coverageP13HBasis)
      orbitP13_path_endpoint_10))

theorem orbitP13_path_endpoint_11 :
    Order16Table.applyOrbitPath orbitP13ActionColumns [1, 0]
      (orbitP13RepresentativeCoeff 11) = orbitP13TargetCoeff 11 := by
  decide +kernel

noncomputable def orbitP13NormalizeEquiv11 :
    CocycleGroup (orbitP13SelectedCocycle (orbitP13Index 11))
        (orbitP13SelectedCocycle_consistent (orbitP13Index 11)) ≃*
      CocycleGroup (orbitP13TargetCocycle 11)
        (orbitP13TargetCocycle_consistent 11) := by
  let e := Order16Table.orbitPathEquiv parent13Table coverageP13HBasis
    orbitP13ActionColumns orbitP13CorrectionColumns orbitP13_hbasis_cocycle
    orbitP13Aut orbitP13_action_linear [1, 0] (orbitP13RepresentativeCoeff 11)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent13Table coverageP13HBasis)
      orbitP13_path_endpoint_11))

theorem orbitP13_path_endpoint_12 :
    Order16Table.applyOrbitPath orbitP13ActionColumns [1, 0]
      (orbitP13RepresentativeCoeff 12) = orbitP13TargetCoeff 12 := by
  decide +kernel

noncomputable def orbitP13NormalizeEquiv12 :
    CocycleGroup (orbitP13SelectedCocycle (orbitP13Index 12))
        (orbitP13SelectedCocycle_consistent (orbitP13Index 12)) ≃*
      CocycleGroup (orbitP13TargetCocycle 12)
        (orbitP13TargetCocycle_consistent 12) := by
  let e := Order16Table.orbitPathEquiv parent13Table coverageP13HBasis
    orbitP13ActionColumns orbitP13CorrectionColumns orbitP13_hbasis_cocycle
    orbitP13Aut orbitP13_action_linear [1, 0] (orbitP13RepresentativeCoeff 12)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent13Table coverageP13HBasis)
      orbitP13_path_endpoint_12))

theorem orbitP13_path_endpoint_13 :
    Order16Table.applyOrbitPath orbitP13ActionColumns []
      (orbitP13RepresentativeCoeff 13) = orbitP13TargetCoeff 13 := by
  decide +kernel

noncomputable def orbitP13NormalizeEquiv13 :
    CocycleGroup (orbitP13SelectedCocycle (orbitP13Index 13))
        (orbitP13SelectedCocycle_consistent (orbitP13Index 13)) ≃*
      CocycleGroup (orbitP13TargetCocycle 13)
        (orbitP13TargetCocycle_consistent 13) := by
  let e := Order16Table.orbitPathEquiv parent13Table coverageP13HBasis
    orbitP13ActionColumns orbitP13CorrectionColumns orbitP13_hbasis_cocycle
    orbitP13Aut orbitP13_action_linear [] (orbitP13RepresentativeCoeff 13)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent13Table coverageP13HBasis)
      orbitP13_path_endpoint_13))

theorem orbitP13_path_endpoint_14 :
    Order16Table.applyOrbitPath orbitP13ActionColumns [1, 1]
      (orbitP13RepresentativeCoeff 14) = orbitP13TargetCoeff 14 := by
  decide +kernel

noncomputable def orbitP13NormalizeEquiv14 :
    CocycleGroup (orbitP13SelectedCocycle (orbitP13Index 14))
        (orbitP13SelectedCocycle_consistent (orbitP13Index 14)) ≃*
      CocycleGroup (orbitP13TargetCocycle 14)
        (orbitP13TargetCocycle_consistent 14) := by
  let e := Order16Table.orbitPathEquiv parent13Table coverageP13HBasis
    orbitP13ActionColumns orbitP13CorrectionColumns orbitP13_hbasis_cocycle
    orbitP13Aut orbitP13_action_linear [1, 1] (orbitP13RepresentativeCoeff 14)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent13Table coverageP13HBasis)
      orbitP13_path_endpoint_14))

theorem orbitP13_path_endpoint_15 :
    Order16Table.applyOrbitPath orbitP13ActionColumns [1, 0]
      (orbitP13RepresentativeCoeff 15) = orbitP13TargetCoeff 15 := by
  decide +kernel

noncomputable def orbitP13NormalizeEquiv15 :
    CocycleGroup (orbitP13SelectedCocycle (orbitP13Index 15))
        (orbitP13SelectedCocycle_consistent (orbitP13Index 15)) ≃*
      CocycleGroup (orbitP13TargetCocycle 15)
        (orbitP13TargetCocycle_consistent 15) := by
  let e := Order16Table.orbitPathEquiv parent13Table coverageP13HBasis
    orbitP13ActionColumns orbitP13CorrectionColumns orbitP13_hbasis_cocycle
    orbitP13Aut orbitP13_action_linear [1, 0] (orbitP13RepresentativeCoeff 15)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent13Table coverageP13HBasis)
      orbitP13_path_endpoint_15))

end Smallgroups.UsefulTheorems.Order32Certificate
