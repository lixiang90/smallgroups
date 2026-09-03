/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent03Core

set_option maxRecDepth 100000

/-! Checked short orbit paths for parent 3; generated part 1. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP3_path_endpoint_0 :
    Order16Table.applyOrbitPath orbitP3ActionColumns []
      (orbitP3RepresentativeCoeff 0) = orbitP3TargetCoeff 0 := by
  decide +kernel

noncomputable def orbitP3NormalizeEquiv0 :
    CocycleGroup (orbitP3SelectedCocycle (orbitP3Index 0))
        (orbitP3SelectedCocycle_consistent (orbitP3Index 0)) ≃*
      CocycleGroup (orbitP3TargetCocycle 0)
        (orbitP3TargetCocycle_consistent 0) := by
  let e := Order16Table.orbitPathEquiv parent3Table coverageP3HBasis
    orbitP3ActionColumns orbitP3CorrectionColumns orbitP3_hbasis_cocycle
    orbitP3Aut orbitP3_action_linear [] (orbitP3RepresentativeCoeff 0)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent3Table coverageP3HBasis)
      orbitP3_path_endpoint_0))

theorem orbitP3_path_endpoint_1 :
    Order16Table.applyOrbitPath orbitP3ActionColumns []
      (orbitP3RepresentativeCoeff 1) = orbitP3TargetCoeff 1 := by
  decide +kernel

noncomputable def orbitP3NormalizeEquiv1 :
    CocycleGroup (orbitP3SelectedCocycle (orbitP3Index 1))
        (orbitP3SelectedCocycle_consistent (orbitP3Index 1)) ≃*
      CocycleGroup (orbitP3TargetCocycle 1)
        (orbitP3TargetCocycle_consistent 1) := by
  let e := Order16Table.orbitPathEquiv parent3Table coverageP3HBasis
    orbitP3ActionColumns orbitP3CorrectionColumns orbitP3_hbasis_cocycle
    orbitP3Aut orbitP3_action_linear [] (orbitP3RepresentativeCoeff 1)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent3Table coverageP3HBasis)
      orbitP3_path_endpoint_1))

theorem orbitP3_path_endpoint_2 :
    Order16Table.applyOrbitPath orbitP3ActionColumns []
      (orbitP3RepresentativeCoeff 2) = orbitP3TargetCoeff 2 := by
  decide +kernel

noncomputable def orbitP3NormalizeEquiv2 :
    CocycleGroup (orbitP3SelectedCocycle (orbitP3Index 2))
        (orbitP3SelectedCocycle_consistent (orbitP3Index 2)) ≃*
      CocycleGroup (orbitP3TargetCocycle 2)
        (orbitP3TargetCocycle_consistent 2) := by
  let e := Order16Table.orbitPathEquiv parent3Table coverageP3HBasis
    orbitP3ActionColumns orbitP3CorrectionColumns orbitP3_hbasis_cocycle
    orbitP3Aut orbitP3_action_linear [] (orbitP3RepresentativeCoeff 2)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent3Table coverageP3HBasis)
      orbitP3_path_endpoint_2))

theorem orbitP3_path_endpoint_3 :
    Order16Table.applyOrbitPath orbitP3ActionColumns []
      (orbitP3RepresentativeCoeff 3) = orbitP3TargetCoeff 3 := by
  decide +kernel

noncomputable def orbitP3NormalizeEquiv3 :
    CocycleGroup (orbitP3SelectedCocycle (orbitP3Index 3))
        (orbitP3SelectedCocycle_consistent (orbitP3Index 3)) ≃*
      CocycleGroup (orbitP3TargetCocycle 3)
        (orbitP3TargetCocycle_consistent 3) := by
  let e := Order16Table.orbitPathEquiv parent3Table coverageP3HBasis
    orbitP3ActionColumns orbitP3CorrectionColumns orbitP3_hbasis_cocycle
    orbitP3Aut orbitP3_action_linear [] (orbitP3RepresentativeCoeff 3)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent3Table coverageP3HBasis)
      orbitP3_path_endpoint_3))

theorem orbitP3_path_endpoint_4 :
    Order16Table.applyOrbitPath orbitP3ActionColumns [4]
      (orbitP3RepresentativeCoeff 4) = orbitP3TargetCoeff 4 := by
  decide +kernel

noncomputable def orbitP3NormalizeEquiv4 :
    CocycleGroup (orbitP3SelectedCocycle (orbitP3Index 4))
        (orbitP3SelectedCocycle_consistent (orbitP3Index 4)) ≃*
      CocycleGroup (orbitP3TargetCocycle 4)
        (orbitP3TargetCocycle_consistent 4) := by
  let e := Order16Table.orbitPathEquiv parent3Table coverageP3HBasis
    orbitP3ActionColumns orbitP3CorrectionColumns orbitP3_hbasis_cocycle
    orbitP3Aut orbitP3_action_linear [4] (orbitP3RepresentativeCoeff 4)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent3Table coverageP3HBasis)
      orbitP3_path_endpoint_4))

theorem orbitP3_path_endpoint_5 :
    Order16Table.applyOrbitPath orbitP3ActionColumns [4]
      (orbitP3RepresentativeCoeff 5) = orbitP3TargetCoeff 5 := by
  decide +kernel

noncomputable def orbitP3NormalizeEquiv5 :
    CocycleGroup (orbitP3SelectedCocycle (orbitP3Index 5))
        (orbitP3SelectedCocycle_consistent (orbitP3Index 5)) ≃*
      CocycleGroup (orbitP3TargetCocycle 5)
        (orbitP3TargetCocycle_consistent 5) := by
  let e := Order16Table.orbitPathEquiv parent3Table coverageP3HBasis
    orbitP3ActionColumns orbitP3CorrectionColumns orbitP3_hbasis_cocycle
    orbitP3Aut orbitP3_action_linear [4] (orbitP3RepresentativeCoeff 5)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent3Table coverageP3HBasis)
      orbitP3_path_endpoint_5))

theorem orbitP3_path_endpoint_6 :
    Order16Table.applyOrbitPath orbitP3ActionColumns []
      (orbitP3RepresentativeCoeff 6) = orbitP3TargetCoeff 6 := by
  decide +kernel

noncomputable def orbitP3NormalizeEquiv6 :
    CocycleGroup (orbitP3SelectedCocycle (orbitP3Index 6))
        (orbitP3SelectedCocycle_consistent (orbitP3Index 6)) ≃*
      CocycleGroup (orbitP3TargetCocycle 6)
        (orbitP3TargetCocycle_consistent 6) := by
  let e := Order16Table.orbitPathEquiv parent3Table coverageP3HBasis
    orbitP3ActionColumns orbitP3CorrectionColumns orbitP3_hbasis_cocycle
    orbitP3Aut orbitP3_action_linear [] (orbitP3RepresentativeCoeff 6)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent3Table coverageP3HBasis)
      orbitP3_path_endpoint_6))

theorem orbitP3_path_endpoint_7 :
    Order16Table.applyOrbitPath orbitP3ActionColumns []
      (orbitP3RepresentativeCoeff 7) = orbitP3TargetCoeff 7 := by
  decide +kernel

noncomputable def orbitP3NormalizeEquiv7 :
    CocycleGroup (orbitP3SelectedCocycle (orbitP3Index 7))
        (orbitP3SelectedCocycle_consistent (orbitP3Index 7)) ≃*
      CocycleGroup (orbitP3TargetCocycle 7)
        (orbitP3TargetCocycle_consistent 7) := by
  let e := Order16Table.orbitPathEquiv parent3Table coverageP3HBasis
    orbitP3ActionColumns orbitP3CorrectionColumns orbitP3_hbasis_cocycle
    orbitP3Aut orbitP3_action_linear [] (orbitP3RepresentativeCoeff 7)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent3Table coverageP3HBasis)
      orbitP3_path_endpoint_7))

theorem orbitP3_path_endpoint_8 :
    Order16Table.applyOrbitPath orbitP3ActionColumns [0]
      (orbitP3RepresentativeCoeff 8) = orbitP3TargetCoeff 8 := by
  decide +kernel

noncomputable def orbitP3NormalizeEquiv8 :
    CocycleGroup (orbitP3SelectedCocycle (orbitP3Index 8))
        (orbitP3SelectedCocycle_consistent (orbitP3Index 8)) ≃*
      CocycleGroup (orbitP3TargetCocycle 8)
        (orbitP3TargetCocycle_consistent 8) := by
  let e := Order16Table.orbitPathEquiv parent3Table coverageP3HBasis
    orbitP3ActionColumns orbitP3CorrectionColumns orbitP3_hbasis_cocycle
    orbitP3Aut orbitP3_action_linear [0] (orbitP3RepresentativeCoeff 8)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent3Table coverageP3HBasis)
      orbitP3_path_endpoint_8))

theorem orbitP3_path_endpoint_9 :
    Order16Table.applyOrbitPath orbitP3ActionColumns []
      (orbitP3RepresentativeCoeff 9) = orbitP3TargetCoeff 9 := by
  decide +kernel

noncomputable def orbitP3NormalizeEquiv9 :
    CocycleGroup (orbitP3SelectedCocycle (orbitP3Index 9))
        (orbitP3SelectedCocycle_consistent (orbitP3Index 9)) ≃*
      CocycleGroup (orbitP3TargetCocycle 9)
        (orbitP3TargetCocycle_consistent 9) := by
  let e := Order16Table.orbitPathEquiv parent3Table coverageP3HBasis
    orbitP3ActionColumns orbitP3CorrectionColumns orbitP3_hbasis_cocycle
    orbitP3Aut orbitP3_action_linear [] (orbitP3RepresentativeCoeff 9)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent3Table coverageP3HBasis)
      orbitP3_path_endpoint_9))

theorem orbitP3_path_endpoint_10 :
    Order16Table.applyOrbitPath orbitP3ActionColumns []
      (orbitP3RepresentativeCoeff 10) = orbitP3TargetCoeff 10 := by
  decide +kernel

noncomputable def orbitP3NormalizeEquiv10 :
    CocycleGroup (orbitP3SelectedCocycle (orbitP3Index 10))
        (orbitP3SelectedCocycle_consistent (orbitP3Index 10)) ≃*
      CocycleGroup (orbitP3TargetCocycle 10)
        (orbitP3TargetCocycle_consistent 10) := by
  let e := Order16Table.orbitPathEquiv parent3Table coverageP3HBasis
    orbitP3ActionColumns orbitP3CorrectionColumns orbitP3_hbasis_cocycle
    orbitP3Aut orbitP3_action_linear [] (orbitP3RepresentativeCoeff 10)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent3Table coverageP3HBasis)
      orbitP3_path_endpoint_10))

theorem orbitP3_path_endpoint_11 :
    Order16Table.applyOrbitPath orbitP3ActionColumns [0]
      (orbitP3RepresentativeCoeff 11) = orbitP3TargetCoeff 11 := by
  decide +kernel

noncomputable def orbitP3NormalizeEquiv11 :
    CocycleGroup (orbitP3SelectedCocycle (orbitP3Index 11))
        (orbitP3SelectedCocycle_consistent (orbitP3Index 11)) ≃*
      CocycleGroup (orbitP3TargetCocycle 11)
        (orbitP3TargetCocycle_consistent 11) := by
  let e := Order16Table.orbitPathEquiv parent3Table coverageP3HBasis
    orbitP3ActionColumns orbitP3CorrectionColumns orbitP3_hbasis_cocycle
    orbitP3Aut orbitP3_action_linear [0] (orbitP3RepresentativeCoeff 11)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent3Table coverageP3HBasis)
      orbitP3_path_endpoint_11))

theorem orbitP3_path_endpoint_12 :
    Order16Table.applyOrbitPath orbitP3ActionColumns [4]
      (orbitP3RepresentativeCoeff 12) = orbitP3TargetCoeff 12 := by
  decide +kernel

noncomputable def orbitP3NormalizeEquiv12 :
    CocycleGroup (orbitP3SelectedCocycle (orbitP3Index 12))
        (orbitP3SelectedCocycle_consistent (orbitP3Index 12)) ≃*
      CocycleGroup (orbitP3TargetCocycle 12)
        (orbitP3TargetCocycle_consistent 12) := by
  let e := Order16Table.orbitPathEquiv parent3Table coverageP3HBasis
    orbitP3ActionColumns orbitP3CorrectionColumns orbitP3_hbasis_cocycle
    orbitP3Aut orbitP3_action_linear [4] (orbitP3RepresentativeCoeff 12)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent3Table coverageP3HBasis)
      orbitP3_path_endpoint_12))

theorem orbitP3_path_endpoint_13 :
    Order16Table.applyOrbitPath orbitP3ActionColumns [0, 4]
      (orbitP3RepresentativeCoeff 13) = orbitP3TargetCoeff 13 := by
  decide +kernel

noncomputable def orbitP3NormalizeEquiv13 :
    CocycleGroup (orbitP3SelectedCocycle (orbitP3Index 13))
        (orbitP3SelectedCocycle_consistent (orbitP3Index 13)) ≃*
      CocycleGroup (orbitP3TargetCocycle 13)
        (orbitP3TargetCocycle_consistent 13) := by
  let e := Order16Table.orbitPathEquiv parent3Table coverageP3HBasis
    orbitP3ActionColumns orbitP3CorrectionColumns orbitP3_hbasis_cocycle
    orbitP3Aut orbitP3_action_linear [0, 4] (orbitP3RepresentativeCoeff 13)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent3Table coverageP3HBasis)
      orbitP3_path_endpoint_13))

theorem orbitP3_path_endpoint_14 :
    Order16Table.applyOrbitPath orbitP3ActionColumns [0]
      (orbitP3RepresentativeCoeff 14) = orbitP3TargetCoeff 14 := by
  decide +kernel

noncomputable def orbitP3NormalizeEquiv14 :
    CocycleGroup (orbitP3SelectedCocycle (orbitP3Index 14))
        (orbitP3SelectedCocycle_consistent (orbitP3Index 14)) ≃*
      CocycleGroup (orbitP3TargetCocycle 14)
        (orbitP3TargetCocycle_consistent 14) := by
  let e := Order16Table.orbitPathEquiv parent3Table coverageP3HBasis
    orbitP3ActionColumns orbitP3CorrectionColumns orbitP3_hbasis_cocycle
    orbitP3Aut orbitP3_action_linear [0] (orbitP3RepresentativeCoeff 14)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent3Table coverageP3HBasis)
      orbitP3_path_endpoint_14))

theorem orbitP3_path_endpoint_15 :
    Order16Table.applyOrbitPath orbitP3ActionColumns []
      (orbitP3RepresentativeCoeff 15) = orbitP3TargetCoeff 15 := by
  decide +kernel

noncomputable def orbitP3NormalizeEquiv15 :
    CocycleGroup (orbitP3SelectedCocycle (orbitP3Index 15))
        (orbitP3SelectedCocycle_consistent (orbitP3Index 15)) ≃*
      CocycleGroup (orbitP3TargetCocycle 15)
        (orbitP3TargetCocycle_consistent 15) := by
  let e := Order16Table.orbitPathEquiv parent3Table coverageP3HBasis
    orbitP3ActionColumns orbitP3CorrectionColumns orbitP3_hbasis_cocycle
    orbitP3Aut orbitP3_action_linear [] (orbitP3RepresentativeCoeff 15)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent3Table coverageP3HBasis)
      orbitP3_path_endpoint_15))

end Smallgroups.UsefulTheorems.Order32Certificate
