/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent12Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11PathPart04

set_option maxRecDepth 100000

/-! Checked short orbit paths for parent 12; generated part 1. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP12_path_endpoint_0 :
    Order16Table.applyOrbitPath orbitP12ActionColumns []
      (orbitP12RepresentativeCoeff 0) = orbitP12TargetCoeff 0 := by
  decide +kernel

noncomputable def orbitP12NormalizeEquiv0 :
    CocycleGroup (orbitP12SelectedCocycle (orbitP12Index 0))
        (orbitP12SelectedCocycle_consistent (orbitP12Index 0)) ≃*
      CocycleGroup (orbitP12TargetCocycle 0)
        (orbitP12TargetCocycle_consistent 0) := by
  let e := Order16Table.orbitPathEquiv parent12Table coverageP12HBasis
    orbitP12ActionColumns orbitP12CorrectionColumns orbitP12_hbasis_cocycle
    orbitP12Aut orbitP12_action_linear [] (orbitP12RepresentativeCoeff 0)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent12Table coverageP12HBasis)
      orbitP12_path_endpoint_0))

theorem orbitP12_path_endpoint_1 :
    Order16Table.applyOrbitPath orbitP12ActionColumns []
      (orbitP12RepresentativeCoeff 1) = orbitP12TargetCoeff 1 := by
  decide +kernel

noncomputable def orbitP12NormalizeEquiv1 :
    CocycleGroup (orbitP12SelectedCocycle (orbitP12Index 1))
        (orbitP12SelectedCocycle_consistent (orbitP12Index 1)) ≃*
      CocycleGroup (orbitP12TargetCocycle 1)
        (orbitP12TargetCocycle_consistent 1) := by
  let e := Order16Table.orbitPathEquiv parent12Table coverageP12HBasis
    orbitP12ActionColumns orbitP12CorrectionColumns orbitP12_hbasis_cocycle
    orbitP12Aut orbitP12_action_linear [] (orbitP12RepresentativeCoeff 1)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent12Table coverageP12HBasis)
      orbitP12_path_endpoint_1))

theorem orbitP12_path_endpoint_2 :
    Order16Table.applyOrbitPath orbitP12ActionColumns []
      (orbitP12RepresentativeCoeff 2) = orbitP12TargetCoeff 2 := by
  decide +kernel

noncomputable def orbitP12NormalizeEquiv2 :
    CocycleGroup (orbitP12SelectedCocycle (orbitP12Index 2))
        (orbitP12SelectedCocycle_consistent (orbitP12Index 2)) ≃*
      CocycleGroup (orbitP12TargetCocycle 2)
        (orbitP12TargetCocycle_consistent 2) := by
  let e := Order16Table.orbitPathEquiv parent12Table coverageP12HBasis
    orbitP12ActionColumns orbitP12CorrectionColumns orbitP12_hbasis_cocycle
    orbitP12Aut orbitP12_action_linear [] (orbitP12RepresentativeCoeff 2)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent12Table coverageP12HBasis)
      orbitP12_path_endpoint_2))

theorem orbitP12_path_endpoint_3 :
    Order16Table.applyOrbitPath orbitP12ActionColumns []
      (orbitP12RepresentativeCoeff 3) = orbitP12TargetCoeff 3 := by
  decide +kernel

noncomputable def orbitP12NormalizeEquiv3 :
    CocycleGroup (orbitP12SelectedCocycle (orbitP12Index 3))
        (orbitP12SelectedCocycle_consistent (orbitP12Index 3)) ≃*
      CocycleGroup (orbitP12TargetCocycle 3)
        (orbitP12TargetCocycle_consistent 3) := by
  let e := Order16Table.orbitPathEquiv parent12Table coverageP12HBasis
    orbitP12ActionColumns orbitP12CorrectionColumns orbitP12_hbasis_cocycle
    orbitP12Aut orbitP12_action_linear [] (orbitP12RepresentativeCoeff 3)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent12Table coverageP12HBasis)
      orbitP12_path_endpoint_3))

theorem orbitP12_path_endpoint_4 :
    Order16Table.applyOrbitPath orbitP12ActionColumns [0, 2]
      (orbitP12RepresentativeCoeff 4) = orbitP12TargetCoeff 4 := by
  decide +kernel

noncomputable def orbitP12NormalizeEquiv4 :
    CocycleGroup (orbitP12SelectedCocycle (orbitP12Index 4))
        (orbitP12SelectedCocycle_consistent (orbitP12Index 4)) ≃*
      CocycleGroup (orbitP12TargetCocycle 4)
        (orbitP12TargetCocycle_consistent 4) := by
  let e := Order16Table.orbitPathEquiv parent12Table coverageP12HBasis
    orbitP12ActionColumns orbitP12CorrectionColumns orbitP12_hbasis_cocycle
    orbitP12Aut orbitP12_action_linear [0, 2] (orbitP12RepresentativeCoeff 4)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent12Table coverageP12HBasis)
      orbitP12_path_endpoint_4))

theorem orbitP12_path_endpoint_5 :
    Order16Table.applyOrbitPath orbitP12ActionColumns [0, 2]
      (orbitP12RepresentativeCoeff 5) = orbitP12TargetCoeff 5 := by
  decide +kernel

noncomputable def orbitP12NormalizeEquiv5 :
    CocycleGroup (orbitP12SelectedCocycle (orbitP12Index 5))
        (orbitP12SelectedCocycle_consistent (orbitP12Index 5)) ≃*
      CocycleGroup (orbitP12TargetCocycle 5)
        (orbitP12TargetCocycle_consistent 5) := by
  let e := Order16Table.orbitPathEquiv parent12Table coverageP12HBasis
    orbitP12ActionColumns orbitP12CorrectionColumns orbitP12_hbasis_cocycle
    orbitP12Aut orbitP12_action_linear [0, 2] (orbitP12RepresentativeCoeff 5)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent12Table coverageP12HBasis)
      orbitP12_path_endpoint_5))

theorem orbitP12_path_endpoint_6 :
    Order16Table.applyOrbitPath orbitP12ActionColumns [1]
      (orbitP12RepresentativeCoeff 6) = orbitP12TargetCoeff 6 := by
  decide +kernel

noncomputable def orbitP12NormalizeEquiv6 :
    CocycleGroup (orbitP12SelectedCocycle (orbitP12Index 6))
        (orbitP12SelectedCocycle_consistent (orbitP12Index 6)) ≃*
      CocycleGroup (orbitP12TargetCocycle 6)
        (orbitP12TargetCocycle_consistent 6) := by
  let e := Order16Table.orbitPathEquiv parent12Table coverageP12HBasis
    orbitP12ActionColumns orbitP12CorrectionColumns orbitP12_hbasis_cocycle
    orbitP12Aut orbitP12_action_linear [1] (orbitP12RepresentativeCoeff 6)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent12Table coverageP12HBasis)
      orbitP12_path_endpoint_6))

theorem orbitP12_path_endpoint_7 :
    Order16Table.applyOrbitPath orbitP12ActionColumns [1]
      (orbitP12RepresentativeCoeff 7) = orbitP12TargetCoeff 7 := by
  decide +kernel

noncomputable def orbitP12NormalizeEquiv7 :
    CocycleGroup (orbitP12SelectedCocycle (orbitP12Index 7))
        (orbitP12SelectedCocycle_consistent (orbitP12Index 7)) ≃*
      CocycleGroup (orbitP12TargetCocycle 7)
        (orbitP12TargetCocycle_consistent 7) := by
  let e := Order16Table.orbitPathEquiv parent12Table coverageP12HBasis
    orbitP12ActionColumns orbitP12CorrectionColumns orbitP12_hbasis_cocycle
    orbitP12Aut orbitP12_action_linear [1] (orbitP12RepresentativeCoeff 7)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent12Table coverageP12HBasis)
      orbitP12_path_endpoint_7))

theorem orbitP12_path_endpoint_8 :
    Order16Table.applyOrbitPath orbitP12ActionColumns [0, 3]
      (orbitP12RepresentativeCoeff 8) = orbitP12TargetCoeff 8 := by
  decide +kernel

noncomputable def orbitP12NormalizeEquiv8 :
    CocycleGroup (orbitP12SelectedCocycle (orbitP12Index 8))
        (orbitP12SelectedCocycle_consistent (orbitP12Index 8)) ≃*
      CocycleGroup (orbitP12TargetCocycle 8)
        (orbitP12TargetCocycle_consistent 8) := by
  let e := Order16Table.orbitPathEquiv parent12Table coverageP12HBasis
    orbitP12ActionColumns orbitP12CorrectionColumns orbitP12_hbasis_cocycle
    orbitP12Aut orbitP12_action_linear [0, 3] (orbitP12RepresentativeCoeff 8)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent12Table coverageP12HBasis)
      orbitP12_path_endpoint_8))

theorem orbitP12_path_endpoint_9 :
    Order16Table.applyOrbitPath orbitP12ActionColumns []
      (orbitP12RepresentativeCoeff 9) = orbitP12TargetCoeff 9 := by
  decide +kernel

noncomputable def orbitP12NormalizeEquiv9 :
    CocycleGroup (orbitP12SelectedCocycle (orbitP12Index 9))
        (orbitP12SelectedCocycle_consistent (orbitP12Index 9)) ≃*
      CocycleGroup (orbitP12TargetCocycle 9)
        (orbitP12TargetCocycle_consistent 9) := by
  let e := Order16Table.orbitPathEquiv parent12Table coverageP12HBasis
    orbitP12ActionColumns orbitP12CorrectionColumns orbitP12_hbasis_cocycle
    orbitP12Aut orbitP12_action_linear [] (orbitP12RepresentativeCoeff 9)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent12Table coverageP12HBasis)
      orbitP12_path_endpoint_9))

theorem orbitP12_path_endpoint_10 :
    Order16Table.applyOrbitPath orbitP12ActionColumns [2, 3]
      (orbitP12RepresentativeCoeff 10) = orbitP12TargetCoeff 10 := by
  decide +kernel

noncomputable def orbitP12NormalizeEquiv10 :
    CocycleGroup (orbitP12SelectedCocycle (orbitP12Index 10))
        (orbitP12SelectedCocycle_consistent (orbitP12Index 10)) ≃*
      CocycleGroup (orbitP12TargetCocycle 10)
        (orbitP12TargetCocycle_consistent 10) := by
  let e := Order16Table.orbitPathEquiv parent12Table coverageP12HBasis
    orbitP12ActionColumns orbitP12CorrectionColumns orbitP12_hbasis_cocycle
    orbitP12Aut orbitP12_action_linear [2, 3] (orbitP12RepresentativeCoeff 10)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent12Table coverageP12HBasis)
      orbitP12_path_endpoint_10))

theorem orbitP12_path_endpoint_11 :
    Order16Table.applyOrbitPath orbitP12ActionColumns [2]
      (orbitP12RepresentativeCoeff 11) = orbitP12TargetCoeff 11 := by
  decide +kernel

noncomputable def orbitP12NormalizeEquiv11 :
    CocycleGroup (orbitP12SelectedCocycle (orbitP12Index 11))
        (orbitP12SelectedCocycle_consistent (orbitP12Index 11)) ≃*
      CocycleGroup (orbitP12TargetCocycle 11)
        (orbitP12TargetCocycle_consistent 11) := by
  let e := Order16Table.orbitPathEquiv parent12Table coverageP12HBasis
    orbitP12ActionColumns orbitP12CorrectionColumns orbitP12_hbasis_cocycle
    orbitP12Aut orbitP12_action_linear [2] (orbitP12RepresentativeCoeff 11)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent12Table coverageP12HBasis)
      orbitP12_path_endpoint_11))

theorem orbitP12_path_endpoint_12 :
    Order16Table.applyOrbitPath orbitP12ActionColumns [0]
      (orbitP12RepresentativeCoeff 12) = orbitP12TargetCoeff 12 := by
  decide +kernel

noncomputable def orbitP12NormalizeEquiv12 :
    CocycleGroup (orbitP12SelectedCocycle (orbitP12Index 12))
        (orbitP12SelectedCocycle_consistent (orbitP12Index 12)) ≃*
      CocycleGroup (orbitP12TargetCocycle 12)
        (orbitP12TargetCocycle_consistent 12) := by
  let e := Order16Table.orbitPathEquiv parent12Table coverageP12HBasis
    orbitP12ActionColumns orbitP12CorrectionColumns orbitP12_hbasis_cocycle
    orbitP12Aut orbitP12_action_linear [0] (orbitP12RepresentativeCoeff 12)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent12Table coverageP12HBasis)
      orbitP12_path_endpoint_12))

theorem orbitP12_path_endpoint_13 :
    Order16Table.applyOrbitPath orbitP12ActionColumns []
      (orbitP12RepresentativeCoeff 13) = orbitP12TargetCoeff 13 := by
  decide +kernel

noncomputable def orbitP12NormalizeEquiv13 :
    CocycleGroup (orbitP12SelectedCocycle (orbitP12Index 13))
        (orbitP12SelectedCocycle_consistent (orbitP12Index 13)) ≃*
      CocycleGroup (orbitP12TargetCocycle 13)
        (orbitP12TargetCocycle_consistent 13) := by
  let e := Order16Table.orbitPathEquiv parent12Table coverageP12HBasis
    orbitP12ActionColumns orbitP12CorrectionColumns orbitP12_hbasis_cocycle
    orbitP12Aut orbitP12_action_linear [] (orbitP12RepresentativeCoeff 13)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent12Table coverageP12HBasis)
      orbitP12_path_endpoint_13))

theorem orbitP12_path_endpoint_14 :
    Order16Table.applyOrbitPath orbitP12ActionColumns [0, 1, 0]
      (orbitP12RepresentativeCoeff 14) = orbitP12TargetCoeff 14 := by
  decide +kernel

noncomputable def orbitP12NormalizeEquiv14 :
    CocycleGroup (orbitP12SelectedCocycle (orbitP12Index 14))
        (orbitP12SelectedCocycle_consistent (orbitP12Index 14)) ≃*
      CocycleGroup (orbitP12TargetCocycle 14)
        (orbitP12TargetCocycle_consistent 14) := by
  let e := Order16Table.orbitPathEquiv parent12Table coverageP12HBasis
    orbitP12ActionColumns orbitP12CorrectionColumns orbitP12_hbasis_cocycle
    orbitP12Aut orbitP12_action_linear [0, 1, 0] (orbitP12RepresentativeCoeff 14)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent12Table coverageP12HBasis)
      orbitP12_path_endpoint_14))

theorem orbitP12_path_endpoint_15 :
    Order16Table.applyOrbitPath orbitP12ActionColumns [1, 3]
      (orbitP12RepresentativeCoeff 15) = orbitP12TargetCoeff 15 := by
  decide +kernel

noncomputable def orbitP12NormalizeEquiv15 :
    CocycleGroup (orbitP12SelectedCocycle (orbitP12Index 15))
        (orbitP12SelectedCocycle_consistent (orbitP12Index 15)) ≃*
      CocycleGroup (orbitP12TargetCocycle 15)
        (orbitP12TargetCocycle_consistent 15) := by
  let e := Order16Table.orbitPathEquiv parent12Table coverageP12HBasis
    orbitP12ActionColumns orbitP12CorrectionColumns orbitP12_hbasis_cocycle
    orbitP12Aut orbitP12_action_linear [1, 3] (orbitP12RepresentativeCoeff 15)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent12Table coverageP12HBasis)
      orbitP12_path_endpoint_15))

end Smallgroups.UsefulTheorems.Order32Certificate
