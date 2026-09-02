/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent09PathPart01

set_option maxRecDepth 100000

/-! Checked short orbit paths for parent 10; generated part 1. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP10_path_endpoint_0 :
    Order16Table.applyOrbitPath orbitP10ActionColumns []
      (orbitP10RepresentativeCoeff 0) = orbitP10TargetCoeff 0 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv0 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 0))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 0)) ≃*
      CocycleGroup (orbitP10TargetCocycle 0)
        (orbitP10TargetCocycle_consistent 0) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [] (orbitP10RepresentativeCoeff 0)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_0))

theorem orbitP10_path_endpoint_1 :
    Order16Table.applyOrbitPath orbitP10ActionColumns []
      (orbitP10RepresentativeCoeff 1) = orbitP10TargetCoeff 1 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv1 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 1))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 1)) ≃*
      CocycleGroup (orbitP10TargetCocycle 1)
        (orbitP10TargetCocycle_consistent 1) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [] (orbitP10RepresentativeCoeff 1)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_1))

theorem orbitP10_path_endpoint_2 :
    Order16Table.applyOrbitPath orbitP10ActionColumns []
      (orbitP10RepresentativeCoeff 2) = orbitP10TargetCoeff 2 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv2 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 2))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 2)) ≃*
      CocycleGroup (orbitP10TargetCocycle 2)
        (orbitP10TargetCocycle_consistent 2) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [] (orbitP10RepresentativeCoeff 2)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_2))

theorem orbitP10_path_endpoint_3 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [0]
      (orbitP10RepresentativeCoeff 3) = orbitP10TargetCoeff 3 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv3 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 3))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 3)) ≃*
      CocycleGroup (orbitP10TargetCocycle 3)
        (orbitP10TargetCocycle_consistent 3) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [0] (orbitP10RepresentativeCoeff 3)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_3))

theorem orbitP10_path_endpoint_4 :
    Order16Table.applyOrbitPath orbitP10ActionColumns []
      (orbitP10RepresentativeCoeff 4) = orbitP10TargetCoeff 4 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv4 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 4))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 4)) ≃*
      CocycleGroup (orbitP10TargetCocycle 4)
        (orbitP10TargetCocycle_consistent 4) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [] (orbitP10RepresentativeCoeff 4)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_4))

theorem orbitP10_path_endpoint_5 :
    Order16Table.applyOrbitPath orbitP10ActionColumns []
      (orbitP10RepresentativeCoeff 5) = orbitP10TargetCoeff 5 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv5 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 5))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 5)) ≃*
      CocycleGroup (orbitP10TargetCocycle 5)
        (orbitP10TargetCocycle_consistent 5) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [] (orbitP10RepresentativeCoeff 5)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_5))

theorem orbitP10_path_endpoint_6 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [2, 6, 0]
      (orbitP10RepresentativeCoeff 6) = orbitP10TargetCoeff 6 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv6 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 6))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 6)) ≃*
      CocycleGroup (orbitP10TargetCocycle 6)
        (orbitP10TargetCocycle_consistent 6) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [2, 6, 0] (orbitP10RepresentativeCoeff 6)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_6))

theorem orbitP10_path_endpoint_7 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [2, 6]
      (orbitP10RepresentativeCoeff 7) = orbitP10TargetCoeff 7 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv7 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 7))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 7)) ≃*
      CocycleGroup (orbitP10TargetCocycle 7)
        (orbitP10TargetCocycle_consistent 7) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [2, 6] (orbitP10RepresentativeCoeff 7)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_7))

theorem orbitP10_path_endpoint_8 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [2]
      (orbitP10RepresentativeCoeff 8) = orbitP10TargetCoeff 8 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv8 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 8))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 8)) ≃*
      CocycleGroup (orbitP10TargetCocycle 8)
        (orbitP10TargetCocycle_consistent 8) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [2] (orbitP10RepresentativeCoeff 8)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_8))

theorem orbitP10_path_endpoint_9 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [2, 0]
      (orbitP10RepresentativeCoeff 9) = orbitP10TargetCoeff 9 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv9 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 9))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 9)) ≃*
      CocycleGroup (orbitP10TargetCocycle 9)
        (orbitP10TargetCocycle_consistent 9) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [2, 0] (orbitP10RepresentativeCoeff 9)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_9))

theorem orbitP10_path_endpoint_10 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [6, 0, 2]
      (orbitP10RepresentativeCoeff 10) = orbitP10TargetCoeff 10 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv10 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 10))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 10)) ≃*
      CocycleGroup (orbitP10TargetCocycle 10)
        (orbitP10TargetCocycle_consistent 10) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [6, 0, 2] (orbitP10RepresentativeCoeff 10)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_10))

theorem orbitP10_path_endpoint_11 :
    Order16Table.applyOrbitPath orbitP10ActionColumns []
      (orbitP10RepresentativeCoeff 11) = orbitP10TargetCoeff 11 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv11 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 11))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 11)) ≃*
      CocycleGroup (orbitP10TargetCocycle 11)
        (orbitP10TargetCocycle_consistent 11) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [] (orbitP10RepresentativeCoeff 11)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_11))

theorem orbitP10_path_endpoint_12 :
    Order16Table.applyOrbitPath orbitP10ActionColumns []
      (orbitP10RepresentativeCoeff 12) = orbitP10TargetCoeff 12 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv12 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 12))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 12)) ≃*
      CocycleGroup (orbitP10TargetCocycle 12)
        (orbitP10TargetCocycle_consistent 12) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [] (orbitP10RepresentativeCoeff 12)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_12))

theorem orbitP10_path_endpoint_13 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [0]
      (orbitP10RepresentativeCoeff 13) = orbitP10TargetCoeff 13 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv13 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 13))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 13)) ≃*
      CocycleGroup (orbitP10TargetCocycle 13)
        (orbitP10TargetCocycle_consistent 13) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [0] (orbitP10RepresentativeCoeff 13)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_13))

theorem orbitP10_path_endpoint_14 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [2, 6]
      (orbitP10RepresentativeCoeff 14) = orbitP10TargetCoeff 14 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv14 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 14))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 14)) ≃*
      CocycleGroup (orbitP10TargetCocycle 14)
        (orbitP10TargetCocycle_consistent 14) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [2, 6] (orbitP10RepresentativeCoeff 14)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_14))

theorem orbitP10_path_endpoint_15 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [0, 2, 6]
      (orbitP10RepresentativeCoeff 15) = orbitP10TargetCoeff 15 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv15 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 15))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 15)) ≃*
      CocycleGroup (orbitP10TargetCocycle 15)
        (orbitP10TargetCocycle_consistent 15) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [0, 2, 6] (orbitP10RepresentativeCoeff 15)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_15))

end Smallgroups.UsefulTheorems.Order32Certificate
