/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10PathIdentity

set_option maxRecDepth 100000

/-! Checked short orbit paths for parent 11; generated part 1. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP11_path_endpoint_0 :
    Order16Table.applyOrbitPath orbitP11ActionColumns []
      (orbitP11RepresentativeCoeff 0) = orbitP11TargetCoeff 0 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv0 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 0))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 0)) ≃*
      CocycleGroup (orbitP11TargetCocycle 0)
        (orbitP11TargetCocycle_consistent 0) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [] (orbitP11RepresentativeCoeff 0)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_0))

theorem orbitP11_path_endpoint_1 :
    Order16Table.applyOrbitPath orbitP11ActionColumns []
      (orbitP11RepresentativeCoeff 1) = orbitP11TargetCoeff 1 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv1 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 1))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 1)) ≃*
      CocycleGroup (orbitP11TargetCocycle 1)
        (orbitP11TargetCocycle_consistent 1) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [] (orbitP11RepresentativeCoeff 1)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_1))

theorem orbitP11_path_endpoint_2 :
    Order16Table.applyOrbitPath orbitP11ActionColumns []
      (orbitP11RepresentativeCoeff 2) = orbitP11TargetCoeff 2 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv2 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 2))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 2)) ≃*
      CocycleGroup (orbitP11TargetCocycle 2)
        (orbitP11TargetCocycle_consistent 2) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [] (orbitP11RepresentativeCoeff 2)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_2))

theorem orbitP11_path_endpoint_3 :
    Order16Table.applyOrbitPath orbitP11ActionColumns []
      (orbitP11RepresentativeCoeff 3) = orbitP11TargetCoeff 3 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv3 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 3))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 3)) ≃*
      CocycleGroup (orbitP11TargetCocycle 3)
        (orbitP11TargetCocycle_consistent 3) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [] (orbitP11RepresentativeCoeff 3)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_3))

theorem orbitP11_path_endpoint_4 :
    Order16Table.applyOrbitPath orbitP11ActionColumns []
      (orbitP11RepresentativeCoeff 4) = orbitP11TargetCoeff 4 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv4 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 4))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 4)) ≃*
      CocycleGroup (orbitP11TargetCocycle 4)
        (orbitP11TargetCocycle_consistent 4) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [] (orbitP11RepresentativeCoeff 4)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_4))

theorem orbitP11_path_endpoint_5 :
    Order16Table.applyOrbitPath orbitP11ActionColumns []
      (orbitP11RepresentativeCoeff 5) = orbitP11TargetCoeff 5 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv5 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 5))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 5)) ≃*
      CocycleGroup (orbitP11TargetCocycle 5)
        (orbitP11TargetCocycle_consistent 5) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [] (orbitP11RepresentativeCoeff 5)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_5))

theorem orbitP11_path_endpoint_6 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [0, 1]
      (orbitP11RepresentativeCoeff 6) = orbitP11TargetCoeff 6 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv6 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 6))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 6)) ≃*
      CocycleGroup (orbitP11TargetCocycle 6)
        (orbitP11TargetCocycle_consistent 6) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [0, 1] (orbitP11RepresentativeCoeff 6)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_6))

theorem orbitP11_path_endpoint_7 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [0, 2]
      (orbitP11RepresentativeCoeff 7) = orbitP11TargetCoeff 7 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv7 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 7))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 7)) ≃*
      CocycleGroup (orbitP11TargetCocycle 7)
        (orbitP11TargetCocycle_consistent 7) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [0, 2] (orbitP11RepresentativeCoeff 7)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_7))

theorem orbitP11_path_endpoint_8 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [0]
      (orbitP11RepresentativeCoeff 8) = orbitP11TargetCoeff 8 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv8 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 8))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 8)) ≃*
      CocycleGroup (orbitP11TargetCocycle 8)
        (orbitP11TargetCocycle_consistent 8) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [0] (orbitP11RepresentativeCoeff 8)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_8))

theorem orbitP11_path_endpoint_9 :
    Order16Table.applyOrbitPath orbitP11ActionColumns []
      (orbitP11RepresentativeCoeff 9) = orbitP11TargetCoeff 9 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv9 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 9))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 9)) ≃*
      CocycleGroup (orbitP11TargetCocycle 9)
        (orbitP11TargetCocycle_consistent 9) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [] (orbitP11RepresentativeCoeff 9)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_9))

theorem orbitP11_path_endpoint_10 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [0]
      (orbitP11RepresentativeCoeff 10) = orbitP11TargetCoeff 10 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv10 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 10))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 10)) ≃*
      CocycleGroup (orbitP11TargetCocycle 10)
        (orbitP11TargetCocycle_consistent 10) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [0] (orbitP11RepresentativeCoeff 10)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_10))

theorem orbitP11_path_endpoint_11 :
    Order16Table.applyOrbitPath orbitP11ActionColumns []
      (orbitP11RepresentativeCoeff 11) = orbitP11TargetCoeff 11 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv11 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 11))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 11)) ≃*
      CocycleGroup (orbitP11TargetCocycle 11)
        (orbitP11TargetCocycle_consistent 11) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [] (orbitP11RepresentativeCoeff 11)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_11))

theorem orbitP11_path_endpoint_12 :
    Order16Table.applyOrbitPath orbitP11ActionColumns []
      (orbitP11RepresentativeCoeff 12) = orbitP11TargetCoeff 12 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv12 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 12))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 12)) ≃*
      CocycleGroup (orbitP11TargetCocycle 12)
        (orbitP11TargetCocycle_consistent 12) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [] (orbitP11RepresentativeCoeff 12)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_12))

theorem orbitP11_path_endpoint_13 :
    Order16Table.applyOrbitPath orbitP11ActionColumns []
      (orbitP11RepresentativeCoeff 13) = orbitP11TargetCoeff 13 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv13 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 13))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 13)) ≃*
      CocycleGroup (orbitP11TargetCocycle 13)
        (orbitP11TargetCocycle_consistent 13) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [] (orbitP11RepresentativeCoeff 13)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_13))

theorem orbitP11_path_endpoint_14 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [0, 2]
      (orbitP11RepresentativeCoeff 14) = orbitP11TargetCoeff 14 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv14 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 14))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 14)) ≃*
      CocycleGroup (orbitP11TargetCocycle 14)
        (orbitP11TargetCocycle_consistent 14) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [0, 2] (orbitP11RepresentativeCoeff 14)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_14))

theorem orbitP11_path_endpoint_15 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [0, 1]
      (orbitP11RepresentativeCoeff 15) = orbitP11TargetCoeff 15 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv15 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 15))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 15)) ≃*
      CocycleGroup (orbitP11TargetCocycle 15)
        (orbitP11TargetCocycle_consistent 15) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [0, 1] (orbitP11RepresentativeCoeff 15)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_15))

end Smallgroups.UsefulTheorems.Order32Certificate
