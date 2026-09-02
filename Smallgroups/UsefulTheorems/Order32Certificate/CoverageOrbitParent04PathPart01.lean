/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent04Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent03PathPart01

set_option maxRecDepth 100000

/-! Checked short orbit paths for parent 4; generated part 1. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP4_path_endpoint_0 :
    Order16Table.applyOrbitPath orbitP4ActionColumns []
      (orbitP4RepresentativeCoeff 0) = orbitP4TargetCoeff 0 := by
  decide +kernel

noncomputable def orbitP4NormalizeEquiv0 :
    CocycleGroup (orbitP4SelectedCocycle (orbitP4Index 0))
        (orbitP4SelectedCocycle_consistent (orbitP4Index 0)) ≃*
      CocycleGroup (orbitP4TargetCocycle 0)
        (orbitP4TargetCocycle_consistent 0) := by
  let e := Order16Table.orbitPathEquiv parent4Table coverageP4HBasis
    orbitP4ActionColumns orbitP4CorrectionColumns orbitP4_hbasis_cocycle
    orbitP4Aut orbitP4_action_linear [] (orbitP4RepresentativeCoeff 0)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent4Table coverageP4HBasis)
      orbitP4_path_endpoint_0))

theorem orbitP4_path_endpoint_1 :
    Order16Table.applyOrbitPath orbitP4ActionColumns []
      (orbitP4RepresentativeCoeff 1) = orbitP4TargetCoeff 1 := by
  decide +kernel

noncomputable def orbitP4NormalizeEquiv1 :
    CocycleGroup (orbitP4SelectedCocycle (orbitP4Index 1))
        (orbitP4SelectedCocycle_consistent (orbitP4Index 1)) ≃*
      CocycleGroup (orbitP4TargetCocycle 1)
        (orbitP4TargetCocycle_consistent 1) := by
  let e := Order16Table.orbitPathEquiv parent4Table coverageP4HBasis
    orbitP4ActionColumns orbitP4CorrectionColumns orbitP4_hbasis_cocycle
    orbitP4Aut orbitP4_action_linear [] (orbitP4RepresentativeCoeff 1)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent4Table coverageP4HBasis)
      orbitP4_path_endpoint_1))

theorem orbitP4_path_endpoint_2 :
    Order16Table.applyOrbitPath orbitP4ActionColumns []
      (orbitP4RepresentativeCoeff 2) = orbitP4TargetCoeff 2 := by
  decide +kernel

noncomputable def orbitP4NormalizeEquiv2 :
    CocycleGroup (orbitP4SelectedCocycle (orbitP4Index 2))
        (orbitP4SelectedCocycle_consistent (orbitP4Index 2)) ≃*
      CocycleGroup (orbitP4TargetCocycle 2)
        (orbitP4TargetCocycle_consistent 2) := by
  let e := Order16Table.orbitPathEquiv parent4Table coverageP4HBasis
    orbitP4ActionColumns orbitP4CorrectionColumns orbitP4_hbasis_cocycle
    orbitP4Aut orbitP4_action_linear [] (orbitP4RepresentativeCoeff 2)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent4Table coverageP4HBasis)
      orbitP4_path_endpoint_2))

theorem orbitP4_path_endpoint_3 :
    Order16Table.applyOrbitPath orbitP4ActionColumns []
      (orbitP4RepresentativeCoeff 3) = orbitP4TargetCoeff 3 := by
  decide +kernel

noncomputable def orbitP4NormalizeEquiv3 :
    CocycleGroup (orbitP4SelectedCocycle (orbitP4Index 3))
        (orbitP4SelectedCocycle_consistent (orbitP4Index 3)) ≃*
      CocycleGroup (orbitP4TargetCocycle 3)
        (orbitP4TargetCocycle_consistent 3) := by
  let e := Order16Table.orbitPathEquiv parent4Table coverageP4HBasis
    orbitP4ActionColumns orbitP4CorrectionColumns orbitP4_hbasis_cocycle
    orbitP4Aut orbitP4_action_linear [] (orbitP4RepresentativeCoeff 3)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent4Table coverageP4HBasis)
      orbitP4_path_endpoint_3))

theorem orbitP4_path_endpoint_4 :
    Order16Table.applyOrbitPath orbitP4ActionColumns []
      (orbitP4RepresentativeCoeff 4) = orbitP4TargetCoeff 4 := by
  decide +kernel

noncomputable def orbitP4NormalizeEquiv4 :
    CocycleGroup (orbitP4SelectedCocycle (orbitP4Index 4))
        (orbitP4SelectedCocycle_consistent (orbitP4Index 4)) ≃*
      CocycleGroup (orbitP4TargetCocycle 4)
        (orbitP4TargetCocycle_consistent 4) := by
  let e := Order16Table.orbitPathEquiv parent4Table coverageP4HBasis
    orbitP4ActionColumns orbitP4CorrectionColumns orbitP4_hbasis_cocycle
    orbitP4Aut orbitP4_action_linear [] (orbitP4RepresentativeCoeff 4)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent4Table coverageP4HBasis)
      orbitP4_path_endpoint_4))

theorem orbitP4_path_endpoint_5 :
    Order16Table.applyOrbitPath orbitP4ActionColumns []
      (orbitP4RepresentativeCoeff 5) = orbitP4TargetCoeff 5 := by
  decide +kernel

noncomputable def orbitP4NormalizeEquiv5 :
    CocycleGroup (orbitP4SelectedCocycle (orbitP4Index 5))
        (orbitP4SelectedCocycle_consistent (orbitP4Index 5)) ≃*
      CocycleGroup (orbitP4TargetCocycle 5)
        (orbitP4TargetCocycle_consistent 5) := by
  let e := Order16Table.orbitPathEquiv parent4Table coverageP4HBasis
    orbitP4ActionColumns orbitP4CorrectionColumns orbitP4_hbasis_cocycle
    orbitP4Aut orbitP4_action_linear [] (orbitP4RepresentativeCoeff 5)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent4Table coverageP4HBasis)
      orbitP4_path_endpoint_5))

theorem orbitP4_path_endpoint_6 :
    Order16Table.applyOrbitPath orbitP4ActionColumns [4]
      (orbitP4RepresentativeCoeff 6) = orbitP4TargetCoeff 6 := by
  decide +kernel

noncomputable def orbitP4NormalizeEquiv6 :
    CocycleGroup (orbitP4SelectedCocycle (orbitP4Index 6))
        (orbitP4SelectedCocycle_consistent (orbitP4Index 6)) ≃*
      CocycleGroup (orbitP4TargetCocycle 6)
        (orbitP4TargetCocycle_consistent 6) := by
  let e := Order16Table.orbitPathEquiv parent4Table coverageP4HBasis
    orbitP4ActionColumns orbitP4CorrectionColumns orbitP4_hbasis_cocycle
    orbitP4Aut orbitP4_action_linear [4] (orbitP4RepresentativeCoeff 6)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent4Table coverageP4HBasis)
      orbitP4_path_endpoint_6))

theorem orbitP4_path_endpoint_7 :
    Order16Table.applyOrbitPath orbitP4ActionColumns [4]
      (orbitP4RepresentativeCoeff 7) = orbitP4TargetCoeff 7 := by
  decide +kernel

noncomputable def orbitP4NormalizeEquiv7 :
    CocycleGroup (orbitP4SelectedCocycle (orbitP4Index 7))
        (orbitP4SelectedCocycle_consistent (orbitP4Index 7)) ≃*
      CocycleGroup (orbitP4TargetCocycle 7)
        (orbitP4TargetCocycle_consistent 7) := by
  let e := Order16Table.orbitPathEquiv parent4Table coverageP4HBasis
    orbitP4ActionColumns orbitP4CorrectionColumns orbitP4_hbasis_cocycle
    orbitP4Aut orbitP4_action_linear [4] (orbitP4RepresentativeCoeff 7)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent4Table coverageP4HBasis)
      orbitP4_path_endpoint_7))

end Smallgroups.UsefulTheorems.Order32Certificate
