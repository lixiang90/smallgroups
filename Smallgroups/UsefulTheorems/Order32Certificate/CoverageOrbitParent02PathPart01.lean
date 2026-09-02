/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent02Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent01PathPart01

set_option maxRecDepth 100000

/-! Checked short orbit paths for parent 2; generated part 1. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP2_path_endpoint_0 :
    Order16Table.applyOrbitPath orbitP2ActionColumns []
      (orbitP2RepresentativeCoeff 0) = orbitP2TargetCoeff 0 := by
  decide +kernel

noncomputable def orbitP2NormalizeEquiv0 :
    CocycleGroup (orbitP2SelectedCocycle (orbitP2Index 0))
        (orbitP2SelectedCocycle_consistent (orbitP2Index 0)) ≃*
      CocycleGroup (orbitP2TargetCocycle 0)
        (orbitP2TargetCocycle_consistent 0) := by
  let e := Order16Table.orbitPathEquiv parent2Table coverageP2HBasis
    orbitP2ActionColumns orbitP2CorrectionColumns orbitP2_hbasis_cocycle
    orbitP2Aut orbitP2_action_linear [] (orbitP2RepresentativeCoeff 0)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent2Table coverageP2HBasis)
      orbitP2_path_endpoint_0))

theorem orbitP2_path_endpoint_1 :
    Order16Table.applyOrbitPath orbitP2ActionColumns []
      (orbitP2RepresentativeCoeff 1) = orbitP2TargetCoeff 1 := by
  decide +kernel

noncomputable def orbitP2NormalizeEquiv1 :
    CocycleGroup (orbitP2SelectedCocycle (orbitP2Index 1))
        (orbitP2SelectedCocycle_consistent (orbitP2Index 1)) ≃*
      CocycleGroup (orbitP2TargetCocycle 1)
        (orbitP2TargetCocycle_consistent 1) := by
  let e := Order16Table.orbitPathEquiv parent2Table coverageP2HBasis
    orbitP2ActionColumns orbitP2CorrectionColumns orbitP2_hbasis_cocycle
    orbitP2Aut orbitP2_action_linear [] (orbitP2RepresentativeCoeff 1)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent2Table coverageP2HBasis)
      orbitP2_path_endpoint_1))

theorem orbitP2_path_endpoint_2 :
    Order16Table.applyOrbitPath orbitP2ActionColumns []
      (orbitP2RepresentativeCoeff 2) = orbitP2TargetCoeff 2 := by
  decide +kernel

noncomputable def orbitP2NormalizeEquiv2 :
    CocycleGroup (orbitP2SelectedCocycle (orbitP2Index 2))
        (orbitP2SelectedCocycle_consistent (orbitP2Index 2)) ≃*
      CocycleGroup (orbitP2TargetCocycle 2)
        (orbitP2TargetCocycle_consistent 2) := by
  let e := Order16Table.orbitPathEquiv parent2Table coverageP2HBasis
    orbitP2ActionColumns orbitP2CorrectionColumns orbitP2_hbasis_cocycle
    orbitP2Aut orbitP2_action_linear [] (orbitP2RepresentativeCoeff 2)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent2Table coverageP2HBasis)
      orbitP2_path_endpoint_2))

theorem orbitP2_path_endpoint_3 :
    Order16Table.applyOrbitPath orbitP2ActionColumns []
      (orbitP2RepresentativeCoeff 3) = orbitP2TargetCoeff 3 := by
  decide +kernel

noncomputable def orbitP2NormalizeEquiv3 :
    CocycleGroup (orbitP2SelectedCocycle (orbitP2Index 3))
        (orbitP2SelectedCocycle_consistent (orbitP2Index 3)) ≃*
      CocycleGroup (orbitP2TargetCocycle 3)
        (orbitP2TargetCocycle_consistent 3) := by
  let e := Order16Table.orbitPathEquiv parent2Table coverageP2HBasis
    orbitP2ActionColumns orbitP2CorrectionColumns orbitP2_hbasis_cocycle
    orbitP2Aut orbitP2_action_linear [] (orbitP2RepresentativeCoeff 3)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent2Table coverageP2HBasis)
      orbitP2_path_endpoint_3))

theorem orbitP2_path_endpoint_4 :
    Order16Table.applyOrbitPath orbitP2ActionColumns [2]
      (orbitP2RepresentativeCoeff 4) = orbitP2TargetCoeff 4 := by
  decide +kernel

noncomputable def orbitP2NormalizeEquiv4 :
    CocycleGroup (orbitP2SelectedCocycle (orbitP2Index 4))
        (orbitP2SelectedCocycle_consistent (orbitP2Index 4)) ≃*
      CocycleGroup (orbitP2TargetCocycle 4)
        (orbitP2TargetCocycle_consistent 4) := by
  let e := Order16Table.orbitPathEquiv parent2Table coverageP2HBasis
    orbitP2ActionColumns orbitP2CorrectionColumns orbitP2_hbasis_cocycle
    orbitP2Aut orbitP2_action_linear [2] (orbitP2RepresentativeCoeff 4)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent2Table coverageP2HBasis)
      orbitP2_path_endpoint_4))

theorem orbitP2_path_endpoint_5 :
    Order16Table.applyOrbitPath orbitP2ActionColumns [2, 0]
      (orbitP2RepresentativeCoeff 5) = orbitP2TargetCoeff 5 := by
  decide +kernel

noncomputable def orbitP2NormalizeEquiv5 :
    CocycleGroup (orbitP2SelectedCocycle (orbitP2Index 5))
        (orbitP2SelectedCocycle_consistent (orbitP2Index 5)) ≃*
      CocycleGroup (orbitP2TargetCocycle 5)
        (orbitP2TargetCocycle_consistent 5) := by
  let e := Order16Table.orbitPathEquiv parent2Table coverageP2HBasis
    orbitP2ActionColumns orbitP2CorrectionColumns orbitP2_hbasis_cocycle
    orbitP2Aut orbitP2_action_linear [2, 0] (orbitP2RepresentativeCoeff 5)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent2Table coverageP2HBasis)
      orbitP2_path_endpoint_5))

theorem orbitP2_path_endpoint_6 :
    Order16Table.applyOrbitPath orbitP2ActionColumns [2]
      (orbitP2RepresentativeCoeff 6) = orbitP2TargetCoeff 6 := by
  decide +kernel

noncomputable def orbitP2NormalizeEquiv6 :
    CocycleGroup (orbitP2SelectedCocycle (orbitP2Index 6))
        (orbitP2SelectedCocycle_consistent (orbitP2Index 6)) ≃*
      CocycleGroup (orbitP2TargetCocycle 6)
        (orbitP2TargetCocycle_consistent 6) := by
  let e := Order16Table.orbitPathEquiv parent2Table coverageP2HBasis
    orbitP2ActionColumns orbitP2CorrectionColumns orbitP2_hbasis_cocycle
    orbitP2Aut orbitP2_action_linear [2] (orbitP2RepresentativeCoeff 6)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent2Table coverageP2HBasis)
      orbitP2_path_endpoint_6))

theorem orbitP2_path_endpoint_7 :
    Order16Table.applyOrbitPath orbitP2ActionColumns [2, 0]
      (orbitP2RepresentativeCoeff 7) = orbitP2TargetCoeff 7 := by
  decide +kernel

noncomputable def orbitP2NormalizeEquiv7 :
    CocycleGroup (orbitP2SelectedCocycle (orbitP2Index 7))
        (orbitP2SelectedCocycle_consistent (orbitP2Index 7)) ≃*
      CocycleGroup (orbitP2TargetCocycle 7)
        (orbitP2TargetCocycle_consistent 7) := by
  let e := Order16Table.orbitPathEquiv parent2Table coverageP2HBasis
    orbitP2ActionColumns orbitP2CorrectionColumns orbitP2_hbasis_cocycle
    orbitP2Aut orbitP2_action_linear [2, 0] (orbitP2RepresentativeCoeff 7)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent2Table coverageP2HBasis)
      orbitP2_path_endpoint_7))

end Smallgroups.UsefulTheorems.Order32Certificate
