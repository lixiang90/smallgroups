/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent06Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent05PathPart01

set_option maxRecDepth 100000

/-! Checked short orbit paths for parent 6; generated part 1. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP6_path_endpoint_0 :
    Order16Table.applyOrbitPath orbitP6ActionColumns []
      (orbitP6RepresentativeCoeff 0) = orbitP6TargetCoeff 0 := by
  decide +kernel

noncomputable def orbitP6NormalizeEquiv0 :
    CocycleGroup (orbitP6SelectedCocycle (orbitP6Index 0))
        (orbitP6SelectedCocycle_consistent (orbitP6Index 0)) ≃*
      CocycleGroup (orbitP6TargetCocycle 0)
        (orbitP6TargetCocycle_consistent 0) := by
  let e := Order16Table.orbitPathEquiv parent6Table coverageP6HBasis
    orbitP6ActionColumns orbitP6CorrectionColumns orbitP6_hbasis_cocycle
    orbitP6Aut orbitP6_action_linear [] (orbitP6RepresentativeCoeff 0)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent6Table coverageP6HBasis)
      orbitP6_path_endpoint_0))

theorem orbitP6_path_endpoint_1 :
    Order16Table.applyOrbitPath orbitP6ActionColumns []
      (orbitP6RepresentativeCoeff 1) = orbitP6TargetCoeff 1 := by
  decide +kernel

noncomputable def orbitP6NormalizeEquiv1 :
    CocycleGroup (orbitP6SelectedCocycle (orbitP6Index 1))
        (orbitP6SelectedCocycle_consistent (orbitP6Index 1)) ≃*
      CocycleGroup (orbitP6TargetCocycle 1)
        (orbitP6TargetCocycle_consistent 1) := by
  let e := Order16Table.orbitPathEquiv parent6Table coverageP6HBasis
    orbitP6ActionColumns orbitP6CorrectionColumns orbitP6_hbasis_cocycle
    orbitP6Aut orbitP6_action_linear [] (orbitP6RepresentativeCoeff 1)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent6Table coverageP6HBasis)
      orbitP6_path_endpoint_1))

theorem orbitP6_path_endpoint_2 :
    Order16Table.applyOrbitPath orbitP6ActionColumns []
      (orbitP6RepresentativeCoeff 2) = orbitP6TargetCoeff 2 := by
  decide +kernel

noncomputable def orbitP6NormalizeEquiv2 :
    CocycleGroup (orbitP6SelectedCocycle (orbitP6Index 2))
        (orbitP6SelectedCocycle_consistent (orbitP6Index 2)) ≃*
      CocycleGroup (orbitP6TargetCocycle 2)
        (orbitP6TargetCocycle_consistent 2) := by
  let e := Order16Table.orbitPathEquiv parent6Table coverageP6HBasis
    orbitP6ActionColumns orbitP6CorrectionColumns orbitP6_hbasis_cocycle
    orbitP6Aut orbitP6_action_linear [] (orbitP6RepresentativeCoeff 2)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent6Table coverageP6HBasis)
      orbitP6_path_endpoint_2))

theorem orbitP6_path_endpoint_3 :
    Order16Table.applyOrbitPath orbitP6ActionColumns []
      (orbitP6RepresentativeCoeff 3) = orbitP6TargetCoeff 3 := by
  decide +kernel

noncomputable def orbitP6NormalizeEquiv3 :
    CocycleGroup (orbitP6SelectedCocycle (orbitP6Index 3))
        (orbitP6SelectedCocycle_consistent (orbitP6Index 3)) ≃*
      CocycleGroup (orbitP6TargetCocycle 3)
        (orbitP6TargetCocycle_consistent 3) := by
  let e := Order16Table.orbitPathEquiv parent6Table coverageP6HBasis
    orbitP6ActionColumns orbitP6CorrectionColumns orbitP6_hbasis_cocycle
    orbitP6Aut orbitP6_action_linear [] (orbitP6RepresentativeCoeff 3)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent6Table coverageP6HBasis)
      orbitP6_path_endpoint_3))

end Smallgroups.UsefulTheorems.Order32Certificate
