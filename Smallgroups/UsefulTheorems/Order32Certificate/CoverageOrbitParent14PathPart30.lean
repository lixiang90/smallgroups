/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart29

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 30. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_464 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 464) = orbitP14TargetCoeff 464 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv464 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 464))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 464)) ≃*
      CocycleGroup (orbitP14TargetCocycle 464)
        (orbitP14TargetCocycle_consistent 464) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 464)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_464))

theorem orbitP14_path_endpoint_465 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 1, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 465) = orbitP14TargetCoeff 465 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv465 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 465))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 465)) ≃*
      CocycleGroup (orbitP14TargetCocycle 465)
        (orbitP14TargetCocycle_consistent 465) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 1, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 465)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_465))

theorem orbitP14_path_endpoint_466 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 2, 1, 0, 2, 0]
      (orbitP14RepresentativeCoeff 466) = orbitP14TargetCoeff 466 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv466 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 466))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 466)) ≃*
      CocycleGroup (orbitP14TargetCocycle 466)
        (orbitP14TargetCocycle_consistent 466) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 2, 1, 0, 2, 0] (orbitP14RepresentativeCoeff 466)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_466))

theorem orbitP14_path_endpoint_467 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 467) = orbitP14TargetCoeff 467 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv467 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 467))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 467)) ≃*
      CocycleGroup (orbitP14TargetCocycle 467)
        (orbitP14TargetCocycle_consistent 467) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 467)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_467))

theorem orbitP14_path_endpoint_468 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 2, 1, 0, 2]
      (orbitP14RepresentativeCoeff 468) = orbitP14TargetCoeff 468 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv468 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 468))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 468)) ≃*
      CocycleGroup (orbitP14TargetCocycle 468)
        (orbitP14TargetCocycle_consistent 468) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 2, 1, 0, 2] (orbitP14RepresentativeCoeff 468)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_468))

theorem orbitP14_path_endpoint_469 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 0, 2, 0, 1]
      (orbitP14RepresentativeCoeff 469) = orbitP14TargetCoeff 469 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv469 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 469))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 469)) ≃*
      CocycleGroup (orbitP14TargetCocycle 469)
        (orbitP14TargetCocycle_consistent 469) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 0, 2, 0, 1] (orbitP14RepresentativeCoeff 469)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_469))

theorem orbitP14_path_endpoint_470 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 0, 2, 0, 1]
      (orbitP14RepresentativeCoeff 470) = orbitP14TargetCoeff 470 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv470 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 470))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 470)) ≃*
      CocycleGroup (orbitP14TargetCocycle 470)
        (orbitP14TargetCocycle_consistent 470) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 0, 2, 0, 1] (orbitP14RepresentativeCoeff 470)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_470))

theorem orbitP14_path_endpoint_471 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 0, 2, 0, 1]
      (orbitP14RepresentativeCoeff 471) = orbitP14TargetCoeff 471 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv471 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 471))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 471)) ≃*
      CocycleGroup (orbitP14TargetCocycle 471)
        (orbitP14TargetCocycle_consistent 471) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 0, 2, 0, 1] (orbitP14RepresentativeCoeff 471)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_471))

theorem orbitP14_path_endpoint_472 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 1, 1, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 472) = orbitP14TargetCoeff 472 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv472 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 472))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 472)) ≃*
      CocycleGroup (orbitP14TargetCocycle 472)
        (orbitP14TargetCocycle_consistent 472) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 1, 1, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 472)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_472))

theorem orbitP14_path_endpoint_473 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 2, 1, 1, 2]
      (orbitP14RepresentativeCoeff 473) = orbitP14TargetCoeff 473 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv473 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 473))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 473)) ≃*
      CocycleGroup (orbitP14TargetCocycle 473)
        (orbitP14TargetCocycle_consistent 473) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 2, 1, 1, 2] (orbitP14RepresentativeCoeff 473)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_473))

theorem orbitP14_path_endpoint_474 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 0, 1, 1]
      (orbitP14RepresentativeCoeff 474) = orbitP14TargetCoeff 474 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv474 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 474))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 474)) ≃*
      CocycleGroup (orbitP14TargetCocycle 474)
        (orbitP14TargetCocycle_consistent 474) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 0, 1, 1] (orbitP14RepresentativeCoeff 474)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_474))

theorem orbitP14_path_endpoint_475 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 2, 1, 2, 1, 1, 0, 2, 1, 2]
      (orbitP14RepresentativeCoeff 475) = orbitP14TargetCoeff 475 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv475 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 475))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 475)) ≃*
      CocycleGroup (orbitP14TargetCocycle 475)
        (orbitP14TargetCocycle_consistent 475) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 2, 1, 2, 1, 1, 0, 2, 1, 2] (orbitP14RepresentativeCoeff 475)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_475))

theorem orbitP14_path_endpoint_476 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 476) = orbitP14TargetCoeff 476 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv476 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 476))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 476)) ≃*
      CocycleGroup (orbitP14TargetCocycle 476)
        (orbitP14TargetCocycle_consistent 476) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 476)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_476))

theorem orbitP14_path_endpoint_477 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 2, 0, 1, 2, 0, 1, 0, 2]
      (orbitP14RepresentativeCoeff 477) = orbitP14TargetCoeff 477 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv477 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 477))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 477)) ≃*
      CocycleGroup (orbitP14TargetCocycle 477)
        (orbitP14TargetCocycle_consistent 477) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 2, 0, 1, 2, 0, 1, 0, 2] (orbitP14RepresentativeCoeff 477)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_477))

theorem orbitP14_path_endpoint_478 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 2, 0, 1, 1, 2]
      (orbitP14RepresentativeCoeff 478) = orbitP14TargetCoeff 478 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv478 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 478))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 478)) ≃*
      CocycleGroup (orbitP14TargetCocycle 478)
        (orbitP14TargetCocycle_consistent 478) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 2, 0, 1, 1, 2] (orbitP14RepresentativeCoeff 478)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_478))

theorem orbitP14_path_endpoint_479 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 1, 1, 0, 2, 1]
      (orbitP14RepresentativeCoeff 479) = orbitP14TargetCoeff 479 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv479 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 479))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 479)) ≃*
      CocycleGroup (orbitP14TargetCocycle 479)
        (orbitP14TargetCocycle_consistent 479) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 1, 1, 0, 2, 1] (orbitP14RepresentativeCoeff 479)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_479))

end Smallgroups.UsefulTheorems.Order32Certificate
