/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart30

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 31. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_480 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1]
      (orbitP14RepresentativeCoeff 480) = orbitP14TargetCoeff 480 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv480 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 480))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 480)) ≃*
      CocycleGroup (orbitP14TargetCocycle 480)
        (orbitP14TargetCocycle_consistent 480) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1] (orbitP14RepresentativeCoeff 480)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_480))

theorem orbitP14_path_endpoint_481 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 2, 1, 0, 1]
      (orbitP14RepresentativeCoeff 481) = orbitP14TargetCoeff 481 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv481 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 481))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 481)) ≃*
      CocycleGroup (orbitP14TargetCocycle 481)
        (orbitP14TargetCocycle_consistent 481) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 2, 1, 0, 1] (orbitP14RepresentativeCoeff 481)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_481))

theorem orbitP14_path_endpoint_482 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 1, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 482) = orbitP14TargetCoeff 482 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv482 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 482))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 482)) ≃*
      CocycleGroup (orbitP14TargetCocycle 482)
        (orbitP14TargetCocycle_consistent 482) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 1, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 482)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_482))

theorem orbitP14_path_endpoint_483 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 0, 1]
      (orbitP14RepresentativeCoeff 483) = orbitP14TargetCoeff 483 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv483 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 483))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 483)) ≃*
      CocycleGroup (orbitP14TargetCocycle 483)
        (orbitP14TargetCocycle_consistent 483) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 0, 1] (orbitP14RepresentativeCoeff 483)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_483))

theorem orbitP14_path_endpoint_484 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 1, 1]
      (orbitP14RepresentativeCoeff 484) = orbitP14TargetCoeff 484 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv484 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 484))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 484)) ≃*
      CocycleGroup (orbitP14TargetCocycle 484)
        (orbitP14TargetCocycle_consistent 484) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 1, 1] (orbitP14RepresentativeCoeff 484)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_484))

theorem orbitP14_path_endpoint_485 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 0, 1, 1]
      (orbitP14RepresentativeCoeff 485) = orbitP14TargetCoeff 485 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv485 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 485))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 485)) ≃*
      CocycleGroup (orbitP14TargetCocycle 485)
        (orbitP14TargetCocycle_consistent 485) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 0, 1, 1] (orbitP14RepresentativeCoeff 485)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_485))

theorem orbitP14_path_endpoint_486 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 2, 1, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 486) = orbitP14TargetCoeff 486 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv486 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 486))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 486)) ≃*
      CocycleGroup (orbitP14TargetCocycle 486)
        (orbitP14TargetCocycle_consistent 486) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 2, 1, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 486)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_486))

theorem orbitP14_path_endpoint_487 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 1, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 487) = orbitP14TargetCoeff 487 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv487 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 487))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 487)) ≃*
      CocycleGroup (orbitP14TargetCocycle 487)
        (orbitP14TargetCocycle_consistent 487) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 1, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 487)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_487))

theorem orbitP14_path_endpoint_488 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 0, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 488) = orbitP14TargetCoeff 488 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv488 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 488))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 488)) ≃*
      CocycleGroup (orbitP14TargetCocycle 488)
        (orbitP14TargetCocycle_consistent 488) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 0, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 488)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_488))

theorem orbitP14_path_endpoint_489 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 0, 2, 0, 1]
      (orbitP14RepresentativeCoeff 489) = orbitP14TargetCoeff 489 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv489 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 489))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 489)) ≃*
      CocycleGroup (orbitP14TargetCocycle 489)
        (orbitP14TargetCocycle_consistent 489) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 0, 2, 0, 1] (orbitP14RepresentativeCoeff 489)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_489))

theorem orbitP14_path_endpoint_490 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 1, 2, 1, 2, 0]
      (orbitP14RepresentativeCoeff 490) = orbitP14TargetCoeff 490 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv490 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 490))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 490)) ≃*
      CocycleGroup (orbitP14TargetCocycle 490)
        (orbitP14TargetCocycle_consistent 490) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 1, 2, 1, 2, 0] (orbitP14RepresentativeCoeff 490)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_490))

theorem orbitP14_path_endpoint_491 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 2]
      (orbitP14RepresentativeCoeff 491) = orbitP14TargetCoeff 491 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv491 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 491))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 491)) ≃*
      CocycleGroup (orbitP14TargetCocycle 491)
        (orbitP14TargetCocycle_consistent 491) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 2] (orbitP14RepresentativeCoeff 491)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_491))

theorem orbitP14_path_endpoint_492 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 1, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 492) = orbitP14TargetCoeff 492 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv492 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 492))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 492)) ≃*
      CocycleGroup (orbitP14TargetCocycle 492)
        (orbitP14TargetCocycle_consistent 492) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 1, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 492)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_492))

theorem orbitP14_path_endpoint_493 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 1, 0, 2, 1]
      (orbitP14RepresentativeCoeff 493) = orbitP14TargetCoeff 493 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv493 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 493))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 493)) ≃*
      CocycleGroup (orbitP14TargetCocycle 493)
        (orbitP14TargetCocycle_consistent 493) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 1, 0, 2, 1] (orbitP14RepresentativeCoeff 493)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_493))

theorem orbitP14_path_endpoint_494 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 494) = orbitP14TargetCoeff 494 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv494 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 494))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 494)) ≃*
      CocycleGroup (orbitP14TargetCocycle 494)
        (orbitP14TargetCocycle_consistent 494) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 494)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_494))

theorem orbitP14_path_endpoint_495 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 2, 1, 0]
      (orbitP14RepresentativeCoeff 495) = orbitP14TargetCoeff 495 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv495 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 495))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 495)) ≃*
      CocycleGroup (orbitP14TargetCocycle 495)
        (orbitP14TargetCocycle_consistent 495) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 2, 1, 0] (orbitP14RepresentativeCoeff 495)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_495))

end Smallgroups.UsefulTheorems.Order32Certificate
