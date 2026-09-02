/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart33

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 34. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_528 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 528) = orbitP14TargetCoeff 528 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv528 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 528))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 528)) ≃*
      CocycleGroup (orbitP14TargetCocycle 528)
        (orbitP14TargetCocycle_consistent 528) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 1] (orbitP14RepresentativeCoeff 528)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_528))

theorem orbitP14_path_endpoint_529 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 529) = orbitP14TargetCoeff 529 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv529 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 529))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 529)) ≃*
      CocycleGroup (orbitP14TargetCocycle 529)
        (orbitP14TargetCocycle_consistent 529) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 2, 0] (orbitP14RepresentativeCoeff 529)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_529))

theorem orbitP14_path_endpoint_530 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 1]
      (orbitP14RepresentativeCoeff 530) = orbitP14TargetCoeff 530 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv530 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 530))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 530)) ≃*
      CocycleGroup (orbitP14TargetCocycle 530)
        (orbitP14TargetCocycle_consistent 530) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 1] (orbitP14RepresentativeCoeff 530)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_530))

theorem orbitP14_path_endpoint_531 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1]
      (orbitP14RepresentativeCoeff 531) = orbitP14TargetCoeff 531 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv531 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 531))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 531)) ≃*
      CocycleGroup (orbitP14TargetCocycle 531)
        (orbitP14TargetCocycle_consistent 531) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1] (orbitP14RepresentativeCoeff 531)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_531))

theorem orbitP14_path_endpoint_532 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 2, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 532) = orbitP14TargetCoeff 532 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv532 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 532))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 532)) ≃*
      CocycleGroup (orbitP14TargetCocycle 532)
        (orbitP14TargetCocycle_consistent 532) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 2, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 532)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_532))

theorem orbitP14_path_endpoint_533 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 2, 0, 1, 2, 0, 1, 0]
      (orbitP14RepresentativeCoeff 533) = orbitP14TargetCoeff 533 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv533 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 533))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 533)) ≃*
      CocycleGroup (orbitP14TargetCocycle 533)
        (orbitP14TargetCocycle_consistent 533) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 2, 0, 1, 2, 0, 1, 0] (orbitP14RepresentativeCoeff 533)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_533))

theorem orbitP14_path_endpoint_534 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 1, 2, 1, 0, 2]
      (orbitP14RepresentativeCoeff 534) = orbitP14TargetCoeff 534 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv534 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 534))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 534)) ≃*
      CocycleGroup (orbitP14TargetCocycle 534)
        (orbitP14TargetCocycle_consistent 534) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 1, 2, 1, 0, 2] (orbitP14RepresentativeCoeff 534)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_534))

theorem orbitP14_path_endpoint_535 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 535) = orbitP14TargetCoeff 535 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv535 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 535))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 535)) ≃*
      CocycleGroup (orbitP14TargetCocycle 535)
        (orbitP14TargetCocycle_consistent 535) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 535)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_535))

theorem orbitP14_path_endpoint_536 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2]
      (orbitP14RepresentativeCoeff 536) = orbitP14TargetCoeff 536 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv536 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 536))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 536)) ≃*
      CocycleGroup (orbitP14TargetCocycle 536)
        (orbitP14TargetCocycle_consistent 536) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2] (orbitP14RepresentativeCoeff 536)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_536))

theorem orbitP14_path_endpoint_537 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 1, 2]
      (orbitP14RepresentativeCoeff 537) = orbitP14TargetCoeff 537 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv537 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 537))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 537)) ≃*
      CocycleGroup (orbitP14TargetCocycle 537)
        (orbitP14TargetCocycle_consistent 537) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 1, 2] (orbitP14RepresentativeCoeff 537)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_537))

theorem orbitP14_path_endpoint_538 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 538) = orbitP14TargetCoeff 538 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv538 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 538))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 538)) ≃*
      CocycleGroup (orbitP14TargetCocycle 538)
        (orbitP14TargetCocycle_consistent 538) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 2, 1] (orbitP14RepresentativeCoeff 538)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_538))

theorem orbitP14_path_endpoint_539 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 539) = orbitP14TargetCoeff 539 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv539 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 539))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 539)) ≃*
      CocycleGroup (orbitP14TargetCocycle 539)
        (orbitP14TargetCocycle_consistent 539) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 2, 1] (orbitP14RepresentativeCoeff 539)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_539))

theorem orbitP14_path_endpoint_540 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 1, 1, 2, 1, 2]
      (orbitP14RepresentativeCoeff 540) = orbitP14TargetCoeff 540 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv540 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 540))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 540)) ≃*
      CocycleGroup (orbitP14TargetCocycle 540)
        (orbitP14TargetCocycle_consistent 540) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 1, 1, 2, 1, 2] (orbitP14RepresentativeCoeff 540)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_540))

theorem orbitP14_path_endpoint_541 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 541) = orbitP14TargetCoeff 541 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv541 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 541))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 541)) ≃*
      CocycleGroup (orbitP14TargetCocycle 541)
        (orbitP14TargetCocycle_consistent 541) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 541)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_541))

theorem orbitP14_path_endpoint_542 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 2, 0, 1, 2, 0, 1, 0]
      (orbitP14RepresentativeCoeff 542) = orbitP14TargetCoeff 542 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv542 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 542))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 542)) ≃*
      CocycleGroup (orbitP14TargetCocycle 542)
        (orbitP14TargetCocycle_consistent 542) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 2, 0, 1, 2, 0, 1, 0] (orbitP14RepresentativeCoeff 542)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_542))

theorem orbitP14_path_endpoint_543 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 0, 2, 0, 1, 2, 0, 1, 0]
      (orbitP14RepresentativeCoeff 543) = orbitP14TargetCoeff 543 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv543 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 543))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 543)) ≃*
      CocycleGroup (orbitP14TargetCocycle 543)
        (orbitP14TargetCocycle_consistent 543) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 0, 2, 0, 1, 2, 0, 1, 0] (orbitP14RepresentativeCoeff 543)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_543))

end Smallgroups.UsefulTheorems.Order32Certificate
