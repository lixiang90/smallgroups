/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart34

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 35. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_544 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 1, 0, 2, 0, 1, 1]
      (orbitP14RepresentativeCoeff 544) = orbitP14TargetCoeff 544 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv544 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 544))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 544)) ≃*
      CocycleGroup (orbitP14TargetCocycle 544)
        (orbitP14TargetCocycle_consistent 544) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 1, 0, 2, 0, 1, 1] (orbitP14RepresentativeCoeff 544)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_544))

theorem orbitP14_path_endpoint_545 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 1, 2, 1, 2, 0, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 545) = orbitP14TargetCoeff 545 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv545 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 545))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 545)) ≃*
      CocycleGroup (orbitP14TargetCocycle 545)
        (orbitP14TargetCocycle_consistent 545) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 1, 2, 1, 2, 0, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 545)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_545))

theorem orbitP14_path_endpoint_546 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 2, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 546) = orbitP14TargetCoeff 546 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv546 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 546))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 546)) ≃*
      CocycleGroup (orbitP14TargetCocycle 546)
        (orbitP14TargetCocycle_consistent 546) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 2, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 546)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_546))

theorem orbitP14_path_endpoint_547 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 2, 1, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 547) = orbitP14TargetCoeff 547 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv547 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 547))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 547)) ≃*
      CocycleGroup (orbitP14TargetCocycle 547)
        (orbitP14TargetCocycle_consistent 547) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 2, 1, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 547)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_547))

theorem orbitP14_path_endpoint_548 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 2, 1, 2, 1, 1, 0]
      (orbitP14RepresentativeCoeff 548) = orbitP14TargetCoeff 548 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv548 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 548))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 548)) ≃*
      CocycleGroup (orbitP14TargetCocycle 548)
        (orbitP14TargetCocycle_consistent 548) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 2, 1, 2, 1, 1, 0] (orbitP14RepresentativeCoeff 548)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_548))

theorem orbitP14_path_endpoint_549 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 2, 1, 2, 0, 1, 1]
      (orbitP14RepresentativeCoeff 549) = orbitP14TargetCoeff 549 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv549 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 549))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 549)) ≃*
      CocycleGroup (orbitP14TargetCocycle 549)
        (orbitP14TargetCocycle_consistent 549) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 2, 1, 2, 0, 1, 1] (orbitP14RepresentativeCoeff 549)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_549))

theorem orbitP14_path_endpoint_550 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 1, 0, 2, 0, 1]
      (orbitP14RepresentativeCoeff 550) = orbitP14TargetCoeff 550 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv550 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 550))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 550)) ≃*
      CocycleGroup (orbitP14TargetCocycle 550)
        (orbitP14TargetCocycle_consistent 550) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 1, 0, 2, 0, 1] (orbitP14RepresentativeCoeff 550)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_550))

theorem orbitP14_path_endpoint_551 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 2, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 551) = orbitP14TargetCoeff 551 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv551 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 551))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 551)) ≃*
      CocycleGroup (orbitP14TargetCocycle 551)
        (orbitP14TargetCocycle_consistent 551) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 2, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 551)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_551))

theorem orbitP14_path_endpoint_552 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 1, 0, 2]
      (orbitP14RepresentativeCoeff 552) = orbitP14TargetCoeff 552 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv552 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 552))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 552)) ≃*
      CocycleGroup (orbitP14TargetCocycle 552)
        (orbitP14TargetCocycle_consistent 552) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 1, 0, 2] (orbitP14RepresentativeCoeff 552)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_552))

theorem orbitP14_path_endpoint_553 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 553) = orbitP14TargetCoeff 553 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv553 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 553))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 553)) ≃*
      CocycleGroup (orbitP14TargetCocycle 553)
        (orbitP14TargetCocycle_consistent 553) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 553)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_553))

theorem orbitP14_path_endpoint_554 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 2]
      (orbitP14RepresentativeCoeff 554) = orbitP14TargetCoeff 554 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv554 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 554))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 554)) ≃*
      CocycleGroup (orbitP14TargetCocycle 554)
        (orbitP14TargetCocycle_consistent 554) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 2] (orbitP14RepresentativeCoeff 554)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_554))

theorem orbitP14_path_endpoint_555 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2]
      (orbitP14RepresentativeCoeff 555) = orbitP14TargetCoeff 555 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv555 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 555))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 555)) ≃*
      CocycleGroup (orbitP14TargetCocycle 555)
        (orbitP14TargetCocycle_consistent 555) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2] (orbitP14RepresentativeCoeff 555)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_555))

theorem orbitP14_path_endpoint_556 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 2, 0]
      (orbitP14RepresentativeCoeff 556) = orbitP14TargetCoeff 556 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv556 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 556))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 556)) ≃*
      CocycleGroup (orbitP14TargetCocycle 556)
        (orbitP14TargetCocycle_consistent 556) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 2, 0] (orbitP14RepresentativeCoeff 556)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_556))

theorem orbitP14_path_endpoint_557 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1]
      (orbitP14RepresentativeCoeff 557) = orbitP14TargetCoeff 557 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv557 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 557))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 557)) ≃*
      CocycleGroup (orbitP14TargetCocycle 557)
        (orbitP14TargetCocycle_consistent 557) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1] (orbitP14RepresentativeCoeff 557)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_557))

theorem orbitP14_path_endpoint_558 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 1, 0, 1]
      (orbitP14RepresentativeCoeff 558) = orbitP14TargetCoeff 558 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv558 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 558))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 558)) ≃*
      CocycleGroup (orbitP14TargetCocycle 558)
        (orbitP14TargetCocycle_consistent 558) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 1, 0, 1] (orbitP14RepresentativeCoeff 558)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_558))

theorem orbitP14_path_endpoint_559 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1]
      (orbitP14RepresentativeCoeff 559) = orbitP14TargetCoeff 559 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv559 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 559))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 559)) ≃*
      CocycleGroup (orbitP14TargetCocycle 559)
        (orbitP14TargetCocycle_consistent 559) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1] (orbitP14RepresentativeCoeff 559)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_559))

end Smallgroups.UsefulTheorems.Order32Certificate
