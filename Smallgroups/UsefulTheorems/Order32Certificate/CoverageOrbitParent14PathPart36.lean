/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart35

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 36. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_560 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 0, 1]
      (orbitP14RepresentativeCoeff 560) = orbitP14TargetCoeff 560 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv560 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 560))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 560)) ≃*
      CocycleGroup (orbitP14TargetCocycle 560)
        (orbitP14TargetCocycle_consistent 560) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 0, 1] (orbitP14RepresentativeCoeff 560)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_560))

theorem orbitP14_path_endpoint_561 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 2, 0, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 561) = orbitP14TargetCoeff 561 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv561 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 561))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 561)) ≃*
      CocycleGroup (orbitP14TargetCocycle 561)
        (orbitP14TargetCocycle_consistent 561) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 2, 0, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 561)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_561))

theorem orbitP14_path_endpoint_562 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 2, 1, 2]
      (orbitP14RepresentativeCoeff 562) = orbitP14TargetCoeff 562 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv562 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 562))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 562)) ≃*
      CocycleGroup (orbitP14TargetCocycle 562)
        (orbitP14TargetCocycle_consistent 562) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 2, 1, 2] (orbitP14RepresentativeCoeff 562)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_562))

theorem orbitP14_path_endpoint_563 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 0, 2, 1]
      (orbitP14RepresentativeCoeff 563) = orbitP14TargetCoeff 563 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv563 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 563))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 563)) ≃*
      CocycleGroup (orbitP14TargetCocycle 563)
        (orbitP14TargetCocycle_consistent 563) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 0, 2, 1] (orbitP14RepresentativeCoeff 563)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_563))

theorem orbitP14_path_endpoint_564 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 2, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 564) = orbitP14TargetCoeff 564 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv564 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 564))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 564)) ≃*
      CocycleGroup (orbitP14TargetCocycle 564)
        (orbitP14TargetCocycle_consistent 564) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 2, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 564)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_564))

theorem orbitP14_path_endpoint_565 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 0, 2, 0]
      (orbitP14RepresentativeCoeff 565) = orbitP14TargetCoeff 565 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv565 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 565))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 565)) ≃*
      CocycleGroup (orbitP14TargetCocycle 565)
        (orbitP14TargetCocycle_consistent 565) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 0, 2, 0] (orbitP14RepresentativeCoeff 565)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_565))

theorem orbitP14_path_endpoint_566 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 2, 0, 1, 2, 0, 1, 1]
      (orbitP14RepresentativeCoeff 566) = orbitP14TargetCoeff 566 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv566 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 566))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 566)) ≃*
      CocycleGroup (orbitP14TargetCocycle 566)
        (orbitP14TargetCocycle_consistent 566) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 2, 0, 1, 2, 0, 1, 1] (orbitP14RepresentativeCoeff 566)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_566))

theorem orbitP14_path_endpoint_567 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1]
      (orbitP14RepresentativeCoeff 567) = orbitP14TargetCoeff 567 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv567 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 567))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 567)) ≃*
      CocycleGroup (orbitP14TargetCocycle 567)
        (orbitP14TargetCocycle_consistent 567) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1] (orbitP14RepresentativeCoeff 567)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_567))

theorem orbitP14_path_endpoint_568 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 568) = orbitP14TargetCoeff 568 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv568 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 568))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 568)) ≃*
      CocycleGroup (orbitP14TargetCocycle 568)
        (orbitP14TargetCocycle_consistent 568) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 568)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_568))

theorem orbitP14_path_endpoint_569 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 569) = orbitP14TargetCoeff 569 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv569 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 569))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 569)) ≃*
      CocycleGroup (orbitP14TargetCocycle 569)
        (orbitP14TargetCocycle_consistent 569) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 569)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_569))

theorem orbitP14_path_endpoint_570 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 0, 1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 570) = orbitP14TargetCoeff 570 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv570 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 570))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 570)) ≃*
      CocycleGroup (orbitP14TargetCocycle 570)
        (orbitP14TargetCocycle_consistent 570) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 0, 1, 1, 2, 0] (orbitP14RepresentativeCoeff 570)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_570))

theorem orbitP14_path_endpoint_571 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 1, 1, 0, 2, 1]
      (orbitP14RepresentativeCoeff 571) = orbitP14TargetCoeff 571 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv571 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 571))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 571)) ≃*
      CocycleGroup (orbitP14TargetCocycle 571)
        (orbitP14TargetCocycle_consistent 571) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 1, 1, 0, 2, 1] (orbitP14RepresentativeCoeff 571)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_571))

theorem orbitP14_path_endpoint_572 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 1, 2, 1, 0, 1]
      (orbitP14RepresentativeCoeff 572) = orbitP14TargetCoeff 572 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv572 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 572))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 572)) ≃*
      CocycleGroup (orbitP14TargetCocycle 572)
        (orbitP14TargetCocycle_consistent 572) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 1, 2, 1, 0, 1] (orbitP14RepresentativeCoeff 572)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_572))

theorem orbitP14_path_endpoint_573 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 1, 2, 1, 2, 1]
      (orbitP14RepresentativeCoeff 573) = orbitP14TargetCoeff 573 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv573 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 573))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 573)) ≃*
      CocycleGroup (orbitP14TargetCocycle 573)
        (orbitP14TargetCocycle_consistent 573) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 1, 2, 1, 2, 1] (orbitP14RepresentativeCoeff 573)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_573))

theorem orbitP14_path_endpoint_574 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 2, 1, 2, 1, 1, 0]
      (orbitP14RepresentativeCoeff 574) = orbitP14TargetCoeff 574 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv574 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 574))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 574)) ≃*
      CocycleGroup (orbitP14TargetCocycle 574)
        (orbitP14TargetCocycle_consistent 574) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 2, 1, 2, 1, 1, 0] (orbitP14RepresentativeCoeff 574)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_574))

theorem orbitP14_path_endpoint_575 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 575) = orbitP14TargetCoeff 575 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv575 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 575))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 575)) ≃*
      CocycleGroup (orbitP14TargetCocycle 575)
        (orbitP14TargetCocycle_consistent 575) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 575)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_575))

end Smallgroups.UsefulTheorems.Order32Certificate
