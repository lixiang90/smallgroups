/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart41

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 42. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_656 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 2, 0, 1, 1]
      (orbitP14RepresentativeCoeff 656) = orbitP14TargetCoeff 656 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv656 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 656))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 656)) ≃*
      CocycleGroup (orbitP14TargetCocycle 656)
        (orbitP14TargetCocycle_consistent 656) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 2, 0, 1, 1] (orbitP14RepresentativeCoeff 656)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_656))

theorem orbitP14_path_endpoint_657 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 657) = orbitP14TargetCoeff 657 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv657 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 657))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 657)) ≃*
      CocycleGroup (orbitP14TargetCocycle 657)
        (orbitP14TargetCocycle_consistent 657) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 657)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_657))

theorem orbitP14_path_endpoint_658 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 1, 2, 1, 2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 658) = orbitP14TargetCoeff 658 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv658 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 658))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 658)) ≃*
      CocycleGroup (orbitP14TargetCocycle 658)
        (orbitP14TargetCocycle_consistent 658) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 1, 2, 1, 2, 0, 1, 2] (orbitP14RepresentativeCoeff 658)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_658))

theorem orbitP14_path_endpoint_659 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 659) = orbitP14TargetCoeff 659 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv659 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 659))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 659)) ≃*
      CocycleGroup (orbitP14TargetCocycle 659)
        (orbitP14TargetCocycle_consistent 659) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 2, 0, 1, 2] (orbitP14RepresentativeCoeff 659)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_659))

theorem orbitP14_path_endpoint_660 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 1, 2, 1, 2, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 660) = orbitP14TargetCoeff 660 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv660 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 660))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 660)) ≃*
      CocycleGroup (orbitP14TargetCocycle 660)
        (orbitP14TargetCocycle_consistent 660) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 1, 2, 1, 2, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 660)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_660))

theorem orbitP14_path_endpoint_661 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 2, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 661) = orbitP14TargetCoeff 661 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv661 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 661))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 661)) ≃*
      CocycleGroup (orbitP14TargetCocycle 661)
        (orbitP14TargetCocycle_consistent 661) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 2, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 661)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_661))

theorem orbitP14_path_endpoint_662 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 1, 1, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 662) = orbitP14TargetCoeff 662 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv662 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 662))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 662)) ≃*
      CocycleGroup (orbitP14TargetCocycle 662)
        (orbitP14TargetCocycle_consistent 662) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 1, 1, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 662)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_662))

theorem orbitP14_path_endpoint_663 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 0, 2, 0, 1]
      (orbitP14RepresentativeCoeff 663) = orbitP14TargetCoeff 663 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv663 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 663))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 663)) ≃*
      CocycleGroup (orbitP14TargetCocycle 663)
        (orbitP14TargetCocycle_consistent 663) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 0, 2, 0, 1] (orbitP14RepresentativeCoeff 663)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_663))

theorem orbitP14_path_endpoint_664 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 664) = orbitP14TargetCoeff 664 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv664 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 664))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 664)) ≃*
      CocycleGroup (orbitP14TargetCocycle 664)
        (orbitP14TargetCocycle_consistent 664) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 664)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_664))

theorem orbitP14_path_endpoint_665 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 1, 2, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 665) = orbitP14TargetCoeff 665 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv665 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 665))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 665)) ≃*
      CocycleGroup (orbitP14TargetCocycle 665)
        (orbitP14TargetCocycle_consistent 665) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 1, 2, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 665)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_665))

theorem orbitP14_path_endpoint_666 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 0, 2, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 666) = orbitP14TargetCoeff 666 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv666 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 666))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 666)) ≃*
      CocycleGroup (orbitP14TargetCocycle 666)
        (orbitP14TargetCocycle_consistent 666) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 0, 2, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 666)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_666))

theorem orbitP14_path_endpoint_667 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 1, 1, 2, 1, 1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 667) = orbitP14TargetCoeff 667 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv667 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 667))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 667)) ≃*
      CocycleGroup (orbitP14TargetCocycle 667)
        (orbitP14TargetCocycle_consistent 667) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 1, 1, 2, 1, 1, 1, 2, 0] (orbitP14RepresentativeCoeff 667)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_667))

theorem orbitP14_path_endpoint_668 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 0, 2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 668) = orbitP14TargetCoeff 668 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv668 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 668))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 668)) ≃*
      CocycleGroup (orbitP14TargetCocycle 668)
        (orbitP14TargetCocycle_consistent 668) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 0, 2, 0, 1, 2] (orbitP14RepresentativeCoeff 668)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_668))

theorem orbitP14_path_endpoint_669 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 1, 1, 2, 1, 1, 1, 2]
      (orbitP14RepresentativeCoeff 669) = orbitP14TargetCoeff 669 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv669 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 669))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 669)) ≃*
      CocycleGroup (orbitP14TargetCocycle 669)
        (orbitP14TargetCocycle_consistent 669) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 1, 1, 2, 1, 1, 1, 2] (orbitP14RepresentativeCoeff 669)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_669))

theorem orbitP14_path_endpoint_670 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 0, 2, 0, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 670) = orbitP14TargetCoeff 670 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv670 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 670))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 670)) ≃*
      CocycleGroup (orbitP14TargetCocycle 670)
        (orbitP14TargetCocycle_consistent 670) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 0, 2, 0, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 670)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_670))

theorem orbitP14_path_endpoint_671 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 671) = orbitP14TargetCoeff 671 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv671 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 671))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 671)) ≃*
      CocycleGroup (orbitP14TargetCocycle 671)
        (orbitP14TargetCocycle_consistent 671) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 671)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_671))

end Smallgroups.UsefulTheorems.Order32Certificate
