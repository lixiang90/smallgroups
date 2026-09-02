/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart40

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 41. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_640 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 1, 0]
      (orbitP14RepresentativeCoeff 640) = orbitP14TargetCoeff 640 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv640 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 640))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 640)) ≃*
      CocycleGroup (orbitP14TargetCocycle 640)
        (orbitP14TargetCocycle_consistent 640) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 1, 0] (orbitP14RepresentativeCoeff 640)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_640))

theorem orbitP14_path_endpoint_641 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 2]
      (orbitP14RepresentativeCoeff 641) = orbitP14TargetCoeff 641 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv641 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 641))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 641)) ≃*
      CocycleGroup (orbitP14TargetCocycle 641)
        (orbitP14TargetCocycle_consistent 641) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 2] (orbitP14RepresentativeCoeff 641)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_641))

theorem orbitP14_path_endpoint_642 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 642) = orbitP14TargetCoeff 642 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv642 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 642))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 642)) ≃*
      CocycleGroup (orbitP14TargetCocycle 642)
        (orbitP14TargetCocycle_consistent 642) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 2, 0, 1, 2] (orbitP14RepresentativeCoeff 642)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_642))

theorem orbitP14_path_endpoint_643 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 2, 0, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 643) = orbitP14TargetCoeff 643 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv643 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 643))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 643)) ≃*
      CocycleGroup (orbitP14TargetCocycle 643)
        (orbitP14TargetCocycle_consistent 643) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 2, 0, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 643)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_643))

theorem orbitP14_path_endpoint_644 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 1, 1]
      (orbitP14RepresentativeCoeff 644) = orbitP14TargetCoeff 644 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv644 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 644))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 644)) ≃*
      CocycleGroup (orbitP14TargetCocycle 644)
        (orbitP14TargetCocycle_consistent 644) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 1, 1] (orbitP14RepresentativeCoeff 644)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_644))

theorem orbitP14_path_endpoint_645 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0]
      (orbitP14RepresentativeCoeff 645) = orbitP14TargetCoeff 645 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv645 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 645))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 645)) ≃*
      CocycleGroup (orbitP14TargetCocycle 645)
        (orbitP14TargetCocycle_consistent 645) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0] (orbitP14RepresentativeCoeff 645)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_645))

theorem orbitP14_path_endpoint_646 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 2, 1, 2, 1, 0, 1]
      (orbitP14RepresentativeCoeff 646) = orbitP14TargetCoeff 646 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv646 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 646))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 646)) ≃*
      CocycleGroup (orbitP14TargetCocycle 646)
        (orbitP14TargetCocycle_consistent 646) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 2, 1, 2, 1, 0, 1] (orbitP14RepresentativeCoeff 646)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_646))

theorem orbitP14_path_endpoint_647 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 1, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 647) = orbitP14TargetCoeff 647 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv647 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 647))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 647)) ≃*
      CocycleGroup (orbitP14TargetCocycle 647)
        (orbitP14TargetCocycle_consistent 647) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 1, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 647)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_647))

theorem orbitP14_path_endpoint_648 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 0]
      (orbitP14RepresentativeCoeff 648) = orbitP14TargetCoeff 648 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv648 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 648))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 648)) ≃*
      CocycleGroup (orbitP14TargetCocycle 648)
        (orbitP14TargetCocycle_consistent 648) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 0] (orbitP14RepresentativeCoeff 648)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_648))

theorem orbitP14_path_endpoint_649 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 649) = orbitP14TargetCoeff 649 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv649 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 649))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 649)) ≃*
      CocycleGroup (orbitP14TargetCocycle 649)
        (orbitP14TargetCocycle_consistent 649) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 649)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_649))

theorem orbitP14_path_endpoint_650 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 650) = orbitP14TargetCoeff 650 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv650 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 650))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 650)) ≃*
      CocycleGroup (orbitP14TargetCocycle 650)
        (orbitP14TargetCocycle_consistent 650) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 650)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_650))

theorem orbitP14_path_endpoint_651 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 651) = orbitP14TargetCoeff 651 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv651 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 651))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 651)) ≃*
      CocycleGroup (orbitP14TargetCocycle 651)
        (orbitP14TargetCocycle_consistent 651) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 651)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_651))

theorem orbitP14_path_endpoint_652 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 652) = orbitP14TargetCoeff 652 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv652 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 652))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 652)) ≃*
      CocycleGroup (orbitP14TargetCocycle 652)
        (orbitP14TargetCocycle_consistent 652) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 652)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_652))

theorem orbitP14_path_endpoint_653 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 653) = orbitP14TargetCoeff 653 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv653 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 653))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 653)) ≃*
      CocycleGroup (orbitP14TargetCocycle 653)
        (orbitP14TargetCocycle_consistent 653) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 653)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_653))

theorem orbitP14_path_endpoint_654 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 2, 0, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 654) = orbitP14TargetCoeff 654 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv654 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 654))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 654)) ≃*
      CocycleGroup (orbitP14TargetCocycle 654)
        (orbitP14TargetCocycle_consistent 654) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 2, 0, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 654)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_654))

theorem orbitP14_path_endpoint_655 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 0, 2, 0, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 655) = orbitP14TargetCoeff 655 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv655 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 655))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 655)) ≃*
      CocycleGroup (orbitP14TargetCocycle 655)
        (orbitP14TargetCocycle_consistent 655) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 0, 2, 0, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 655)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_655))

end Smallgroups.UsefulTheorems.Order32Certificate
