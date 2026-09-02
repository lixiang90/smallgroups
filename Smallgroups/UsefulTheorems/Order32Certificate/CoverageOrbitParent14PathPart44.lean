/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart43

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 44. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_688 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 1]
      (orbitP14RepresentativeCoeff 688) = orbitP14TargetCoeff 688 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv688 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 688))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 688)) ≃*
      CocycleGroup (orbitP14TargetCocycle 688)
        (orbitP14TargetCocycle_consistent 688) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 1] (orbitP14RepresentativeCoeff 688)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_688))

theorem orbitP14_path_endpoint_689 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 2, 0, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 689) = orbitP14TargetCoeff 689 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv689 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 689))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 689)) ≃*
      CocycleGroup (orbitP14TargetCocycle 689)
        (orbitP14TargetCocycle_consistent 689) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 2, 0, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 689)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_689))

theorem orbitP14_path_endpoint_690 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 0, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 690) = orbitP14TargetCoeff 690 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv690 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 690))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 690)) ≃*
      CocycleGroup (orbitP14TargetCocycle 690)
        (orbitP14TargetCocycle_consistent 690) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 0, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 690)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_690))

theorem orbitP14_path_endpoint_691 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 0, 2, 1, 1]
      (orbitP14RepresentativeCoeff 691) = orbitP14TargetCoeff 691 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv691 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 691))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 691)) ≃*
      CocycleGroup (orbitP14TargetCocycle 691)
        (orbitP14TargetCocycle_consistent 691) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 0, 2, 1, 1] (orbitP14RepresentativeCoeff 691)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_691))

theorem orbitP14_path_endpoint_692 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 2, 1, 1, 0, 2]
      (orbitP14RepresentativeCoeff 692) = orbitP14TargetCoeff 692 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv692 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 692))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 692)) ≃*
      CocycleGroup (orbitP14TargetCocycle 692)
        (orbitP14TargetCocycle_consistent 692) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 2, 1, 1, 0, 2] (orbitP14RepresentativeCoeff 692)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_692))

theorem orbitP14_path_endpoint_693 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 1, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 693) = orbitP14TargetCoeff 693 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv693 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 693))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 693)) ≃*
      CocycleGroup (orbitP14TargetCocycle 693)
        (orbitP14TargetCocycle_consistent 693) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 1, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 693)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_693))

theorem orbitP14_path_endpoint_694 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1]
      (orbitP14RepresentativeCoeff 694) = orbitP14TargetCoeff 694 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv694 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 694))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 694)) ≃*
      CocycleGroup (orbitP14TargetCocycle 694)
        (orbitP14TargetCocycle_consistent 694) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1] (orbitP14RepresentativeCoeff 694)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_694))

theorem orbitP14_path_endpoint_695 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 2, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 695) = orbitP14TargetCoeff 695 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv695 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 695))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 695)) ≃*
      CocycleGroup (orbitP14TargetCocycle 695)
        (orbitP14TargetCocycle_consistent 695) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 2, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 695)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_695))

theorem orbitP14_path_endpoint_696 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 1, 2, 0, 1, 0, 2]
      (orbitP14RepresentativeCoeff 696) = orbitP14TargetCoeff 696 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv696 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 696))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 696)) ≃*
      CocycleGroup (orbitP14TargetCocycle 696)
        (orbitP14TargetCocycle_consistent 696) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 1, 2, 0, 1, 0, 2] (orbitP14RepresentativeCoeff 696)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_696))

theorem orbitP14_path_endpoint_697 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 1, 2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 697) = orbitP14TargetCoeff 697 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv697 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 697))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 697)) ≃*
      CocycleGroup (orbitP14TargetCocycle 697)
        (orbitP14TargetCocycle_consistent 697) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 1, 2, 0, 1, 2] (orbitP14RepresentativeCoeff 697)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_697))

theorem orbitP14_path_endpoint_698 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 2, 0, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 698) = orbitP14TargetCoeff 698 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv698 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 698))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 698)) ≃*
      CocycleGroup (orbitP14TargetCocycle 698)
        (orbitP14TargetCocycle_consistent 698) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 2, 0, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 698)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_698))

theorem orbitP14_path_endpoint_699 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 1, 2, 1, 1, 2, 1, 2]
      (orbitP14RepresentativeCoeff 699) = orbitP14TargetCoeff 699 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv699 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 699))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 699)) ≃*
      CocycleGroup (orbitP14TargetCocycle 699)
        (orbitP14TargetCocycle_consistent 699) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 1, 2, 1, 1, 2, 1, 2] (orbitP14RepresentativeCoeff 699)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_699))

theorem orbitP14_path_endpoint_700 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 2, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 700) = orbitP14TargetCoeff 700 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv700 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 700))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 700)) ≃*
      CocycleGroup (orbitP14TargetCocycle 700)
        (orbitP14TargetCocycle_consistent 700) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 2, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 700)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_700))

theorem orbitP14_path_endpoint_701 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 1, 2, 0, 1, 0, 2]
      (orbitP14RepresentativeCoeff 701) = orbitP14TargetCoeff 701 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv701 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 701))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 701)) ≃*
      CocycleGroup (orbitP14TargetCocycle 701)
        (orbitP14TargetCocycle_consistent 701) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 1, 2, 0, 1, 0, 2] (orbitP14RepresentativeCoeff 701)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_701))

theorem orbitP14_path_endpoint_702 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 1, 2, 1, 2, 1, 1, 0, 2]
      (orbitP14RepresentativeCoeff 702) = orbitP14TargetCoeff 702 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv702 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 702))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 702)) ≃*
      CocycleGroup (orbitP14TargetCocycle 702)
        (orbitP14TargetCocycle_consistent 702) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 1, 2, 1, 2, 1, 1, 0, 2] (orbitP14RepresentativeCoeff 702)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_702))

theorem orbitP14_path_endpoint_703 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 1, 2, 1, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 703) = orbitP14TargetCoeff 703 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv703 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 703))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 703)) ≃*
      CocycleGroup (orbitP14TargetCocycle 703)
        (orbitP14TargetCocycle_consistent 703) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 1, 2, 1, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 703)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_703))

end Smallgroups.UsefulTheorems.Order32Certificate
