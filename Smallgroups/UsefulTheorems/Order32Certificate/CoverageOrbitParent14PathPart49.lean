/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart48

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 49. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_768 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 0]
      (orbitP14RepresentativeCoeff 768) = orbitP14TargetCoeff 768 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv768 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 768))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 768)) ≃*
      CocycleGroup (orbitP14TargetCocycle 768)
        (orbitP14TargetCocycle_consistent 768) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 0] (orbitP14RepresentativeCoeff 768)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_768))

theorem orbitP14_path_endpoint_769 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 2, 0]
      (orbitP14RepresentativeCoeff 769) = orbitP14TargetCoeff 769 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv769 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 769))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 769)) ≃*
      CocycleGroup (orbitP14TargetCocycle 769)
        (orbitP14TargetCocycle_consistent 769) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 2, 0] (orbitP14RepresentativeCoeff 769)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_769))

theorem orbitP14_path_endpoint_770 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2]
      (orbitP14RepresentativeCoeff 770) = orbitP14TargetCoeff 770 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv770 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 770))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 770)) ≃*
      CocycleGroup (orbitP14TargetCocycle 770)
        (orbitP14TargetCocycle_consistent 770) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2] (orbitP14RepresentativeCoeff 770)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_770))

theorem orbitP14_path_endpoint_771 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 2, 1, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 771) = orbitP14TargetCoeff 771 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv771 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 771))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 771)) ≃*
      CocycleGroup (orbitP14TargetCocycle 771)
        (orbitP14TargetCocycle_consistent 771) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 2, 1, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 771)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_771))

theorem orbitP14_path_endpoint_772 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 2, 0]
      (orbitP14RepresentativeCoeff 772) = orbitP14TargetCoeff 772 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv772 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 772))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 772)) ≃*
      CocycleGroup (orbitP14TargetCocycle 772)
        (orbitP14TargetCocycle_consistent 772) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 2, 0] (orbitP14RepresentativeCoeff 772)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_772))

theorem orbitP14_path_endpoint_773 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 2]
      (orbitP14RepresentativeCoeff 773) = orbitP14TargetCoeff 773 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv773 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 773))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 773)) ≃*
      CocycleGroup (orbitP14TargetCocycle 773)
        (orbitP14TargetCocycle_consistent 773) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 2] (orbitP14RepresentativeCoeff 773)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_773))

theorem orbitP14_path_endpoint_774 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 774) = orbitP14TargetCoeff 774 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv774 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 774))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 774)) ≃*
      CocycleGroup (orbitP14TargetCocycle 774)
        (orbitP14TargetCocycle_consistent 774) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 774)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_774))

theorem orbitP14_path_endpoint_775 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 1, 2, 1, 2]
      (orbitP14RepresentativeCoeff 775) = orbitP14TargetCoeff 775 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv775 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 775))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 775)) ≃*
      CocycleGroup (orbitP14TargetCocycle 775)
        (orbitP14TargetCocycle_consistent 775) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 1, 2, 1, 2] (orbitP14RepresentativeCoeff 775)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_775))

theorem orbitP14_path_endpoint_776 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2]
      (orbitP14RepresentativeCoeff 776) = orbitP14TargetCoeff 776 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv776 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 776))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 776)) ≃*
      CocycleGroup (orbitP14TargetCocycle 776)
        (orbitP14TargetCocycle_consistent 776) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2] (orbitP14RepresentativeCoeff 776)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_776))

theorem orbitP14_path_endpoint_777 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 1, 1, 2]
      (orbitP14RepresentativeCoeff 777) = orbitP14TargetCoeff 777 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv777 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 777))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 777)) ≃*
      CocycleGroup (orbitP14TargetCocycle 777)
        (orbitP14TargetCocycle_consistent 777) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 1, 1, 2] (orbitP14RepresentativeCoeff 777)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_777))

theorem orbitP14_path_endpoint_778 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 778) = orbitP14TargetCoeff 778 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv778 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 778))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 778)) ≃*
      CocycleGroup (orbitP14TargetCocycle 778)
        (orbitP14TargetCocycle_consistent 778) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 2] (orbitP14RepresentativeCoeff 778)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_778))

theorem orbitP14_path_endpoint_779 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 1, 2, 1, 2, 0]
      (orbitP14RepresentativeCoeff 779) = orbitP14TargetCoeff 779 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv779 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 779))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 779)) ≃*
      CocycleGroup (orbitP14TargetCocycle 779)
        (orbitP14TargetCocycle_consistent 779) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 1, 2, 1, 2, 0] (orbitP14RepresentativeCoeff 779)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_779))

theorem orbitP14_path_endpoint_780 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1]
      (orbitP14RepresentativeCoeff 780) = orbitP14TargetCoeff 780 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv780 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 780))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 780)) ≃*
      CocycleGroup (orbitP14TargetCocycle 780)
        (orbitP14TargetCocycle_consistent 780) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1] (orbitP14RepresentativeCoeff 780)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_780))

theorem orbitP14_path_endpoint_781 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 0, 1, 0]
      (orbitP14RepresentativeCoeff 781) = orbitP14TargetCoeff 781 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv781 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 781))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 781)) ≃*
      CocycleGroup (orbitP14TargetCocycle 781)
        (orbitP14TargetCocycle_consistent 781) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 0, 1, 0] (orbitP14RepresentativeCoeff 781)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_781))

theorem orbitP14_path_endpoint_782 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 1, 2, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 782) = orbitP14TargetCoeff 782 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv782 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 782))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 782)) ≃*
      CocycleGroup (orbitP14TargetCocycle 782)
        (orbitP14TargetCocycle_consistent 782) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 1, 2, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 782)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_782))

theorem orbitP14_path_endpoint_783 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 783) = orbitP14TargetCoeff 783 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv783 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 783))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 783)) ≃*
      CocycleGroup (orbitP14TargetCocycle 783)
        (orbitP14TargetCocycle_consistent 783) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 783)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_783))

end Smallgroups.UsefulTheorems.Order32Certificate
