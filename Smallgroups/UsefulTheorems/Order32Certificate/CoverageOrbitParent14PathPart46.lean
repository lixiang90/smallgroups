/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart45

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 46. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_720 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 720) = orbitP14TargetCoeff 720 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv720 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 720))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 720)) ≃*
      CocycleGroup (orbitP14TargetCocycle 720)
        (orbitP14TargetCocycle_consistent 720) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 720)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_720))

theorem orbitP14_path_endpoint_721 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 1, 2, 1, 2]
      (orbitP14RepresentativeCoeff 721) = orbitP14TargetCoeff 721 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv721 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 721))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 721)) ≃*
      CocycleGroup (orbitP14TargetCocycle 721)
        (orbitP14TargetCocycle_consistent 721) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 1, 2, 1, 2] (orbitP14RepresentativeCoeff 721)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_721))

theorem orbitP14_path_endpoint_722 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 722) = orbitP14TargetCoeff 722 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv722 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 722))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 722)) ≃*
      CocycleGroup (orbitP14TargetCocycle 722)
        (orbitP14TargetCocycle_consistent 722) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 722)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_722))

theorem orbitP14_path_endpoint_723 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 0, 2, 0, 1, 2, 1, 0, 1]
      (orbitP14RepresentativeCoeff 723) = orbitP14TargetCoeff 723 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv723 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 723))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 723)) ≃*
      CocycleGroup (orbitP14TargetCocycle 723)
        (orbitP14TargetCocycle_consistent 723) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 0, 2, 0, 1, 2, 1, 0, 1] (orbitP14RepresentativeCoeff 723)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_723))

theorem orbitP14_path_endpoint_724 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 724) = orbitP14TargetCoeff 724 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv724 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 724))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 724)) ≃*
      CocycleGroup (orbitP14TargetCocycle 724)
        (orbitP14TargetCocycle_consistent 724) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 724)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_724))

theorem orbitP14_path_endpoint_725 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 0, 1, 2, 1, 2, 1]
      (orbitP14RepresentativeCoeff 725) = orbitP14TargetCoeff 725 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv725 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 725))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 725)) ≃*
      CocycleGroup (orbitP14TargetCocycle 725)
        (orbitP14TargetCocycle_consistent 725) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 0, 1, 2, 1, 2, 1] (orbitP14RepresentativeCoeff 725)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_725))

theorem orbitP14_path_endpoint_726 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 1, 2, 0, 1, 0]
      (orbitP14RepresentativeCoeff 726) = orbitP14TargetCoeff 726 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv726 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 726))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 726)) ≃*
      CocycleGroup (orbitP14TargetCocycle 726)
        (orbitP14TargetCocycle_consistent 726) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 1, 2, 0, 1, 0] (orbitP14RepresentativeCoeff 726)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_726))

theorem orbitP14_path_endpoint_727 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 727) = orbitP14TargetCoeff 727 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv727 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 727))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 727)) ≃*
      CocycleGroup (orbitP14TargetCocycle 727)
        (orbitP14TargetCocycle_consistent 727) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 727)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_727))

theorem orbitP14_path_endpoint_728 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 2, 0, 1, 2, 1, 2, 0]
      (orbitP14RepresentativeCoeff 728) = orbitP14TargetCoeff 728 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv728 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 728))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 728)) ≃*
      CocycleGroup (orbitP14TargetCocycle 728)
        (orbitP14TargetCocycle_consistent 728) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 2, 0, 1, 2, 1, 2, 0] (orbitP14RepresentativeCoeff 728)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_728))

theorem orbitP14_path_endpoint_729 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 729) = orbitP14TargetCoeff 729 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv729 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 729))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 729)) ≃*
      CocycleGroup (orbitP14TargetCocycle 729)
        (orbitP14TargetCocycle_consistent 729) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 2, 0] (orbitP14RepresentativeCoeff 729)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_729))

theorem orbitP14_path_endpoint_730 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 730) = orbitP14TargetCoeff 730 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv730 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 730))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 730)) ≃*
      CocycleGroup (orbitP14TargetCocycle 730)
        (orbitP14TargetCocycle_consistent 730) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 730)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_730))

theorem orbitP14_path_endpoint_731 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 2, 1, 1, 2]
      (orbitP14RepresentativeCoeff 731) = orbitP14TargetCoeff 731 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv731 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 731))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 731)) ≃*
      CocycleGroup (orbitP14TargetCocycle 731)
        (orbitP14TargetCocycle_consistent 731) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 2, 1, 1, 2] (orbitP14RepresentativeCoeff 731)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_731))

theorem orbitP14_path_endpoint_732 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 1, 2, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 732) = orbitP14TargetCoeff 732 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv732 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 732))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 732)) ≃*
      CocycleGroup (orbitP14TargetCocycle 732)
        (orbitP14TargetCocycle_consistent 732) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 1, 2, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 732)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_732))

theorem orbitP14_path_endpoint_733 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 1, 2, 0, 1, 0, 2, 1]
      (orbitP14RepresentativeCoeff 733) = orbitP14TargetCoeff 733 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv733 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 733))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 733)) ≃*
      CocycleGroup (orbitP14TargetCocycle 733)
        (orbitP14TargetCocycle_consistent 733) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 1, 2, 0, 1, 0, 2, 1] (orbitP14RepresentativeCoeff 733)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_733))

theorem orbitP14_path_endpoint_734 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 1, 2, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 734) = orbitP14TargetCoeff 734 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv734 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 734))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 734)) ≃*
      CocycleGroup (orbitP14TargetCocycle 734)
        (orbitP14TargetCocycle_consistent 734) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 1, 2, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 734)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_734))

theorem orbitP14_path_endpoint_735 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 1, 2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 735) = orbitP14TargetCoeff 735 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv735 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 735))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 735)) ≃*
      CocycleGroup (orbitP14TargetCocycle 735)
        (orbitP14TargetCocycle_consistent 735) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 1, 2, 0, 1, 2] (orbitP14RepresentativeCoeff 735)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_735))

end Smallgroups.UsefulTheorems.Order32Certificate
