/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart50

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 51. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_800 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 2, 1, 2, 1, 0, 2]
      (orbitP14RepresentativeCoeff 800) = orbitP14TargetCoeff 800 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv800 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 800))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 800)) ≃*
      CocycleGroup (orbitP14TargetCocycle 800)
        (orbitP14TargetCocycle_consistent 800) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 2, 1, 2, 1, 0, 2] (orbitP14RepresentativeCoeff 800)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_800))

theorem orbitP14_path_endpoint_801 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 0, 1, 1]
      (orbitP14RepresentativeCoeff 801) = orbitP14TargetCoeff 801 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv801 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 801))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 801)) ≃*
      CocycleGroup (orbitP14TargetCocycle 801)
        (orbitP14TargetCocycle_consistent 801) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 0, 1, 1] (orbitP14RepresentativeCoeff 801)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_801))

theorem orbitP14_path_endpoint_802 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 802) = orbitP14TargetCoeff 802 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv802 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 802))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 802)) ≃*
      CocycleGroup (orbitP14TargetCocycle 802)
        (orbitP14TargetCocycle_consistent 802) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2] (orbitP14RepresentativeCoeff 802)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_802))

theorem orbitP14_path_endpoint_803 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 1, 1, 0, 2]
      (orbitP14RepresentativeCoeff 803) = orbitP14TargetCoeff 803 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv803 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 803))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 803)) ≃*
      CocycleGroup (orbitP14TargetCocycle 803)
        (orbitP14TargetCocycle_consistent 803) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 1, 1, 0, 2] (orbitP14RepresentativeCoeff 803)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_803))

theorem orbitP14_path_endpoint_804 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 804) = orbitP14TargetCoeff 804 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv804 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 804))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 804)) ≃*
      CocycleGroup (orbitP14TargetCocycle 804)
        (orbitP14TargetCocycle_consistent 804) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 804)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_804))

theorem orbitP14_path_endpoint_805 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 2, 0, 1, 2, 1, 1, 0]
      (orbitP14RepresentativeCoeff 805) = orbitP14TargetCoeff 805 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv805 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 805))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 805)) ≃*
      CocycleGroup (orbitP14TargetCocycle 805)
        (orbitP14TargetCocycle_consistent 805) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 2, 0, 1, 2, 1, 1, 0] (orbitP14RepresentativeCoeff 805)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_805))

theorem orbitP14_path_endpoint_806 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 1, 2]
      (orbitP14RepresentativeCoeff 806) = orbitP14TargetCoeff 806 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv806 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 806))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 806)) ≃*
      CocycleGroup (orbitP14TargetCocycle 806)
        (orbitP14TargetCocycle_consistent 806) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 1, 2] (orbitP14RepresentativeCoeff 806)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_806))

theorem orbitP14_path_endpoint_807 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 807) = orbitP14TargetCoeff 807 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv807 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 807))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 807)) ≃*
      CocycleGroup (orbitP14TargetCocycle 807)
        (orbitP14TargetCocycle_consistent 807) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 2, 0] (orbitP14RepresentativeCoeff 807)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_807))

theorem orbitP14_path_endpoint_808 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 808) = orbitP14TargetCoeff 808 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv808 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 808))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 808)) ≃*
      CocycleGroup (orbitP14TargetCocycle 808)
        (orbitP14TargetCocycle_consistent 808) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 808)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_808))

theorem orbitP14_path_endpoint_809 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 1, 2]
      (orbitP14RepresentativeCoeff 809) = orbitP14TargetCoeff 809 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv809 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 809))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 809)) ≃*
      CocycleGroup (orbitP14TargetCocycle 809)
        (orbitP14TargetCocycle_consistent 809) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 1, 2] (orbitP14RepresentativeCoeff 809)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_809))

theorem orbitP14_path_endpoint_810 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 810) = orbitP14TargetCoeff 810 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv810 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 810))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 810)) ≃*
      CocycleGroup (orbitP14TargetCocycle 810)
        (orbitP14TargetCocycle_consistent 810) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 810)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_810))

theorem orbitP14_path_endpoint_811 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 2, 1]
      (orbitP14RepresentativeCoeff 811) = orbitP14TargetCoeff 811 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv811 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 811))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 811)) ≃*
      CocycleGroup (orbitP14TargetCocycle 811)
        (orbitP14TargetCocycle_consistent 811) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 2, 1] (orbitP14RepresentativeCoeff 811)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_811))

theorem orbitP14_path_endpoint_812 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 0, 1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 812) = orbitP14TargetCoeff 812 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv812 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 812))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 812)) ≃*
      CocycleGroup (orbitP14TargetCocycle 812)
        (orbitP14TargetCocycle_consistent 812) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 0, 1, 1, 2, 0] (orbitP14RepresentativeCoeff 812)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_812))

theorem orbitP14_path_endpoint_813 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2]
      (orbitP14RepresentativeCoeff 813) = orbitP14TargetCoeff 813 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv813 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 813))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 813)) ≃*
      CocycleGroup (orbitP14TargetCocycle 813)
        (orbitP14TargetCocycle_consistent 813) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2] (orbitP14RepresentativeCoeff 813)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_813))

theorem orbitP14_path_endpoint_814 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 814) = orbitP14TargetCoeff 814 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv814 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 814))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 814)) ≃*
      CocycleGroup (orbitP14TargetCocycle 814)
        (orbitP14TargetCocycle_consistent 814) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 814)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_814))

theorem orbitP14_path_endpoint_815 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 0, 2, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 815) = orbitP14TargetCoeff 815 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv815 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 815))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 815)) ≃*
      CocycleGroup (orbitP14TargetCocycle 815)
        (orbitP14TargetCocycle_consistent 815) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 0, 2, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 815)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_815))

end Smallgroups.UsefulTheorems.Order32Certificate
