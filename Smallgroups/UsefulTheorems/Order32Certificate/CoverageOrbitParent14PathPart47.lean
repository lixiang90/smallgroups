/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart46

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 47. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_736 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 2, 0, 1, 1]
      (orbitP14RepresentativeCoeff 736) = orbitP14TargetCoeff 736 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv736 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 736))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 736)) ≃*
      CocycleGroup (orbitP14TargetCocycle 736)
        (orbitP14TargetCocycle_consistent 736) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 2, 0, 1, 1] (orbitP14RepresentativeCoeff 736)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_736))

theorem orbitP14_path_endpoint_737 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 1, 2, 0, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 737) = orbitP14TargetCoeff 737 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv737 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 737))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 737)) ≃*
      CocycleGroup (orbitP14TargetCocycle 737)
        (orbitP14TargetCocycle_consistent 737) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 1, 2, 0, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 737)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_737))

theorem orbitP14_path_endpoint_738 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 0, 2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 738) = orbitP14TargetCoeff 738 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv738 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 738))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 738)) ≃*
      CocycleGroup (orbitP14TargetCocycle 738)
        (orbitP14TargetCocycle_consistent 738) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 0, 2, 0, 1, 2] (orbitP14RepresentativeCoeff 738)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_738))

theorem orbitP14_path_endpoint_739 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 0, 2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 739) = orbitP14TargetCoeff 739 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv739 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 739))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 739)) ≃*
      CocycleGroup (orbitP14TargetCocycle 739)
        (orbitP14TargetCocycle_consistent 739) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 0, 2, 0, 1, 2] (orbitP14RepresentativeCoeff 739)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_739))

theorem orbitP14_path_endpoint_740 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 740) = orbitP14TargetCoeff 740 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv740 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 740))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 740)) ≃*
      CocycleGroup (orbitP14TargetCocycle 740)
        (orbitP14TargetCocycle_consistent 740) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 740)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_740))

theorem orbitP14_path_endpoint_741 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 2, 1, 2, 1, 1, 0, 2, 1]
      (orbitP14RepresentativeCoeff 741) = orbitP14TargetCoeff 741 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv741 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 741))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 741)) ≃*
      CocycleGroup (orbitP14TargetCocycle 741)
        (orbitP14TargetCocycle_consistent 741) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 2, 1, 2, 1, 1, 0, 2, 1] (orbitP14RepresentativeCoeff 741)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_741))

theorem orbitP14_path_endpoint_742 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 0, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 742) = orbitP14TargetCoeff 742 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv742 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 742))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 742)) ≃*
      CocycleGroup (orbitP14TargetCocycle 742)
        (orbitP14TargetCocycle_consistent 742) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 0, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 742)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_742))

theorem orbitP14_path_endpoint_743 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 2, 1, 2, 0]
      (orbitP14RepresentativeCoeff 743) = orbitP14TargetCoeff 743 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv743 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 743))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 743)) ≃*
      CocycleGroup (orbitP14TargetCocycle 743)
        (orbitP14TargetCocycle_consistent 743) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 2, 1, 2, 0] (orbitP14RepresentativeCoeff 743)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_743))

theorem orbitP14_path_endpoint_744 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 2, 0, 1, 2, 0, 1, 0]
      (orbitP14RepresentativeCoeff 744) = orbitP14TargetCoeff 744 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv744 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 744))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 744)) ≃*
      CocycleGroup (orbitP14TargetCocycle 744)
        (orbitP14TargetCocycle_consistent 744) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 2, 0, 1, 2, 0, 1, 0] (orbitP14RepresentativeCoeff 744)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_744))

theorem orbitP14_path_endpoint_745 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 1, 1, 2]
      (orbitP14RepresentativeCoeff 745) = orbitP14TargetCoeff 745 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv745 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 745))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 745)) ≃*
      CocycleGroup (orbitP14TargetCocycle 745)
        (orbitP14TargetCocycle_consistent 745) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 1, 1, 2] (orbitP14RepresentativeCoeff 745)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_745))

theorem orbitP14_path_endpoint_746 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 746) = orbitP14TargetCoeff 746 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv746 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 746))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 746)) ≃*
      CocycleGroup (orbitP14TargetCocycle 746)
        (orbitP14TargetCocycle_consistent 746) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 746)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_746))

theorem orbitP14_path_endpoint_747 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 0, 2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 747) = orbitP14TargetCoeff 747 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv747 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 747))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 747)) ≃*
      CocycleGroup (orbitP14TargetCocycle 747)
        (orbitP14TargetCocycle_consistent 747) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 0, 2, 0, 1, 2] (orbitP14RepresentativeCoeff 747)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_747))

theorem orbitP14_path_endpoint_748 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 748) = orbitP14TargetCoeff 748 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv748 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 748))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 748)) ≃*
      CocycleGroup (orbitP14TargetCocycle 748)
        (orbitP14TargetCocycle_consistent 748) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 748)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_748))

theorem orbitP14_path_endpoint_749 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2]
      (orbitP14RepresentativeCoeff 749) = orbitP14TargetCoeff 749 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv749 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 749))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 749)) ≃*
      CocycleGroup (orbitP14TargetCocycle 749)
        (orbitP14TargetCocycle_consistent 749) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2] (orbitP14RepresentativeCoeff 749)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_749))

theorem orbitP14_path_endpoint_750 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 2, 1, 1, 1, 2]
      (orbitP14RepresentativeCoeff 750) = orbitP14TargetCoeff 750 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv750 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 750))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 750)) ≃*
      CocycleGroup (orbitP14TargetCocycle 750)
        (orbitP14TargetCocycle_consistent 750) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 2, 1, 1, 1, 2] (orbitP14RepresentativeCoeff 750)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_750))

theorem orbitP14_path_endpoint_751 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 1, 2, 1, 1, 1, 2]
      (orbitP14RepresentativeCoeff 751) = orbitP14TargetCoeff 751 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv751 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 751))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 751)) ≃*
      CocycleGroup (orbitP14TargetCocycle 751)
        (orbitP14TargetCocycle_consistent 751) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 1, 2, 1, 1, 1, 2] (orbitP14RepresentativeCoeff 751)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_751))

end Smallgroups.UsefulTheorems.Order32Certificate
