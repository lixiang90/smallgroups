/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart49

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 50. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_784 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 0, 1, 1, 0, 1]
      (orbitP14RepresentativeCoeff 784) = orbitP14TargetCoeff 784 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv784 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 784))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 784)) ≃*
      CocycleGroup (orbitP14TargetCocycle 784)
        (orbitP14TargetCocycle_consistent 784) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 0, 1, 1, 0, 1] (orbitP14RepresentativeCoeff 784)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_784))

theorem orbitP14_path_endpoint_785 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 785) = orbitP14TargetCoeff 785 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv785 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 785))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 785)) ≃*
      CocycleGroup (orbitP14TargetCocycle 785)
        (orbitP14TargetCocycle_consistent 785) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 785)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_785))

theorem orbitP14_path_endpoint_786 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 2, 1, 2, 1]
      (orbitP14RepresentativeCoeff 786) = orbitP14TargetCoeff 786 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv786 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 786))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 786)) ≃*
      CocycleGroup (orbitP14TargetCocycle 786)
        (orbitP14TargetCocycle_consistent 786) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 2, 1, 2, 1] (orbitP14RepresentativeCoeff 786)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_786))

theorem orbitP14_path_endpoint_787 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 1, 2, 1, 0, 1, 2]
      (orbitP14RepresentativeCoeff 787) = orbitP14TargetCoeff 787 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv787 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 787))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 787)) ≃*
      CocycleGroup (orbitP14TargetCocycle 787)
        (orbitP14TargetCocycle_consistent 787) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 1, 2, 1, 0, 1, 2] (orbitP14RepresentativeCoeff 787)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_787))

theorem orbitP14_path_endpoint_788 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 0, 1, 2]
      (orbitP14RepresentativeCoeff 788) = orbitP14TargetCoeff 788 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv788 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 788))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 788)) ≃*
      CocycleGroup (orbitP14TargetCocycle 788)
        (orbitP14TargetCocycle_consistent 788) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 0, 1, 2] (orbitP14RepresentativeCoeff 788)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_788))

theorem orbitP14_path_endpoint_789 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 1, 2, 0, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 789) = orbitP14TargetCoeff 789 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv789 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 789))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 789)) ≃*
      CocycleGroup (orbitP14TargetCocycle 789)
        (orbitP14TargetCocycle_consistent 789) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 1, 2, 0, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 789)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_789))

theorem orbitP14_path_endpoint_790 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 0, 1, 0, 2, 0]
      (orbitP14RepresentativeCoeff 790) = orbitP14TargetCoeff 790 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv790 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 790))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 790)) ≃*
      CocycleGroup (orbitP14TargetCocycle 790)
        (orbitP14TargetCocycle_consistent 790) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 0, 1, 0, 2, 0] (orbitP14RepresentativeCoeff 790)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_790))

theorem orbitP14_path_endpoint_791 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 791) = orbitP14TargetCoeff 791 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv791 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 791))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 791)) ≃*
      CocycleGroup (orbitP14TargetCocycle 791)
        (orbitP14TargetCocycle_consistent 791) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 2, 0, 1, 2] (orbitP14RepresentativeCoeff 791)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_791))

theorem orbitP14_path_endpoint_792 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 792) = orbitP14TargetCoeff 792 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv792 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 792))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 792)) ≃*
      CocycleGroup (orbitP14TargetCocycle 792)
        (orbitP14TargetCocycle_consistent 792) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2] (orbitP14RepresentativeCoeff 792)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_792))

theorem orbitP14_path_endpoint_793 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 0, 2, 0, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 793) = orbitP14TargetCoeff 793 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv793 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 793))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 793)) ≃*
      CocycleGroup (orbitP14TargetCocycle 793)
        (orbitP14TargetCocycle_consistent 793) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 0, 2, 0, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 793)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_793))

theorem orbitP14_path_endpoint_794 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 2, 1, 2, 1, 1, 0, 2]
      (orbitP14RepresentativeCoeff 794) = orbitP14TargetCoeff 794 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv794 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 794))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 794)) ≃*
      CocycleGroup (orbitP14TargetCocycle 794)
        (orbitP14TargetCocycle_consistent 794) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 2, 1, 2, 1, 1, 0, 2] (orbitP14RepresentativeCoeff 794)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_794))

theorem orbitP14_path_endpoint_795 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 0, 1, 0, 2, 0]
      (orbitP14RepresentativeCoeff 795) = orbitP14TargetCoeff 795 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv795 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 795))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 795)) ≃*
      CocycleGroup (orbitP14TargetCocycle 795)
        (orbitP14TargetCocycle_consistent 795) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 0, 1, 0, 2, 0] (orbitP14RepresentativeCoeff 795)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_795))

theorem orbitP14_path_endpoint_796 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 796) = orbitP14TargetCoeff 796 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv796 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 796))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 796)) ≃*
      CocycleGroup (orbitP14TargetCocycle 796)
        (orbitP14TargetCocycle_consistent 796) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 796)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_796))

theorem orbitP14_path_endpoint_797 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 2, 1]
      (orbitP14RepresentativeCoeff 797) = orbitP14TargetCoeff 797 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv797 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 797))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 797)) ≃*
      CocycleGroup (orbitP14TargetCocycle 797)
        (orbitP14TargetCocycle_consistent 797) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 2, 1] (orbitP14RepresentativeCoeff 797)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_797))

theorem orbitP14_path_endpoint_798 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 1, 1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 798) = orbitP14TargetCoeff 798 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv798 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 798))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 798)) ≃*
      CocycleGroup (orbitP14TargetCocycle 798)
        (orbitP14TargetCocycle_consistent 798) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 1, 1, 1, 2, 0] (orbitP14RepresentativeCoeff 798)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_798))

theorem orbitP14_path_endpoint_799 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 1, 1, 0, 2, 1, 2]
      (orbitP14RepresentativeCoeff 799) = orbitP14TargetCoeff 799 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv799 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 799))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 799)) ≃*
      CocycleGroup (orbitP14TargetCocycle 799)
        (orbitP14TargetCocycle_consistent 799) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 1, 1, 0, 2, 1, 2] (orbitP14RepresentativeCoeff 799)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_799))

end Smallgroups.UsefulTheorems.Order32Certificate
