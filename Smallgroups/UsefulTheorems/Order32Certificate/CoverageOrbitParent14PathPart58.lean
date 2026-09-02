/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart57

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 58. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_912 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 2, 1, 1, 0]
      (orbitP14RepresentativeCoeff 912) = orbitP14TargetCoeff 912 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv912 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 912))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 912)) ≃*
      CocycleGroup (orbitP14TargetCocycle 912)
        (orbitP14TargetCocycle_consistent 912) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 2, 1, 1, 0] (orbitP14RepresentativeCoeff 912)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_912))

theorem orbitP14_path_endpoint_913 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 1, 2, 1, 2, 0]
      (orbitP14RepresentativeCoeff 913) = orbitP14TargetCoeff 913 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv913 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 913))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 913)) ≃*
      CocycleGroup (orbitP14TargetCocycle 913)
        (orbitP14TargetCocycle_consistent 913) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 1, 2, 1, 2, 0] (orbitP14RepresentativeCoeff 913)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_913))

theorem orbitP14_path_endpoint_914 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 1, 2, 0, 1, 0]
      (orbitP14RepresentativeCoeff 914) = orbitP14TargetCoeff 914 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv914 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 914))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 914)) ≃*
      CocycleGroup (orbitP14TargetCocycle 914)
        (orbitP14TargetCocycle_consistent 914) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 1, 2, 0, 1, 0] (orbitP14RepresentativeCoeff 914)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_914))

theorem orbitP14_path_endpoint_915 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 0, 1, 2, 1, 2, 1]
      (orbitP14RepresentativeCoeff 915) = orbitP14TargetCoeff 915 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv915 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 915))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 915)) ≃*
      CocycleGroup (orbitP14TargetCocycle 915)
        (orbitP14TargetCocycle_consistent 915) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 0, 1, 2, 1, 2, 1] (orbitP14RepresentativeCoeff 915)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_915))

theorem orbitP14_path_endpoint_916 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 1, 2]
      (orbitP14RepresentativeCoeff 916) = orbitP14TargetCoeff 916 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv916 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 916))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 916)) ≃*
      CocycleGroup (orbitP14TargetCocycle 916)
        (orbitP14TargetCocycle_consistent 916) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 1, 2] (orbitP14RepresentativeCoeff 916)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_916))

theorem orbitP14_path_endpoint_917 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 2, 0, 1, 2, 1, 1, 2]
      (orbitP14RepresentativeCoeff 917) = orbitP14TargetCoeff 917 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv917 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 917))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 917)) ≃*
      CocycleGroup (orbitP14TargetCocycle 917)
        (orbitP14TargetCocycle_consistent 917) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 2, 0, 1, 2, 1, 1, 2] (orbitP14RepresentativeCoeff 917)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_917))

theorem orbitP14_path_endpoint_918 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 918) = orbitP14TargetCoeff 918 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv918 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 918))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 918)) ≃*
      CocycleGroup (orbitP14TargetCocycle 918)
        (orbitP14TargetCocycle_consistent 918) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 918)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_918))

theorem orbitP14_path_endpoint_919 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 1, 2, 0, 1, 0]
      (orbitP14RepresentativeCoeff 919) = orbitP14TargetCoeff 919 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv919 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 919))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 919)) ≃*
      CocycleGroup (orbitP14TargetCocycle 919)
        (orbitP14TargetCocycle_consistent 919) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 1, 2, 0, 1, 0] (orbitP14RepresentativeCoeff 919)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_919))

theorem orbitP14_path_endpoint_920 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 2, 0, 1, 2, 1, 2]
      (orbitP14RepresentativeCoeff 920) = orbitP14TargetCoeff 920 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv920 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 920))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 920)) ≃*
      CocycleGroup (orbitP14TargetCocycle 920)
        (orbitP14TargetCocycle_consistent 920) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 2, 0, 1, 2, 1, 2] (orbitP14RepresentativeCoeff 920)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_920))

theorem orbitP14_path_endpoint_921 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 2]
      (orbitP14RepresentativeCoeff 921) = orbitP14TargetCoeff 921 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv921 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 921))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 921)) ≃*
      CocycleGroup (orbitP14TargetCocycle 921)
        (orbitP14TargetCocycle_consistent 921) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 2] (orbitP14RepresentativeCoeff 921)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_921))

theorem orbitP14_path_endpoint_922 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 1, 2, 1, 2, 1, 1, 0]
      (orbitP14RepresentativeCoeff 922) = orbitP14TargetCoeff 922 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv922 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 922))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 922)) ≃*
      CocycleGroup (orbitP14TargetCocycle 922)
        (orbitP14TargetCocycle_consistent 922) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 1, 2, 1, 2, 1, 1, 0] (orbitP14RepresentativeCoeff 922)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_922))

theorem orbitP14_path_endpoint_923 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 1, 1, 0, 2, 1]
      (orbitP14RepresentativeCoeff 923) = orbitP14TargetCoeff 923 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv923 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 923))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 923)) ≃*
      CocycleGroup (orbitP14TargetCocycle 923)
        (orbitP14TargetCocycle_consistent 923) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 1, 1, 0, 2, 1] (orbitP14RepresentativeCoeff 923)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_923))

theorem orbitP14_path_endpoint_924 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 924) = orbitP14TargetCoeff 924 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv924 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 924))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 924)) ≃*
      CocycleGroup (orbitP14TargetCocycle 924)
        (orbitP14TargetCocycle_consistent 924) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 924)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_924))

theorem orbitP14_path_endpoint_925 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 2, 1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 925) = orbitP14TargetCoeff 925 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv925 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 925))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 925)) ≃*
      CocycleGroup (orbitP14TargetCocycle 925)
        (orbitP14TargetCocycle_consistent 925) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 2, 1, 1, 2, 0] (orbitP14RepresentativeCoeff 925)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_925))

theorem orbitP14_path_endpoint_926 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 0, 1, 2, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 926) = orbitP14TargetCoeff 926 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv926 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 926))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 926)) ≃*
      CocycleGroup (orbitP14TargetCocycle 926)
        (orbitP14TargetCocycle_consistent 926) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 0, 1, 2, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 926)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_926))

theorem orbitP14_path_endpoint_927 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 1, 2, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 927) = orbitP14TargetCoeff 927 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv927 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 927))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 927)) ≃*
      CocycleGroup (orbitP14TargetCocycle 927)
        (orbitP14TargetCocycle_consistent 927) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 1, 2, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 927)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_927))

end Smallgroups.UsefulTheorems.Order32Certificate
