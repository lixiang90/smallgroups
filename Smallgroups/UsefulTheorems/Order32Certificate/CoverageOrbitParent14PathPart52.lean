/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart51

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 52. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_816 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 0, 1, 1]
      (orbitP14RepresentativeCoeff 816) = orbitP14TargetCoeff 816 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv816 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 816))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 816)) ≃*
      CocycleGroup (orbitP14TargetCocycle 816)
        (orbitP14TargetCocycle_consistent 816) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 0, 1, 1] (orbitP14RepresentativeCoeff 816)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_816))

theorem orbitP14_path_endpoint_817 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 1, 2, 0, 1, 2, 0, 1, 0]
      (orbitP14RepresentativeCoeff 817) = orbitP14TargetCoeff 817 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv817 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 817))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 817)) ≃*
      CocycleGroup (orbitP14TargetCocycle 817)
        (orbitP14TargetCocycle_consistent 817) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 1, 2, 0, 1, 2, 0, 1, 0] (orbitP14RepresentativeCoeff 817)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_817))

theorem orbitP14_path_endpoint_818 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 818) = orbitP14TargetCoeff 818 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv818 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 818))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 818)) ≃*
      CocycleGroup (orbitP14TargetCocycle 818)
        (orbitP14TargetCocycle_consistent 818) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 818)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_818))

theorem orbitP14_path_endpoint_819 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 0, 1, 0, 2, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 819) = orbitP14TargetCoeff 819 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv819 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 819))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 819)) ≃*
      CocycleGroup (orbitP14TargetCocycle 819)
        (orbitP14TargetCocycle_consistent 819) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 0, 1, 0, 2, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 819)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_819))

theorem orbitP14_path_endpoint_820 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 0, 2, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 820) = orbitP14TargetCoeff 820 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv820 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 820))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 820)) ≃*
      CocycleGroup (orbitP14TargetCocycle 820)
        (orbitP14TargetCocycle_consistent 820) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 0, 2, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 820)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_820))

theorem orbitP14_path_endpoint_821 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 0, 2, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 821) = orbitP14TargetCoeff 821 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv821 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 821))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 821)) ≃*
      CocycleGroup (orbitP14TargetCocycle 821)
        (orbitP14TargetCocycle_consistent 821) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 0, 2, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 821)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_821))

theorem orbitP14_path_endpoint_822 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 822) = orbitP14TargetCoeff 822 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv822 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 822))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 822)) ≃*
      CocycleGroup (orbitP14TargetCocycle 822)
        (orbitP14TargetCocycle_consistent 822) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 822)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_822))

theorem orbitP14_path_endpoint_823 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 2, 1, 2]
      (orbitP14RepresentativeCoeff 823) = orbitP14TargetCoeff 823 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv823 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 823))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 823)) ≃*
      CocycleGroup (orbitP14TargetCocycle 823)
        (orbitP14TargetCocycle_consistent 823) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 2, 1, 2] (orbitP14RepresentativeCoeff 823)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_823))

theorem orbitP14_path_endpoint_824 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 2, 0, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 824) = orbitP14TargetCoeff 824 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv824 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 824))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 824)) ≃*
      CocycleGroup (orbitP14TargetCocycle 824)
        (orbitP14TargetCocycle_consistent 824) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 2, 0, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 824)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_824))

theorem orbitP14_path_endpoint_825 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 1, 2, 1, 2]
      (orbitP14RepresentativeCoeff 825) = orbitP14TargetCoeff 825 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv825 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 825))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 825)) ≃*
      CocycleGroup (orbitP14TargetCocycle 825)
        (orbitP14TargetCocycle_consistent 825) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 1, 2, 1, 2] (orbitP14RepresentativeCoeff 825)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_825))

theorem orbitP14_path_endpoint_826 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 826) = orbitP14TargetCoeff 826 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv826 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 826))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 826)) ≃*
      CocycleGroup (orbitP14TargetCocycle 826)
        (orbitP14TargetCocycle_consistent 826) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 826)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_826))

theorem orbitP14_path_endpoint_827 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 827) = orbitP14TargetCoeff 827 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv827 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 827))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 827)) ≃*
      CocycleGroup (orbitP14TargetCocycle 827)
        (orbitP14TargetCocycle_consistent 827) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 0] (orbitP14RepresentativeCoeff 827)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_827))

theorem orbitP14_path_endpoint_828 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 828) = orbitP14TargetCoeff 828 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv828 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 828))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 828)) ≃*
      CocycleGroup (orbitP14TargetCocycle 828)
        (orbitP14TargetCocycle_consistent 828) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 828)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_828))

theorem orbitP14_path_endpoint_829 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 0, 1, 2, 1, 2]
      (orbitP14RepresentativeCoeff 829) = orbitP14TargetCoeff 829 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv829 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 829))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 829)) ≃*
      CocycleGroup (orbitP14TargetCocycle 829)
        (orbitP14TargetCocycle_consistent 829) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 0, 1, 2, 1, 2] (orbitP14RepresentativeCoeff 829)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_829))

theorem orbitP14_path_endpoint_830 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 0, 2, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 830) = orbitP14TargetCoeff 830 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv830 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 830))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 830)) ≃*
      CocycleGroup (orbitP14TargetCocycle 830)
        (orbitP14TargetCocycle_consistent 830) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 0, 2, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 830)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_830))

theorem orbitP14_path_endpoint_831 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 1, 2, 1, 1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 831) = orbitP14TargetCoeff 831 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv831 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 831))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 831)) ≃*
      CocycleGroup (orbitP14TargetCocycle 831)
        (orbitP14TargetCocycle_consistent 831) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 1, 2, 1, 1, 1, 2, 0] (orbitP14RepresentativeCoeff 831)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_831))

end Smallgroups.UsefulTheorems.Order32Certificate
