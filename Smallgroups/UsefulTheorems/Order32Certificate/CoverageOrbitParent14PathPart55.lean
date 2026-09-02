/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart54

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 55. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_864 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 0, 1]
      (orbitP14RepresentativeCoeff 864) = orbitP14TargetCoeff 864 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv864 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 864))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 864)) ≃*
      CocycleGroup (orbitP14TargetCocycle 864)
        (orbitP14TargetCocycle_consistent 864) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 0, 1] (orbitP14RepresentativeCoeff 864)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_864))

theorem orbitP14_path_endpoint_865 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 865) = orbitP14TargetCoeff 865 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv865 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 865))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 865)) ≃*
      CocycleGroup (orbitP14TargetCocycle 865)
        (orbitP14TargetCocycle_consistent 865) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 865)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_865))

theorem orbitP14_path_endpoint_866 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 1, 1, 2, 1, 2]
      (orbitP14RepresentativeCoeff 866) = orbitP14TargetCoeff 866 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv866 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 866))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 866)) ≃*
      CocycleGroup (orbitP14TargetCocycle 866)
        (orbitP14TargetCocycle_consistent 866) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 1, 1, 2, 1, 2] (orbitP14RepresentativeCoeff 866)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_866))

theorem orbitP14_path_endpoint_867 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 0, 1, 2]
      (orbitP14RepresentativeCoeff 867) = orbitP14TargetCoeff 867 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv867 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 867))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 867)) ≃*
      CocycleGroup (orbitP14TargetCocycle 867)
        (orbitP14TargetCocycle_consistent 867) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 0, 1, 2] (orbitP14RepresentativeCoeff 867)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_867))

theorem orbitP14_path_endpoint_868 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 2, 1, 0, 1, 2]
      (orbitP14RepresentativeCoeff 868) = orbitP14TargetCoeff 868 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv868 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 868))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 868)) ≃*
      CocycleGroup (orbitP14TargetCocycle 868)
        (orbitP14TargetCocycle_consistent 868) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 2, 1, 0, 1, 2] (orbitP14RepresentativeCoeff 868)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_868))

theorem orbitP14_path_endpoint_869 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 2, 1, 2]
      (orbitP14RepresentativeCoeff 869) = orbitP14TargetCoeff 869 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv869 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 869))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 869)) ≃*
      CocycleGroup (orbitP14TargetCocycle 869)
        (orbitP14TargetCocycle_consistent 869) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 2, 1, 2] (orbitP14RepresentativeCoeff 869)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_869))

theorem orbitP14_path_endpoint_870 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 0, 1, 2, 1, 0, 1]
      (orbitP14RepresentativeCoeff 870) = orbitP14TargetCoeff 870 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv870 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 870))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 870)) ≃*
      CocycleGroup (orbitP14TargetCocycle 870)
        (orbitP14TargetCocycle_consistent 870) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 0, 1, 2, 1, 0, 1] (orbitP14RepresentativeCoeff 870)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_870))

theorem orbitP14_path_endpoint_871 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 2, 1, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 871) = orbitP14TargetCoeff 871 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv871 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 871))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 871)) ≃*
      CocycleGroup (orbitP14TargetCocycle 871)
        (orbitP14TargetCocycle_consistent 871) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 2, 1, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 871)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_871))

theorem orbitP14_path_endpoint_872 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 872) = orbitP14TargetCoeff 872 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv872 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 872))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 872)) ≃*
      CocycleGroup (orbitP14TargetCocycle 872)
        (orbitP14TargetCocycle_consistent 872) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 0, 1, 2] (orbitP14RepresentativeCoeff 872)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_872))

theorem orbitP14_path_endpoint_873 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 0, 1, 2, 1, 2]
      (orbitP14RepresentativeCoeff 873) = orbitP14TargetCoeff 873 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv873 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 873))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 873)) ≃*
      CocycleGroup (orbitP14TargetCocycle 873)
        (orbitP14TargetCocycle_consistent 873) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 0, 1, 2, 1, 2] (orbitP14RepresentativeCoeff 873)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_873))

theorem orbitP14_path_endpoint_874 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 0, 2]
      (orbitP14RepresentativeCoeff 874) = orbitP14TargetCoeff 874 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv874 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 874))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 874)) ≃*
      CocycleGroup (orbitP14TargetCocycle 874)
        (orbitP14TargetCocycle_consistent 874) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 0, 2] (orbitP14RepresentativeCoeff 874)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_874))

theorem orbitP14_path_endpoint_875 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 875) = orbitP14TargetCoeff 875 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv875 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 875))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 875)) ≃*
      CocycleGroup (orbitP14TargetCocycle 875)
        (orbitP14TargetCocycle_consistent 875) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 875)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_875))

theorem orbitP14_path_endpoint_876 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 0, 2, 0]
      (orbitP14RepresentativeCoeff 876) = orbitP14TargetCoeff 876 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv876 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 876))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 876)) ≃*
      CocycleGroup (orbitP14TargetCocycle 876)
        (orbitP14TargetCocycle_consistent 876) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 0, 2, 0] (orbitP14RepresentativeCoeff 876)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_876))

theorem orbitP14_path_endpoint_877 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 877) = orbitP14TargetCoeff 877 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv877 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 877))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 877)) ≃*
      CocycleGroup (orbitP14TargetCocycle 877)
        (orbitP14TargetCocycle_consistent 877) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 877)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_877))

theorem orbitP14_path_endpoint_878 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 0, 2, 1, 2]
      (orbitP14RepresentativeCoeff 878) = orbitP14TargetCoeff 878 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv878 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 878))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 878)) ≃*
      CocycleGroup (orbitP14TargetCocycle 878)
        (orbitP14TargetCocycle_consistent 878) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 0, 2, 1, 2] (orbitP14RepresentativeCoeff 878)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_878))

theorem orbitP14_path_endpoint_879 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 879) = orbitP14TargetCoeff 879 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv879 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 879))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 879)) ≃*
      CocycleGroup (orbitP14TargetCocycle 879)
        (orbitP14TargetCocycle_consistent 879) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 0, 1, 2] (orbitP14RepresentativeCoeff 879)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_879))

end Smallgroups.UsefulTheorems.Order32Certificate
