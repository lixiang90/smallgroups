/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart56

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 57. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_896 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 896) = orbitP14TargetCoeff 896 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv896 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 896))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 896)) ≃*
      CocycleGroup (orbitP14TargetCocycle 896)
        (orbitP14TargetCocycle_consistent 896) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 1] (orbitP14RepresentativeCoeff 896)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_896))

theorem orbitP14_path_endpoint_897 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 897) = orbitP14TargetCoeff 897 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv897 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 897))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 897)) ≃*
      CocycleGroup (orbitP14TargetCocycle 897)
        (orbitP14TargetCocycle_consistent 897) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 897)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_897))

theorem orbitP14_path_endpoint_898 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 898) = orbitP14TargetCoeff 898 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv898 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 898))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 898)) ≃*
      CocycleGroup (orbitP14TargetCocycle 898)
        (orbitP14TargetCocycle_consistent 898) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 898)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_898))

theorem orbitP14_path_endpoint_899 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 899) = orbitP14TargetCoeff 899 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv899 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 899))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 899)) ≃*
      CocycleGroup (orbitP14TargetCocycle 899)
        (orbitP14TargetCocycle_consistent 899) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 899)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_899))

theorem orbitP14_path_endpoint_900 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 1, 1, 1, 2]
      (orbitP14RepresentativeCoeff 900) = orbitP14TargetCoeff 900 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv900 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 900))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 900)) ≃*
      CocycleGroup (orbitP14TargetCocycle 900)
        (orbitP14TargetCocycle_consistent 900) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 1, 1, 1, 2] (orbitP14RepresentativeCoeff 900)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_900))

theorem orbitP14_path_endpoint_901 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 2]
      (orbitP14RepresentativeCoeff 901) = orbitP14TargetCoeff 901 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv901 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 901))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 901)) ≃*
      CocycleGroup (orbitP14TargetCocycle 901)
        (orbitP14TargetCocycle_consistent 901) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 2] (orbitP14RepresentativeCoeff 901)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_901))

theorem orbitP14_path_endpoint_902 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2]
      (orbitP14RepresentativeCoeff 902) = orbitP14TargetCoeff 902 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv902 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 902))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 902)) ≃*
      CocycleGroup (orbitP14TargetCocycle 902)
        (orbitP14TargetCocycle_consistent 902) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2] (orbitP14RepresentativeCoeff 902)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_902))

theorem orbitP14_path_endpoint_903 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 903) = orbitP14TargetCoeff 903 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv903 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 903))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 903)) ≃*
      CocycleGroup (orbitP14TargetCocycle 903)
        (orbitP14TargetCocycle_consistent 903) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 903)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_903))

theorem orbitP14_path_endpoint_904 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 904) = orbitP14TargetCoeff 904 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv904 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 904))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 904)) ≃*
      CocycleGroup (orbitP14TargetCocycle 904)
        (orbitP14TargetCocycle_consistent 904) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 904)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_904))

theorem orbitP14_path_endpoint_905 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2]
      (orbitP14RepresentativeCoeff 905) = orbitP14TargetCoeff 905 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv905 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 905))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 905)) ≃*
      CocycleGroup (orbitP14TargetCocycle 905)
        (orbitP14TargetCocycle_consistent 905) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2] (orbitP14RepresentativeCoeff 905)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_905))

theorem orbitP14_path_endpoint_906 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 1, 0, 2, 1]
      (orbitP14RepresentativeCoeff 906) = orbitP14TargetCoeff 906 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv906 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 906))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 906)) ≃*
      CocycleGroup (orbitP14TargetCocycle 906)
        (orbitP14TargetCocycle_consistent 906) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 1, 0, 2, 1] (orbitP14RepresentativeCoeff 906)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_906))

theorem orbitP14_path_endpoint_907 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 0]
      (orbitP14RepresentativeCoeff 907) = orbitP14TargetCoeff 907 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv907 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 907))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 907)) ≃*
      CocycleGroup (orbitP14TargetCocycle 907)
        (orbitP14TargetCocycle_consistent 907) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 0] (orbitP14RepresentativeCoeff 907)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_907))

theorem orbitP14_path_endpoint_908 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 908) = orbitP14TargetCoeff 908 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv908 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 908))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 908)) ≃*
      CocycleGroup (orbitP14TargetCocycle 908)
        (orbitP14TargetCocycle_consistent 908) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 908)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_908))

theorem orbitP14_path_endpoint_909 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0]
      (orbitP14RepresentativeCoeff 909) = orbitP14TargetCoeff 909 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv909 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 909))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 909)) ≃*
      CocycleGroup (orbitP14TargetCocycle 909)
        (orbitP14TargetCocycle_consistent 909) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0] (orbitP14RepresentativeCoeff 909)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_909))

theorem orbitP14_path_endpoint_910 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 910) = orbitP14TargetCoeff 910 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv910 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 910))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 910)) ≃*
      CocycleGroup (orbitP14TargetCocycle 910)
        (orbitP14TargetCocycle_consistent 910) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 910)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_910))

theorem orbitP14_path_endpoint_911 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 1, 2]
      (orbitP14RepresentativeCoeff 911) = orbitP14TargetCoeff 911 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv911 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 911))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 911)) ≃*
      CocycleGroup (orbitP14TargetCocycle 911)
        (orbitP14TargetCocycle_consistent 911) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 1, 2] (orbitP14RepresentativeCoeff 911)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_911))

end Smallgroups.UsefulTheorems.Order32Certificate
