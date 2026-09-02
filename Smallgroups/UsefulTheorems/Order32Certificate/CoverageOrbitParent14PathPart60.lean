/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart59

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 60. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_944 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 1]
      (orbitP14RepresentativeCoeff 944) = orbitP14TargetCoeff 944 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv944 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 944))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 944)) ≃*
      CocycleGroup (orbitP14TargetCocycle 944)
        (orbitP14TargetCocycle_consistent 944) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 1] (orbitP14RepresentativeCoeff 944)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_944))

theorem orbitP14_path_endpoint_945 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 1, 2, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 945) = orbitP14TargetCoeff 945 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv945 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 945))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 945)) ≃*
      CocycleGroup (orbitP14TargetCocycle 945)
        (orbitP14TargetCocycle_consistent 945) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 1, 2, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 945)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_945))

theorem orbitP14_path_endpoint_946 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 1, 2, 0, 1, 1]
      (orbitP14RepresentativeCoeff 946) = orbitP14TargetCoeff 946 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv946 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 946))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 946)) ≃*
      CocycleGroup (orbitP14TargetCocycle 946)
        (orbitP14TargetCocycle_consistent 946) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 1, 2, 0, 1, 1] (orbitP14RepresentativeCoeff 946)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_946))

theorem orbitP14_path_endpoint_947 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 1, 2, 1, 1, 2]
      (orbitP14RepresentativeCoeff 947) = orbitP14TargetCoeff 947 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv947 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 947))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 947)) ≃*
      CocycleGroup (orbitP14TargetCocycle 947)
        (orbitP14TargetCocycle_consistent 947) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 1, 2, 1, 1, 2] (orbitP14RepresentativeCoeff 947)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_947))

theorem orbitP14_path_endpoint_948 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 2, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 948) = orbitP14TargetCoeff 948 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv948 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 948))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 948)) ≃*
      CocycleGroup (orbitP14TargetCocycle 948)
        (orbitP14TargetCocycle_consistent 948) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 2, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 948)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_948))

theorem orbitP14_path_endpoint_949 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 949) = orbitP14TargetCoeff 949 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv949 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 949))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 949)) ≃*
      CocycleGroup (orbitP14TargetCocycle 949)
        (orbitP14TargetCocycle_consistent 949) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 949)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_949))

theorem orbitP14_path_endpoint_950 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 950) = orbitP14TargetCoeff 950 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv950 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 950))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 950)) ≃*
      CocycleGroup (orbitP14TargetCocycle 950)
        (orbitP14TargetCocycle_consistent 950) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 2, 0] (orbitP14RepresentativeCoeff 950)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_950))

theorem orbitP14_path_endpoint_951 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 1, 2, 1, 2, 0]
      (orbitP14RepresentativeCoeff 951) = orbitP14TargetCoeff 951 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv951 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 951))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 951)) ≃*
      CocycleGroup (orbitP14TargetCocycle 951)
        (orbitP14TargetCocycle_consistent 951) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 1, 2, 1, 2, 0] (orbitP14RepresentativeCoeff 951)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_951))

theorem orbitP14_path_endpoint_952 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 952) = orbitP14TargetCoeff 952 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv952 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 952))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 952)) ≃*
      CocycleGroup (orbitP14TargetCocycle 952)
        (orbitP14TargetCocycle_consistent 952) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 952)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_952))

theorem orbitP14_path_endpoint_953 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 1, 2, 0]
      (orbitP14RepresentativeCoeff 953) = orbitP14TargetCoeff 953 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv953 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 953))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 953)) ≃*
      CocycleGroup (orbitP14TargetCocycle 953)
        (orbitP14TargetCocycle_consistent 953) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 1, 2, 0] (orbitP14RepresentativeCoeff 953)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_953))

theorem orbitP14_path_endpoint_954 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 1, 2, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 954) = orbitP14TargetCoeff 954 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv954 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 954))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 954)) ≃*
      CocycleGroup (orbitP14TargetCocycle 954)
        (orbitP14TargetCocycle_consistent 954) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 1, 2, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 954)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_954))

theorem orbitP14_path_endpoint_955 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 955) = orbitP14TargetCoeff 955 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv955 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 955))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 955)) ≃*
      CocycleGroup (orbitP14TargetCocycle 955)
        (orbitP14TargetCocycle_consistent 955) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 1] (orbitP14RepresentativeCoeff 955)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_955))

theorem orbitP14_path_endpoint_956 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 1, 2, 1, 2, 1]
      (orbitP14RepresentativeCoeff 956) = orbitP14TargetCoeff 956 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv956 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 956))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 956)) ≃*
      CocycleGroup (orbitP14TargetCocycle 956)
        (orbitP14TargetCocycle_consistent 956) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 1, 2, 1, 2, 1] (orbitP14RepresentativeCoeff 956)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_956))

theorem orbitP14_path_endpoint_957 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 957) = orbitP14TargetCoeff 957 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv957 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 957))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 957)) ≃*
      CocycleGroup (orbitP14TargetCocycle 957)
        (orbitP14TargetCocycle_consistent 957) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 1, 2, 0] (orbitP14RepresentativeCoeff 957)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_957))

theorem orbitP14_path_endpoint_958 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 1, 2, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 958) = orbitP14TargetCoeff 958 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv958 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 958))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 958)) ≃*
      CocycleGroup (orbitP14TargetCocycle 958)
        (orbitP14TargetCocycle_consistent 958) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 1, 2, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 958)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_958))

theorem orbitP14_path_endpoint_959 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 959) = orbitP14TargetCoeff 959 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv959 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 959))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 959)) ≃*
      CocycleGroup (orbitP14TargetCocycle 959)
        (orbitP14TargetCocycle_consistent 959) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 959)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_959))

end Smallgroups.UsefulTheorems.Order32Certificate
