/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart60

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 61. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_960 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 2, 1, 1, 0]
      (orbitP14RepresentativeCoeff 960) = orbitP14TargetCoeff 960 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv960 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 960))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 960)) ≃*
      CocycleGroup (orbitP14TargetCocycle 960)
        (orbitP14TargetCocycle_consistent 960) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 2, 1, 1, 0] (orbitP14RepresentativeCoeff 960)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_960))

theorem orbitP14_path_endpoint_961 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 1, 2, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 961) = orbitP14TargetCoeff 961 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv961 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 961))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 961)) ≃*
      CocycleGroup (orbitP14TargetCocycle 961)
        (orbitP14TargetCocycle_consistent 961) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 1, 2, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 961)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_961))

theorem orbitP14_path_endpoint_962 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 962) = orbitP14TargetCoeff 962 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv962 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 962))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 962)) ≃*
      CocycleGroup (orbitP14TargetCocycle 962)
        (orbitP14TargetCocycle_consistent 962) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 962)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_962))

theorem orbitP14_path_endpoint_963 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 1, 2]
      (orbitP14RepresentativeCoeff 963) = orbitP14TargetCoeff 963 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv963 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 963))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 963)) ≃*
      CocycleGroup (orbitP14TargetCocycle 963)
        (orbitP14TargetCocycle_consistent 963) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 1, 2] (orbitP14RepresentativeCoeff 963)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_963))

theorem orbitP14_path_endpoint_964 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 1, 2]
      (orbitP14RepresentativeCoeff 964) = orbitP14TargetCoeff 964 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv964 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 964))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 964)) ≃*
      CocycleGroup (orbitP14TargetCocycle 964)
        (orbitP14TargetCocycle_consistent 964) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 1, 2] (orbitP14RepresentativeCoeff 964)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_964))

theorem orbitP14_path_endpoint_965 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 1, 2, 0, 1, 0]
      (orbitP14RepresentativeCoeff 965) = orbitP14TargetCoeff 965 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv965 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 965))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 965)) ≃*
      CocycleGroup (orbitP14TargetCocycle 965)
        (orbitP14TargetCocycle_consistent 965) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 1, 2, 0, 1, 0] (orbitP14RepresentativeCoeff 965)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_965))

theorem orbitP14_path_endpoint_966 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 0, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 966) = orbitP14TargetCoeff 966 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv966 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 966))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 966)) ≃*
      CocycleGroup (orbitP14TargetCocycle 966)
        (orbitP14TargetCocycle_consistent 966) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 0, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 966)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_966))

theorem orbitP14_path_endpoint_967 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 0, 1, 2, 1, 1, 2]
      (orbitP14RepresentativeCoeff 967) = orbitP14TargetCoeff 967 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv967 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 967))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 967)) ≃*
      CocycleGroup (orbitP14TargetCocycle 967)
        (orbitP14TargetCocycle_consistent 967) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 0, 1, 2, 1, 1, 2] (orbitP14RepresentativeCoeff 967)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_967))

theorem orbitP14_path_endpoint_968 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 1, 2, 1, 1, 2]
      (orbitP14RepresentativeCoeff 968) = orbitP14TargetCoeff 968 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv968 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 968))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 968)) ≃*
      CocycleGroup (orbitP14TargetCocycle 968)
        (orbitP14TargetCocycle_consistent 968) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 1, 2, 1, 1, 2] (orbitP14RepresentativeCoeff 968)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_968))

theorem orbitP14_path_endpoint_969 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 1, 2]
      (orbitP14RepresentativeCoeff 969) = orbitP14TargetCoeff 969 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv969 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 969))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 969)) ≃*
      CocycleGroup (orbitP14TargetCocycle 969)
        (orbitP14TargetCocycle_consistent 969) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 1, 2] (orbitP14RepresentativeCoeff 969)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_969))

theorem orbitP14_path_endpoint_970 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 1, 2, 0, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 970) = orbitP14TargetCoeff 970 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv970 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 970))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 970)) ≃*
      CocycleGroup (orbitP14TargetCocycle 970)
        (orbitP14TargetCocycle_consistent 970) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 1, 2, 0, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 970)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_970))

theorem orbitP14_path_endpoint_971 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 0]
      (orbitP14RepresentativeCoeff 971) = orbitP14TargetCoeff 971 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv971 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 971))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 971)) ≃*
      CocycleGroup (orbitP14TargetCocycle 971)
        (orbitP14TargetCocycle_consistent 971) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 0] (orbitP14RepresentativeCoeff 971)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_971))

theorem orbitP14_path_endpoint_972 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 1, 2, 0, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 972) = orbitP14TargetCoeff 972 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv972 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 972))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 972)) ≃*
      CocycleGroup (orbitP14TargetCocycle 972)
        (orbitP14TargetCocycle_consistent 972) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 1, 2, 0, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 972)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_972))

theorem orbitP14_path_endpoint_973 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 973) = orbitP14TargetCoeff 973 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv973 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 973))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 973)) ≃*
      CocycleGroup (orbitP14TargetCocycle 973)
        (orbitP14TargetCocycle_consistent 973) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 973)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_973))

theorem orbitP14_path_endpoint_974 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 0, 1, 1, 2]
      (orbitP14RepresentativeCoeff 974) = orbitP14TargetCoeff 974 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv974 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 974))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 974)) ≃*
      CocycleGroup (orbitP14TargetCocycle 974)
        (orbitP14TargetCocycle_consistent 974) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 0, 1, 1, 2] (orbitP14RepresentativeCoeff 974)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_974))

theorem orbitP14_path_endpoint_975 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 2, 1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 975) = orbitP14TargetCoeff 975 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv975 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 975))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 975)) ≃*
      CocycleGroup (orbitP14TargetCocycle 975)
        (orbitP14TargetCocycle_consistent 975) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 2, 1, 1, 2, 0] (orbitP14RepresentativeCoeff 975)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_975))

end Smallgroups.UsefulTheorems.Order32Certificate
