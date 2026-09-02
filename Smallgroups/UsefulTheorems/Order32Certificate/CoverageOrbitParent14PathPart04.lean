/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart03

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 4. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_48 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1]
      (orbitP14RepresentativeCoeff 48) = orbitP14TargetCoeff 48 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv48 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 48))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 48)) ≃*
      CocycleGroup (orbitP14TargetCocycle 48)
        (orbitP14TargetCocycle_consistent 48) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1] (orbitP14RepresentativeCoeff 48)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_48))

theorem orbitP14_path_endpoint_49 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 0, 2, 0]
      (orbitP14RepresentativeCoeff 49) = orbitP14TargetCoeff 49 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv49 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 49))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 49)) ≃*
      CocycleGroup (orbitP14TargetCocycle 49)
        (orbitP14TargetCocycle_consistent 49) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 0, 2, 0] (orbitP14RepresentativeCoeff 49)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_49))

theorem orbitP14_path_endpoint_50 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 1]
      (orbitP14RepresentativeCoeff 50) = orbitP14TargetCoeff 50 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv50 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 50))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 50)) ≃*
      CocycleGroup (orbitP14TargetCocycle 50)
        (orbitP14TargetCocycle_consistent 50) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 1] (orbitP14RepresentativeCoeff 50)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_50))

theorem orbitP14_path_endpoint_51 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 0, 2, 1, 1]
      (orbitP14RepresentativeCoeff 51) = orbitP14TargetCoeff 51 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv51 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 51))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 51)) ≃*
      CocycleGroup (orbitP14TargetCocycle 51)
        (orbitP14TargetCocycle_consistent 51) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 0, 2, 1, 1] (orbitP14RepresentativeCoeff 51)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_51))

theorem orbitP14_path_endpoint_52 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 0, 2, 0]
      (orbitP14RepresentativeCoeff 52) = orbitP14TargetCoeff 52 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv52 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 52))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 52)) ≃*
      CocycleGroup (orbitP14TargetCocycle 52)
        (orbitP14TargetCocycle_consistent 52) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 0, 2, 0] (orbitP14RepresentativeCoeff 52)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_52))

theorem orbitP14_path_endpoint_53 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 0]
      (orbitP14RepresentativeCoeff 53) = orbitP14TargetCoeff 53 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv53 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 53))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 53)) ≃*
      CocycleGroup (orbitP14TargetCocycle 53)
        (orbitP14TargetCocycle_consistent 53) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 0] (orbitP14RepresentativeCoeff 53)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_53))

theorem orbitP14_path_endpoint_54 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1]
      (orbitP14RepresentativeCoeff 54) = orbitP14TargetCoeff 54 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv54 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 54))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 54)) ≃*
      CocycleGroup (orbitP14TargetCocycle 54)
        (orbitP14TargetCocycle_consistent 54) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1] (orbitP14RepresentativeCoeff 54)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_54))

theorem orbitP14_path_endpoint_55 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 1, 1]
      (orbitP14RepresentativeCoeff 55) = orbitP14TargetCoeff 55 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv55 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 55))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 55)) ≃*
      CocycleGroup (orbitP14TargetCocycle 55)
        (orbitP14TargetCocycle_consistent 55) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 1, 1] (orbitP14RepresentativeCoeff 55)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_55))

theorem orbitP14_path_endpoint_56 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 0, 1, 1, 1]
      (orbitP14RepresentativeCoeff 56) = orbitP14TargetCoeff 56 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv56 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 56))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 56)) ≃*
      CocycleGroup (orbitP14TargetCocycle 56)
        (orbitP14TargetCocycle_consistent 56) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 0, 1, 1, 1] (orbitP14RepresentativeCoeff 56)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_56))

theorem orbitP14_path_endpoint_57 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 57) = orbitP14TargetCoeff 57 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv57 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 57))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 57)) ≃*
      CocycleGroup (orbitP14TargetCocycle 57)
        (orbitP14TargetCocycle_consistent 57) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 57)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_57))

theorem orbitP14_path_endpoint_58 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 58) = orbitP14TargetCoeff 58 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv58 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 58))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 58)) ≃*
      CocycleGroup (orbitP14TargetCocycle 58)
        (orbitP14TargetCocycle_consistent 58) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 58)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_58))

theorem orbitP14_path_endpoint_59 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 0, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 59) = orbitP14TargetCoeff 59 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv59 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 59))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 59)) ≃*
      CocycleGroup (orbitP14TargetCocycle 59)
        (orbitP14TargetCocycle_consistent 59) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 0, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 59)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_59))

theorem orbitP14_path_endpoint_60 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1]
      (orbitP14RepresentativeCoeff 60) = orbitP14TargetCoeff 60 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv60 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 60))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 60)) ≃*
      CocycleGroup (orbitP14TargetCocycle 60)
        (orbitP14TargetCocycle_consistent 60) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1] (orbitP14RepresentativeCoeff 60)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_60))

theorem orbitP14_path_endpoint_61 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 1, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 61) = orbitP14TargetCoeff 61 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv61 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 61))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 61)) ≃*
      CocycleGroup (orbitP14TargetCocycle 61)
        (orbitP14TargetCocycle_consistent 61) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 1, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 61)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_61))

theorem orbitP14_path_endpoint_62 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 1, 0, 1]
      (orbitP14RepresentativeCoeff 62) = orbitP14TargetCoeff 62 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv62 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 62))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 62)) ≃*
      CocycleGroup (orbitP14TargetCocycle 62)
        (orbitP14TargetCocycle_consistent 62) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 1, 0, 1] (orbitP14RepresentativeCoeff 62)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_62))

theorem orbitP14_path_endpoint_63 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 63) = orbitP14TargetCoeff 63 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv63 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 63))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 63)) ≃*
      CocycleGroup (orbitP14TargetCocycle 63)
        (orbitP14TargetCocycle_consistent 63) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1] (orbitP14RepresentativeCoeff 63)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_63))

end Smallgroups.UsefulTheorems.Order32Certificate
