/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart01

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 2. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_16 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1]
      (orbitP14RepresentativeCoeff 16) = orbitP14TargetCoeff 16 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv16 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 16))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 16)) ≃*
      CocycleGroup (orbitP14TargetCocycle 16)
        (orbitP14TargetCocycle_consistent 16) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1] (orbitP14RepresentativeCoeff 16)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_16))

theorem orbitP14_path_endpoint_17 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1]
      (orbitP14RepresentativeCoeff 17) = orbitP14TargetCoeff 17 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv17 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 17))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 17)) ≃*
      CocycleGroup (orbitP14TargetCocycle 17)
        (orbitP14TargetCocycle_consistent 17) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1] (orbitP14RepresentativeCoeff 17)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_17))

theorem orbitP14_path_endpoint_18 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 0, 1]
      (orbitP14RepresentativeCoeff 18) = orbitP14TargetCoeff 18 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv18 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 18))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 18)) ≃*
      CocycleGroup (orbitP14TargetCocycle 18)
        (orbitP14TargetCocycle_consistent 18) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 0, 1] (orbitP14RepresentativeCoeff 18)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_18))

theorem orbitP14_path_endpoint_19 :
    Order16Table.applyOrbitPath orbitP14ActionColumns []
      (orbitP14RepresentativeCoeff 19) = orbitP14TargetCoeff 19 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv19 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 19))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 19)) ≃*
      CocycleGroup (orbitP14TargetCocycle 19)
        (orbitP14TargetCocycle_consistent 19) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [] (orbitP14RepresentativeCoeff 19)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_19))

theorem orbitP14_path_endpoint_20 :
    Order16Table.applyOrbitPath orbitP14ActionColumns []
      (orbitP14RepresentativeCoeff 20) = orbitP14TargetCoeff 20 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv20 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 20))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 20)) ≃*
      CocycleGroup (orbitP14TargetCocycle 20)
        (orbitP14TargetCocycle_consistent 20) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [] (orbitP14RepresentativeCoeff 20)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_20))

theorem orbitP14_path_endpoint_21 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 1, 0]
      (orbitP14RepresentativeCoeff 21) = orbitP14TargetCoeff 21 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv21 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 21))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 21)) ≃*
      CocycleGroup (orbitP14TargetCocycle 21)
        (orbitP14TargetCocycle_consistent 21) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 1, 0] (orbitP14RepresentativeCoeff 21)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_21))

theorem orbitP14_path_endpoint_22 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 0, 2, 0]
      (orbitP14RepresentativeCoeff 22) = orbitP14TargetCoeff 22 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv22 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 22))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 22)) ≃*
      CocycleGroup (orbitP14TargetCocycle 22)
        (orbitP14TargetCocycle_consistent 22) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 0, 2, 0] (orbitP14RepresentativeCoeff 22)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_22))

theorem orbitP14_path_endpoint_23 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 0, 2, 0, 1, 0]
      (orbitP14RepresentativeCoeff 23) = orbitP14TargetCoeff 23 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv23 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 23))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 23)) ≃*
      CocycleGroup (orbitP14TargetCocycle 23)
        (orbitP14TargetCocycle_consistent 23) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 0, 2, 0, 1, 0] (orbitP14RepresentativeCoeff 23)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_23))

theorem orbitP14_path_endpoint_24 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 1, 2, 0]
      (orbitP14RepresentativeCoeff 24) = orbitP14TargetCoeff 24 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv24 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 24))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 24)) ≃*
      CocycleGroup (orbitP14TargetCocycle 24)
        (orbitP14TargetCocycle_consistent 24) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 1, 2, 0] (orbitP14RepresentativeCoeff 24)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_24))

theorem orbitP14_path_endpoint_25 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0]
      (orbitP14RepresentativeCoeff 25) = orbitP14TargetCoeff 25 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv25 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 25))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 25)) ≃*
      CocycleGroup (orbitP14TargetCocycle 25)
        (orbitP14TargetCocycle_consistent 25) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0] (orbitP14RepresentativeCoeff 25)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_25))

theorem orbitP14_path_endpoint_26 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 0, 1]
      (orbitP14RepresentativeCoeff 26) = orbitP14TargetCoeff 26 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv26 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 26))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 26)) ≃*
      CocycleGroup (orbitP14TargetCocycle 26)
        (orbitP14TargetCocycle_consistent 26) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 0, 1] (orbitP14RepresentativeCoeff 26)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_26))

theorem orbitP14_path_endpoint_27 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 27) = orbitP14TargetCoeff 27 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv27 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 27))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 27)) ≃*
      CocycleGroup (orbitP14TargetCocycle 27)
        (orbitP14TargetCocycle_consistent 27) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 27)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_27))

theorem orbitP14_path_endpoint_28 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 2, 1, 2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 28) = orbitP14TargetCoeff 28 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv28 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 28))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 28)) ≃*
      CocycleGroup (orbitP14TargetCocycle 28)
        (orbitP14TargetCocycle_consistent 28) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 2, 1, 2, 0, 1, 2] (orbitP14RepresentativeCoeff 28)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_28))

theorem orbitP14_path_endpoint_29 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 2, 1, 2, 1, 1, 0, 1, 2]
      (orbitP14RepresentativeCoeff 29) = orbitP14TargetCoeff 29 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv29 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 29))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 29)) ≃*
      CocycleGroup (orbitP14TargetCocycle 29)
        (orbitP14TargetCocycle_consistent 29) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 2, 1, 2, 1, 1, 0, 1, 2] (orbitP14RepresentativeCoeff 29)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_29))

theorem orbitP14_path_endpoint_30 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 0, 1, 2, 1, 2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 30) = orbitP14TargetCoeff 30 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv30 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 30))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 30)) ≃*
      CocycleGroup (orbitP14TargetCocycle 30)
        (orbitP14TargetCocycle_consistent 30) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 0, 1, 2, 1, 2, 0, 1, 2] (orbitP14RepresentativeCoeff 30)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_30))

theorem orbitP14_path_endpoint_31 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 0, 1, 2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 31) = orbitP14TargetCoeff 31 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv31 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 31))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 31)) ≃*
      CocycleGroup (orbitP14TargetCocycle 31)
        (orbitP14TargetCocycle_consistent 31) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 0, 1, 2, 0, 1, 2] (orbitP14RepresentativeCoeff 31)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_31))

end Smallgroups.UsefulTheorems.Order32Certificate
