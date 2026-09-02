/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13PathPart01

set_option maxRecDepth 100000

/-! Checked short orbit paths for parent 13; generated part 2. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP13_path_endpoint_16 :
    Order16Table.applyOrbitPath orbitP13ActionColumns [1]
      (orbitP13RepresentativeCoeff 16) = orbitP13TargetCoeff 16 := by
  decide +kernel

noncomputable def orbitP13NormalizeEquiv16 :
    CocycleGroup (orbitP13SelectedCocycle (orbitP13Index 16))
        (orbitP13SelectedCocycle_consistent (orbitP13Index 16)) ≃*
      CocycleGroup (orbitP13TargetCocycle 16)
        (orbitP13TargetCocycle_consistent 16) := by
  let e := Order16Table.orbitPathEquiv parent13Table coverageP13HBasis
    orbitP13ActionColumns orbitP13CorrectionColumns orbitP13_hbasis_cocycle
    orbitP13Aut orbitP13_action_linear [1] (orbitP13RepresentativeCoeff 16)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent13Table coverageP13HBasis)
      orbitP13_path_endpoint_16))

theorem orbitP13_path_endpoint_17 :
    Order16Table.applyOrbitPath orbitP13ActionColumns [0]
      (orbitP13RepresentativeCoeff 17) = orbitP13TargetCoeff 17 := by
  decide +kernel

noncomputable def orbitP13NormalizeEquiv17 :
    CocycleGroup (orbitP13SelectedCocycle (orbitP13Index 17))
        (orbitP13SelectedCocycle_consistent (orbitP13Index 17)) ≃*
      CocycleGroup (orbitP13TargetCocycle 17)
        (orbitP13TargetCocycle_consistent 17) := by
  let e := Order16Table.orbitPathEquiv parent13Table coverageP13HBasis
    orbitP13ActionColumns orbitP13CorrectionColumns orbitP13_hbasis_cocycle
    orbitP13Aut orbitP13_action_linear [0] (orbitP13RepresentativeCoeff 17)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent13Table coverageP13HBasis)
      orbitP13_path_endpoint_17))

theorem orbitP13_path_endpoint_18 :
    Order16Table.applyOrbitPath orbitP13ActionColumns [1]
      (orbitP13RepresentativeCoeff 18) = orbitP13TargetCoeff 18 := by
  decide +kernel

noncomputable def orbitP13NormalizeEquiv18 :
    CocycleGroup (orbitP13SelectedCocycle (orbitP13Index 18))
        (orbitP13SelectedCocycle_consistent (orbitP13Index 18)) ≃*
      CocycleGroup (orbitP13TargetCocycle 18)
        (orbitP13TargetCocycle_consistent 18) := by
  let e := Order16Table.orbitPathEquiv parent13Table coverageP13HBasis
    orbitP13ActionColumns orbitP13CorrectionColumns orbitP13_hbasis_cocycle
    orbitP13Aut orbitP13_action_linear [1] (orbitP13RepresentativeCoeff 18)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent13Table coverageP13HBasis)
      orbitP13_path_endpoint_18))

theorem orbitP13_path_endpoint_19 :
    Order16Table.applyOrbitPath orbitP13ActionColumns [0]
      (orbitP13RepresentativeCoeff 19) = orbitP13TargetCoeff 19 := by
  decide +kernel

noncomputable def orbitP13NormalizeEquiv19 :
    CocycleGroup (orbitP13SelectedCocycle (orbitP13Index 19))
        (orbitP13SelectedCocycle_consistent (orbitP13Index 19)) ≃*
      CocycleGroup (orbitP13TargetCocycle 19)
        (orbitP13TargetCocycle_consistent 19) := by
  let e := Order16Table.orbitPathEquiv parent13Table coverageP13HBasis
    orbitP13ActionColumns orbitP13CorrectionColumns orbitP13_hbasis_cocycle
    orbitP13Aut orbitP13_action_linear [0] (orbitP13RepresentativeCoeff 19)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent13Table coverageP13HBasis)
      orbitP13_path_endpoint_19))

theorem orbitP13_path_endpoint_20 :
    Order16Table.applyOrbitPath orbitP13ActionColumns [0]
      (orbitP13RepresentativeCoeff 20) = orbitP13TargetCoeff 20 := by
  decide +kernel

noncomputable def orbitP13NormalizeEquiv20 :
    CocycleGroup (orbitP13SelectedCocycle (orbitP13Index 20))
        (orbitP13SelectedCocycle_consistent (orbitP13Index 20)) ≃*
      CocycleGroup (orbitP13TargetCocycle 20)
        (orbitP13TargetCocycle_consistent 20) := by
  let e := Order16Table.orbitPathEquiv parent13Table coverageP13HBasis
    orbitP13ActionColumns orbitP13CorrectionColumns orbitP13_hbasis_cocycle
    orbitP13Aut orbitP13_action_linear [0] (orbitP13RepresentativeCoeff 20)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent13Table coverageP13HBasis)
      orbitP13_path_endpoint_20))

theorem orbitP13_path_endpoint_21 :
    Order16Table.applyOrbitPath orbitP13ActionColumns [1]
      (orbitP13RepresentativeCoeff 21) = orbitP13TargetCoeff 21 := by
  decide +kernel

noncomputable def orbitP13NormalizeEquiv21 :
    CocycleGroup (orbitP13SelectedCocycle (orbitP13Index 21))
        (orbitP13SelectedCocycle_consistent (orbitP13Index 21)) ≃*
      CocycleGroup (orbitP13TargetCocycle 21)
        (orbitP13TargetCocycle_consistent 21) := by
  let e := Order16Table.orbitPathEquiv parent13Table coverageP13HBasis
    orbitP13ActionColumns orbitP13CorrectionColumns orbitP13_hbasis_cocycle
    orbitP13Aut orbitP13_action_linear [1] (orbitP13RepresentativeCoeff 21)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent13Table coverageP13HBasis)
      orbitP13_path_endpoint_21))

theorem orbitP13_path_endpoint_22 :
    Order16Table.applyOrbitPath orbitP13ActionColumns [1]
      (orbitP13RepresentativeCoeff 22) = orbitP13TargetCoeff 22 := by
  decide +kernel

noncomputable def orbitP13NormalizeEquiv22 :
    CocycleGroup (orbitP13SelectedCocycle (orbitP13Index 22))
        (orbitP13SelectedCocycle_consistent (orbitP13Index 22)) ≃*
      CocycleGroup (orbitP13TargetCocycle 22)
        (orbitP13TargetCocycle_consistent 22) := by
  let e := Order16Table.orbitPathEquiv parent13Table coverageP13HBasis
    orbitP13ActionColumns orbitP13CorrectionColumns orbitP13_hbasis_cocycle
    orbitP13Aut orbitP13_action_linear [1] (orbitP13RepresentativeCoeff 22)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent13Table coverageP13HBasis)
      orbitP13_path_endpoint_22))

theorem orbitP13_path_endpoint_23 :
    Order16Table.applyOrbitPath orbitP13ActionColumns [0, 1]
      (orbitP13RepresentativeCoeff 23) = orbitP13TargetCoeff 23 := by
  decide +kernel

noncomputable def orbitP13NormalizeEquiv23 :
    CocycleGroup (orbitP13SelectedCocycle (orbitP13Index 23))
        (orbitP13SelectedCocycle_consistent (orbitP13Index 23)) ≃*
      CocycleGroup (orbitP13TargetCocycle 23)
        (orbitP13TargetCocycle_consistent 23) := by
  let e := Order16Table.orbitPathEquiv parent13Table coverageP13HBasis
    orbitP13ActionColumns orbitP13CorrectionColumns orbitP13_hbasis_cocycle
    orbitP13Aut orbitP13_action_linear [0, 1] (orbitP13RepresentativeCoeff 23)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent13Table coverageP13HBasis)
      orbitP13_path_endpoint_23))

theorem orbitP13_path_endpoint_24 :
    Order16Table.applyOrbitPath orbitP13ActionColumns []
      (orbitP13RepresentativeCoeff 24) = orbitP13TargetCoeff 24 := by
  decide +kernel

noncomputable def orbitP13NormalizeEquiv24 :
    CocycleGroup (orbitP13SelectedCocycle (orbitP13Index 24))
        (orbitP13SelectedCocycle_consistent (orbitP13Index 24)) ≃*
      CocycleGroup (orbitP13TargetCocycle 24)
        (orbitP13TargetCocycle_consistent 24) := by
  let e := Order16Table.orbitPathEquiv parent13Table coverageP13HBasis
    orbitP13ActionColumns orbitP13CorrectionColumns orbitP13_hbasis_cocycle
    orbitP13Aut orbitP13_action_linear [] (orbitP13RepresentativeCoeff 24)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent13Table coverageP13HBasis)
      orbitP13_path_endpoint_24))

theorem orbitP13_path_endpoint_25 :
    Order16Table.applyOrbitPath orbitP13ActionColumns [0, 1]
      (orbitP13RepresentativeCoeff 25) = orbitP13TargetCoeff 25 := by
  decide +kernel

noncomputable def orbitP13NormalizeEquiv25 :
    CocycleGroup (orbitP13SelectedCocycle (orbitP13Index 25))
        (orbitP13SelectedCocycle_consistent (orbitP13Index 25)) ≃*
      CocycleGroup (orbitP13TargetCocycle 25)
        (orbitP13TargetCocycle_consistent 25) := by
  let e := Order16Table.orbitPathEquiv parent13Table coverageP13HBasis
    orbitP13ActionColumns orbitP13CorrectionColumns orbitP13_hbasis_cocycle
    orbitP13Aut orbitP13_action_linear [0, 1] (orbitP13RepresentativeCoeff 25)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent13Table coverageP13HBasis)
      orbitP13_path_endpoint_25))

theorem orbitP13_path_endpoint_26 :
    Order16Table.applyOrbitPath orbitP13ActionColumns []
      (orbitP13RepresentativeCoeff 26) = orbitP13TargetCoeff 26 := by
  decide +kernel

noncomputable def orbitP13NormalizeEquiv26 :
    CocycleGroup (orbitP13SelectedCocycle (orbitP13Index 26))
        (orbitP13SelectedCocycle_consistent (orbitP13Index 26)) ≃*
      CocycleGroup (orbitP13TargetCocycle 26)
        (orbitP13TargetCocycle_consistent 26) := by
  let e := Order16Table.orbitPathEquiv parent13Table coverageP13HBasis
    orbitP13ActionColumns orbitP13CorrectionColumns orbitP13_hbasis_cocycle
    orbitP13Aut orbitP13_action_linear [] (orbitP13RepresentativeCoeff 26)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent13Table coverageP13HBasis)
      orbitP13_path_endpoint_26))

theorem orbitP13_path_endpoint_27 :
    Order16Table.applyOrbitPath orbitP13ActionColumns [1, 1]
      (orbitP13RepresentativeCoeff 27) = orbitP13TargetCoeff 27 := by
  decide +kernel

noncomputable def orbitP13NormalizeEquiv27 :
    CocycleGroup (orbitP13SelectedCocycle (orbitP13Index 27))
        (orbitP13SelectedCocycle_consistent (orbitP13Index 27)) ≃*
      CocycleGroup (orbitP13TargetCocycle 27)
        (orbitP13TargetCocycle_consistent 27) := by
  let e := Order16Table.orbitPathEquiv parent13Table coverageP13HBasis
    orbitP13ActionColumns orbitP13CorrectionColumns orbitP13_hbasis_cocycle
    orbitP13Aut orbitP13_action_linear [1, 1] (orbitP13RepresentativeCoeff 27)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent13Table coverageP13HBasis)
      orbitP13_path_endpoint_27))

theorem orbitP13_path_endpoint_28 :
    Order16Table.applyOrbitPath orbitP13ActionColumns [0, 1]
      (orbitP13RepresentativeCoeff 28) = orbitP13TargetCoeff 28 := by
  decide +kernel

noncomputable def orbitP13NormalizeEquiv28 :
    CocycleGroup (orbitP13SelectedCocycle (orbitP13Index 28))
        (orbitP13SelectedCocycle_consistent (orbitP13Index 28)) ≃*
      CocycleGroup (orbitP13TargetCocycle 28)
        (orbitP13TargetCocycle_consistent 28) := by
  let e := Order16Table.orbitPathEquiv parent13Table coverageP13HBasis
    orbitP13ActionColumns orbitP13CorrectionColumns orbitP13_hbasis_cocycle
    orbitP13Aut orbitP13_action_linear [0, 1] (orbitP13RepresentativeCoeff 28)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent13Table coverageP13HBasis)
      orbitP13_path_endpoint_28))

theorem orbitP13_path_endpoint_29 :
    Order16Table.applyOrbitPath orbitP13ActionColumns [0, 1]
      (orbitP13RepresentativeCoeff 29) = orbitP13TargetCoeff 29 := by
  decide +kernel

noncomputable def orbitP13NormalizeEquiv29 :
    CocycleGroup (orbitP13SelectedCocycle (orbitP13Index 29))
        (orbitP13SelectedCocycle_consistent (orbitP13Index 29)) ≃*
      CocycleGroup (orbitP13TargetCocycle 29)
        (orbitP13TargetCocycle_consistent 29) := by
  let e := Order16Table.orbitPathEquiv parent13Table coverageP13HBasis
    orbitP13ActionColumns orbitP13CorrectionColumns orbitP13_hbasis_cocycle
    orbitP13Aut orbitP13_action_linear [0, 1] (orbitP13RepresentativeCoeff 29)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent13Table coverageP13HBasis)
      orbitP13_path_endpoint_29))

theorem orbitP13_path_endpoint_30 :
    Order16Table.applyOrbitPath orbitP13ActionColumns [0, 1]
      (orbitP13RepresentativeCoeff 30) = orbitP13TargetCoeff 30 := by
  decide +kernel

noncomputable def orbitP13NormalizeEquiv30 :
    CocycleGroup (orbitP13SelectedCocycle (orbitP13Index 30))
        (orbitP13SelectedCocycle_consistent (orbitP13Index 30)) ≃*
      CocycleGroup (orbitP13TargetCocycle 30)
        (orbitP13TargetCocycle_consistent 30) := by
  let e := Order16Table.orbitPathEquiv parent13Table coverageP13HBasis
    orbitP13ActionColumns orbitP13CorrectionColumns orbitP13_hbasis_cocycle
    orbitP13Aut orbitP13_action_linear [0, 1] (orbitP13RepresentativeCoeff 30)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent13Table coverageP13HBasis)
      orbitP13_path_endpoint_30))

theorem orbitP13_path_endpoint_31 :
    Order16Table.applyOrbitPath orbitP13ActionColumns [0]
      (orbitP13RepresentativeCoeff 31) = orbitP13TargetCoeff 31 := by
  decide +kernel

noncomputable def orbitP13NormalizeEquiv31 :
    CocycleGroup (orbitP13SelectedCocycle (orbitP13Index 31))
        (orbitP13SelectedCocycle_consistent (orbitP13Index 31)) ≃*
      CocycleGroup (orbitP13TargetCocycle 31)
        (orbitP13TargetCocycle_consistent 31) := by
  let e := Order16Table.orbitPathEquiv parent13Table coverageP13HBasis
    orbitP13ActionColumns orbitP13CorrectionColumns orbitP13_hbasis_cocycle
    orbitP13Aut orbitP13_action_linear [0] (orbitP13RepresentativeCoeff 31)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent13Table coverageP13HBasis)
      orbitP13_path_endpoint_31))

end Smallgroups.UsefulTheorems.Order32Certificate
