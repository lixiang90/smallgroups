/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10Core

set_option maxRecDepth 100000

/-! Checked short orbit paths for parent 10; generated part 2. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP10_path_endpoint_16 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [6]
      (orbitP10RepresentativeCoeff 16) = orbitP10TargetCoeff 16 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv16 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 16))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 16)) ≃*
      CocycleGroup (orbitP10TargetCocycle 16)
        (orbitP10TargetCocycle_consistent 16) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [6] (orbitP10RepresentativeCoeff 16)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_16))

theorem orbitP10_path_endpoint_17 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [0, 6]
      (orbitP10RepresentativeCoeff 17) = orbitP10TargetCoeff 17 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv17 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 17))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 17)) ≃*
      CocycleGroup (orbitP10TargetCocycle 17)
        (orbitP10TargetCocycle_consistent 17) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [0, 6] (orbitP10RepresentativeCoeff 17)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_17))

theorem orbitP10_path_endpoint_18 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [2]
      (orbitP10RepresentativeCoeff 18) = orbitP10TargetCoeff 18 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv18 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 18))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 18)) ≃*
      CocycleGroup (orbitP10TargetCocycle 18)
        (orbitP10TargetCocycle_consistent 18) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [2] (orbitP10RepresentativeCoeff 18)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_18))

theorem orbitP10_path_endpoint_19 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [0, 2]
      (orbitP10RepresentativeCoeff 19) = orbitP10TargetCoeff 19 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv19 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 19))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 19)) ≃*
      CocycleGroup (orbitP10TargetCocycle 19)
        (orbitP10TargetCocycle_consistent 19) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [0, 2] (orbitP10RepresentativeCoeff 19)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_19))

theorem orbitP10_path_endpoint_20 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [6, 0]
      (orbitP10RepresentativeCoeff 20) = orbitP10TargetCoeff 20 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv20 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 20))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 20)) ≃*
      CocycleGroup (orbitP10TargetCocycle 20)
        (orbitP10TargetCocycle_consistent 20) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [6, 0] (orbitP10RepresentativeCoeff 20)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_20))

theorem orbitP10_path_endpoint_21 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [2]
      (orbitP10RepresentativeCoeff 21) = orbitP10TargetCoeff 21 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv21 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 21))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 21)) ≃*
      CocycleGroup (orbitP10TargetCocycle 21)
        (orbitP10TargetCocycle_consistent 21) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [2] (orbitP10RepresentativeCoeff 21)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_21))

theorem orbitP10_path_endpoint_22 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [0, 2, 0]
      (orbitP10RepresentativeCoeff 22) = orbitP10TargetCoeff 22 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv22 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 22))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 22)) ≃*
      CocycleGroup (orbitP10TargetCocycle 22)
        (orbitP10TargetCocycle_consistent 22) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [0, 2, 0] (orbitP10RepresentativeCoeff 22)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_22))

theorem orbitP10_path_endpoint_23 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [2, 0]
      (orbitP10RepresentativeCoeff 23) = orbitP10TargetCoeff 23 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv23 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 23))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 23)) ≃*
      CocycleGroup (orbitP10TargetCocycle 23)
        (orbitP10TargetCocycle_consistent 23) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [2, 0] (orbitP10RepresentativeCoeff 23)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_23))

theorem orbitP10_path_endpoint_24 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [0, 2, 0]
      (orbitP10RepresentativeCoeff 24) = orbitP10TargetCoeff 24 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv24 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 24))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 24)) ≃*
      CocycleGroup (orbitP10TargetCocycle 24)
        (orbitP10TargetCocycle_consistent 24) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [0, 2, 0] (orbitP10RepresentativeCoeff 24)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_24))

theorem orbitP10_path_endpoint_25 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [6]
      (orbitP10RepresentativeCoeff 25) = orbitP10TargetCoeff 25 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv25 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 25))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 25)) ≃*
      CocycleGroup (orbitP10TargetCocycle 25)
        (orbitP10TargetCocycle_consistent 25) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [6] (orbitP10RepresentativeCoeff 25)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_25))

theorem orbitP10_path_endpoint_26 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [2]
      (orbitP10RepresentativeCoeff 26) = orbitP10TargetCoeff 26 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv26 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 26))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 26)) ≃*
      CocycleGroup (orbitP10TargetCocycle 26)
        (orbitP10TargetCocycle_consistent 26) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [2] (orbitP10RepresentativeCoeff 26)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_26))

theorem orbitP10_path_endpoint_27 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [2]
      (orbitP10RepresentativeCoeff 27) = orbitP10TargetCoeff 27 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv27 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 27))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 27)) ≃*
      CocycleGroup (orbitP10TargetCocycle 27)
        (orbitP10TargetCocycle_consistent 27) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [2] (orbitP10RepresentativeCoeff 27)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_27))

theorem orbitP10_path_endpoint_28 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [2]
      (orbitP10RepresentativeCoeff 28) = orbitP10TargetCoeff 28 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv28 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 28))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 28)) ≃*
      CocycleGroup (orbitP10TargetCocycle 28)
        (orbitP10TargetCocycle_consistent 28) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [2] (orbitP10RepresentativeCoeff 28)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_28))

theorem orbitP10_path_endpoint_29 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [0, 2]
      (orbitP10RepresentativeCoeff 29) = orbitP10TargetCoeff 29 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv29 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 29))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 29)) ≃*
      CocycleGroup (orbitP10TargetCocycle 29)
        (orbitP10TargetCocycle_consistent 29) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [0, 2] (orbitP10RepresentativeCoeff 29)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_29))

theorem orbitP10_path_endpoint_30 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [2, 0]
      (orbitP10RepresentativeCoeff 30) = orbitP10TargetCoeff 30 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv30 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 30))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 30)) ≃*
      CocycleGroup (orbitP10TargetCocycle 30)
        (orbitP10TargetCocycle_consistent 30) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [2, 0] (orbitP10RepresentativeCoeff 30)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_30))

theorem orbitP10_path_endpoint_31 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [2, 0]
      (orbitP10RepresentativeCoeff 31) = orbitP10TargetCoeff 31 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv31 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 31))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 31)) ≃*
      CocycleGroup (orbitP10TargetCocycle 31)
        (orbitP10TargetCocycle_consistent 31) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [2, 0] (orbitP10RepresentativeCoeff 31)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_31))

end Smallgroups.UsefulTheorems.Order32Certificate
