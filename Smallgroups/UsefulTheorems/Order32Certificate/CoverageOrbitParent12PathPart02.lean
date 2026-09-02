/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent12Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent12PathPart01

set_option maxRecDepth 100000

/-! Checked short orbit paths for parent 12; generated part 2. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP12_path_endpoint_16 :
    Order16Table.applyOrbitPath orbitP12ActionColumns [1, 3]
      (orbitP12RepresentativeCoeff 16) = orbitP12TargetCoeff 16 := by
  decide +kernel

noncomputable def orbitP12NormalizeEquiv16 :
    CocycleGroup (orbitP12SelectedCocycle (orbitP12Index 16))
        (orbitP12SelectedCocycle_consistent (orbitP12Index 16)) ≃*
      CocycleGroup (orbitP12TargetCocycle 16)
        (orbitP12TargetCocycle_consistent 16) := by
  let e := Order16Table.orbitPathEquiv parent12Table coverageP12HBasis
    orbitP12ActionColumns orbitP12CorrectionColumns orbitP12_hbasis_cocycle
    orbitP12Aut orbitP12_action_linear [1, 3] (orbitP12RepresentativeCoeff 16)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent12Table coverageP12HBasis)
      orbitP12_path_endpoint_16))

theorem orbitP12_path_endpoint_17 :
    Order16Table.applyOrbitPath orbitP12ActionColumns [1, 0]
      (orbitP12RepresentativeCoeff 17) = orbitP12TargetCoeff 17 := by
  decide +kernel

noncomputable def orbitP12NormalizeEquiv17 :
    CocycleGroup (orbitP12SelectedCocycle (orbitP12Index 17))
        (orbitP12SelectedCocycle_consistent (orbitP12Index 17)) ≃*
      CocycleGroup (orbitP12TargetCocycle 17)
        (orbitP12TargetCocycle_consistent 17) := by
  let e := Order16Table.orbitPathEquiv parent12Table coverageP12HBasis
    orbitP12ActionColumns orbitP12CorrectionColumns orbitP12_hbasis_cocycle
    orbitP12Aut orbitP12_action_linear [1, 0] (orbitP12RepresentativeCoeff 17)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent12Table coverageP12HBasis)
      orbitP12_path_endpoint_17))

theorem orbitP12_path_endpoint_18 :
    Order16Table.applyOrbitPath orbitP12ActionColumns [0, 3]
      (orbitP12RepresentativeCoeff 18) = orbitP12TargetCoeff 18 := by
  decide +kernel

noncomputable def orbitP12NormalizeEquiv18 :
    CocycleGroup (orbitP12SelectedCocycle (orbitP12Index 18))
        (orbitP12SelectedCocycle_consistent (orbitP12Index 18)) ≃*
      CocycleGroup (orbitP12TargetCocycle 18)
        (orbitP12TargetCocycle_consistent 18) := by
  let e := Order16Table.orbitPathEquiv parent12Table coverageP12HBasis
    orbitP12ActionColumns orbitP12CorrectionColumns orbitP12_hbasis_cocycle
    orbitP12Aut orbitP12_action_linear [0, 3] (orbitP12RepresentativeCoeff 18)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent12Table coverageP12HBasis)
      orbitP12_path_endpoint_18))

theorem orbitP12_path_endpoint_19 :
    Order16Table.applyOrbitPath orbitP12ActionColumns [2]
      (orbitP12RepresentativeCoeff 19) = orbitP12TargetCoeff 19 := by
  decide +kernel

noncomputable def orbitP12NormalizeEquiv19 :
    CocycleGroup (orbitP12SelectedCocycle (orbitP12Index 19))
        (orbitP12SelectedCocycle_consistent (orbitP12Index 19)) ≃*
      CocycleGroup (orbitP12TargetCocycle 19)
        (orbitP12TargetCocycle_consistent 19) := by
  let e := Order16Table.orbitPathEquiv parent12Table coverageP12HBasis
    orbitP12ActionColumns orbitP12CorrectionColumns orbitP12_hbasis_cocycle
    orbitP12Aut orbitP12_action_linear [2] (orbitP12RepresentativeCoeff 19)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent12Table coverageP12HBasis)
      orbitP12_path_endpoint_19))

theorem orbitP12_path_endpoint_20 :
    Order16Table.applyOrbitPath orbitP12ActionColumns [3]
      (orbitP12RepresentativeCoeff 20) = orbitP12TargetCoeff 20 := by
  decide +kernel

noncomputable def orbitP12NormalizeEquiv20 :
    CocycleGroup (orbitP12SelectedCocycle (orbitP12Index 20))
        (orbitP12SelectedCocycle_consistent (orbitP12Index 20)) ≃*
      CocycleGroup (orbitP12TargetCocycle 20)
        (orbitP12TargetCocycle_consistent 20) := by
  let e := Order16Table.orbitPathEquiv parent12Table coverageP12HBasis
    orbitP12ActionColumns orbitP12CorrectionColumns orbitP12_hbasis_cocycle
    orbitP12Aut orbitP12_action_linear [3] (orbitP12RepresentativeCoeff 20)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent12Table coverageP12HBasis)
      orbitP12_path_endpoint_20))

theorem orbitP12_path_endpoint_21 :
    Order16Table.applyOrbitPath orbitP12ActionColumns [0]
      (orbitP12RepresentativeCoeff 21) = orbitP12TargetCoeff 21 := by
  decide +kernel

noncomputable def orbitP12NormalizeEquiv21 :
    CocycleGroup (orbitP12SelectedCocycle (orbitP12Index 21))
        (orbitP12SelectedCocycle_consistent (orbitP12Index 21)) ≃*
      CocycleGroup (orbitP12TargetCocycle 21)
        (orbitP12TargetCocycle_consistent 21) := by
  let e := Order16Table.orbitPathEquiv parent12Table coverageP12HBasis
    orbitP12ActionColumns orbitP12CorrectionColumns orbitP12_hbasis_cocycle
    orbitP12Aut orbitP12_action_linear [0] (orbitP12RepresentativeCoeff 21)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent12Table coverageP12HBasis)
      orbitP12_path_endpoint_21))

theorem orbitP12_path_endpoint_22 :
    Order16Table.applyOrbitPath orbitP12ActionColumns [0]
      (orbitP12RepresentativeCoeff 22) = orbitP12TargetCoeff 22 := by
  decide +kernel

noncomputable def orbitP12NormalizeEquiv22 :
    CocycleGroup (orbitP12SelectedCocycle (orbitP12Index 22))
        (orbitP12SelectedCocycle_consistent (orbitP12Index 22)) ≃*
      CocycleGroup (orbitP12TargetCocycle 22)
        (orbitP12TargetCocycle_consistent 22) := by
  let e := Order16Table.orbitPathEquiv parent12Table coverageP12HBasis
    orbitP12ActionColumns orbitP12CorrectionColumns orbitP12_hbasis_cocycle
    orbitP12Aut orbitP12_action_linear [0] (orbitP12RepresentativeCoeff 22)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent12Table coverageP12HBasis)
      orbitP12_path_endpoint_22))

theorem orbitP12_path_endpoint_23 :
    Order16Table.applyOrbitPath orbitP12ActionColumns [1]
      (orbitP12RepresentativeCoeff 23) = orbitP12TargetCoeff 23 := by
  decide +kernel

noncomputable def orbitP12NormalizeEquiv23 :
    CocycleGroup (orbitP12SelectedCocycle (orbitP12Index 23))
        (orbitP12SelectedCocycle_consistent (orbitP12Index 23)) ≃*
      CocycleGroup (orbitP12TargetCocycle 23)
        (orbitP12TargetCocycle_consistent 23) := by
  let e := Order16Table.orbitPathEquiv parent12Table coverageP12HBasis
    orbitP12ActionColumns orbitP12CorrectionColumns orbitP12_hbasis_cocycle
    orbitP12Aut orbitP12_action_linear [1] (orbitP12RepresentativeCoeff 23)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent12Table coverageP12HBasis)
      orbitP12_path_endpoint_23))

theorem orbitP12_path_endpoint_24 :
    Order16Table.applyOrbitPath orbitP12ActionColumns [3, 1]
      (orbitP12RepresentativeCoeff 24) = orbitP12TargetCoeff 24 := by
  decide +kernel

noncomputable def orbitP12NormalizeEquiv24 :
    CocycleGroup (orbitP12SelectedCocycle (orbitP12Index 24))
        (orbitP12SelectedCocycle_consistent (orbitP12Index 24)) ≃*
      CocycleGroup (orbitP12TargetCocycle 24)
        (orbitP12TargetCocycle_consistent 24) := by
  let e := Order16Table.orbitPathEquiv parent12Table coverageP12HBasis
    orbitP12ActionColumns orbitP12CorrectionColumns orbitP12_hbasis_cocycle
    orbitP12Aut orbitP12_action_linear [3, 1] (orbitP12RepresentativeCoeff 24)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent12Table coverageP12HBasis)
      orbitP12_path_endpoint_24))

theorem orbitP12_path_endpoint_25 :
    Order16Table.applyOrbitPath orbitP12ActionColumns [0, 1]
      (orbitP12RepresentativeCoeff 25) = orbitP12TargetCoeff 25 := by
  decide +kernel

noncomputable def orbitP12NormalizeEquiv25 :
    CocycleGroup (orbitP12SelectedCocycle (orbitP12Index 25))
        (orbitP12SelectedCocycle_consistent (orbitP12Index 25)) ≃*
      CocycleGroup (orbitP12TargetCocycle 25)
        (orbitP12TargetCocycle_consistent 25) := by
  let e := Order16Table.orbitPathEquiv parent12Table coverageP12HBasis
    orbitP12ActionColumns orbitP12CorrectionColumns orbitP12_hbasis_cocycle
    orbitP12Aut orbitP12_action_linear [0, 1] (orbitP12RepresentativeCoeff 25)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent12Table coverageP12HBasis)
      orbitP12_path_endpoint_25))

theorem orbitP12_path_endpoint_26 :
    Order16Table.applyOrbitPath orbitP12ActionColumns [0]
      (orbitP12RepresentativeCoeff 26) = orbitP12TargetCoeff 26 := by
  decide +kernel

noncomputable def orbitP12NormalizeEquiv26 :
    CocycleGroup (orbitP12SelectedCocycle (orbitP12Index 26))
        (orbitP12SelectedCocycle_consistent (orbitP12Index 26)) ≃*
      CocycleGroup (orbitP12TargetCocycle 26)
        (orbitP12TargetCocycle_consistent 26) := by
  let e := Order16Table.orbitPathEquiv parent12Table coverageP12HBasis
    orbitP12ActionColumns orbitP12CorrectionColumns orbitP12_hbasis_cocycle
    orbitP12Aut orbitP12_action_linear [0] (orbitP12RepresentativeCoeff 26)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent12Table coverageP12HBasis)
      orbitP12_path_endpoint_26))

theorem orbitP12_path_endpoint_27 :
    Order16Table.applyOrbitPath orbitP12ActionColumns [3, 0]
      (orbitP12RepresentativeCoeff 27) = orbitP12TargetCoeff 27 := by
  decide +kernel

noncomputable def orbitP12NormalizeEquiv27 :
    CocycleGroup (orbitP12SelectedCocycle (orbitP12Index 27))
        (orbitP12SelectedCocycle_consistent (orbitP12Index 27)) ≃*
      CocycleGroup (orbitP12TargetCocycle 27)
        (orbitP12TargetCocycle_consistent 27) := by
  let e := Order16Table.orbitPathEquiv parent12Table coverageP12HBasis
    orbitP12ActionColumns orbitP12CorrectionColumns orbitP12_hbasis_cocycle
    orbitP12Aut orbitP12_action_linear [3, 0] (orbitP12RepresentativeCoeff 27)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent12Table coverageP12HBasis)
      orbitP12_path_endpoint_27))

theorem orbitP12_path_endpoint_28 :
    Order16Table.applyOrbitPath orbitP12ActionColumns [0, 2]
      (orbitP12RepresentativeCoeff 28) = orbitP12TargetCoeff 28 := by
  decide +kernel

noncomputable def orbitP12NormalizeEquiv28 :
    CocycleGroup (orbitP12SelectedCocycle (orbitP12Index 28))
        (orbitP12SelectedCocycle_consistent (orbitP12Index 28)) ≃*
      CocycleGroup (orbitP12TargetCocycle 28)
        (orbitP12TargetCocycle_consistent 28) := by
  let e := Order16Table.orbitPathEquiv parent12Table coverageP12HBasis
    orbitP12ActionColumns orbitP12CorrectionColumns orbitP12_hbasis_cocycle
    orbitP12Aut orbitP12_action_linear [0, 2] (orbitP12RepresentativeCoeff 28)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent12Table coverageP12HBasis)
      orbitP12_path_endpoint_28))

theorem orbitP12_path_endpoint_29 :
    Order16Table.applyOrbitPath orbitP12ActionColumns [2]
      (orbitP12RepresentativeCoeff 29) = orbitP12TargetCoeff 29 := by
  decide +kernel

noncomputable def orbitP12NormalizeEquiv29 :
    CocycleGroup (orbitP12SelectedCocycle (orbitP12Index 29))
        (orbitP12SelectedCocycle_consistent (orbitP12Index 29)) ≃*
      CocycleGroup (orbitP12TargetCocycle 29)
        (orbitP12TargetCocycle_consistent 29) := by
  let e := Order16Table.orbitPathEquiv parent12Table coverageP12HBasis
    orbitP12ActionColumns orbitP12CorrectionColumns orbitP12_hbasis_cocycle
    orbitP12Aut orbitP12_action_linear [2] (orbitP12RepresentativeCoeff 29)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent12Table coverageP12HBasis)
      orbitP12_path_endpoint_29))

theorem orbitP12_path_endpoint_30 :
    Order16Table.applyOrbitPath orbitP12ActionColumns [0]
      (orbitP12RepresentativeCoeff 30) = orbitP12TargetCoeff 30 := by
  decide +kernel

noncomputable def orbitP12NormalizeEquiv30 :
    CocycleGroup (orbitP12SelectedCocycle (orbitP12Index 30))
        (orbitP12SelectedCocycle_consistent (orbitP12Index 30)) ≃*
      CocycleGroup (orbitP12TargetCocycle 30)
        (orbitP12TargetCocycle_consistent 30) := by
  let e := Order16Table.orbitPathEquiv parent12Table coverageP12HBasis
    orbitP12ActionColumns orbitP12CorrectionColumns orbitP12_hbasis_cocycle
    orbitP12Aut orbitP12_action_linear [0] (orbitP12RepresentativeCoeff 30)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent12Table coverageP12HBasis)
      orbitP12_path_endpoint_30))

theorem orbitP12_path_endpoint_31 :
    Order16Table.applyOrbitPath orbitP12ActionColumns [3]
      (orbitP12RepresentativeCoeff 31) = orbitP12TargetCoeff 31 := by
  decide +kernel

noncomputable def orbitP12NormalizeEquiv31 :
    CocycleGroup (orbitP12SelectedCocycle (orbitP12Index 31))
        (orbitP12SelectedCocycle_consistent (orbitP12Index 31)) ≃*
      CocycleGroup (orbitP12TargetCocycle 31)
        (orbitP12TargetCocycle_consistent 31) := by
  let e := Order16Table.orbitPathEquiv parent12Table coverageP12HBasis
    orbitP12ActionColumns orbitP12CorrectionColumns orbitP12_hbasis_cocycle
    orbitP12Aut orbitP12_action_linear [3] (orbitP12RepresentativeCoeff 31)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent12Table coverageP12HBasis)
      orbitP12_path_endpoint_31))

end Smallgroups.UsefulTheorems.Order32Certificate
