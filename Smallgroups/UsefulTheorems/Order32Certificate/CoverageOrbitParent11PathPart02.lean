/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11PathPart01

set_option maxRecDepth 100000

/-! Checked short orbit paths for parent 11; generated part 2. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP11_path_endpoint_16 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [0]
      (orbitP11RepresentativeCoeff 16) = orbitP11TargetCoeff 16 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv16 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 16))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 16)) ≃*
      CocycleGroup (orbitP11TargetCocycle 16)
        (orbitP11TargetCocycle_consistent 16) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [0] (orbitP11RepresentativeCoeff 16)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_16))

theorem orbitP11_path_endpoint_17 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [0]
      (orbitP11RepresentativeCoeff 17) = orbitP11TargetCoeff 17 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv17 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 17))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 17)) ≃*
      CocycleGroup (orbitP11TargetCocycle 17)
        (orbitP11TargetCocycle_consistent 17) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [0] (orbitP11RepresentativeCoeff 17)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_17))

theorem orbitP11_path_endpoint_18 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [2]
      (orbitP11RepresentativeCoeff 18) = orbitP11TargetCoeff 18 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv18 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 18))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 18)) ≃*
      CocycleGroup (orbitP11TargetCocycle 18)
        (orbitP11TargetCocycle_consistent 18) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [2] (orbitP11RepresentativeCoeff 18)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_18))

theorem orbitP11_path_endpoint_19 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [1]
      (orbitP11RepresentativeCoeff 19) = orbitP11TargetCoeff 19 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv19 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 19))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 19)) ≃*
      CocycleGroup (orbitP11TargetCocycle 19)
        (orbitP11TargetCocycle_consistent 19) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [1] (orbitP11RepresentativeCoeff 19)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_19))

theorem orbitP11_path_endpoint_20 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [2]
      (orbitP11RepresentativeCoeff 20) = orbitP11TargetCoeff 20 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv20 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 20))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 20)) ≃*
      CocycleGroup (orbitP11TargetCocycle 20)
        (orbitP11TargetCocycle_consistent 20) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [2] (orbitP11RepresentativeCoeff 20)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_20))

theorem orbitP11_path_endpoint_21 :
    Order16Table.applyOrbitPath orbitP11ActionColumns []
      (orbitP11RepresentativeCoeff 21) = orbitP11TargetCoeff 21 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv21 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 21))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 21)) ≃*
      CocycleGroup (orbitP11TargetCocycle 21)
        (orbitP11TargetCocycle_consistent 21) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [] (orbitP11RepresentativeCoeff 21)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_21))

theorem orbitP11_path_endpoint_22 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [2]
      (orbitP11RepresentativeCoeff 22) = orbitP11TargetCoeff 22 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv22 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 22))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 22)) ≃*
      CocycleGroup (orbitP11TargetCocycle 22)
        (orbitP11TargetCocycle_consistent 22) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [2] (orbitP11RepresentativeCoeff 22)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_22))

theorem orbitP11_path_endpoint_23 :
    Order16Table.applyOrbitPath orbitP11ActionColumns []
      (orbitP11RepresentativeCoeff 23) = orbitP11TargetCoeff 23 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv23 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 23))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 23)) ≃*
      CocycleGroup (orbitP11TargetCocycle 23)
        (orbitP11TargetCocycle_consistent 23) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [] (orbitP11RepresentativeCoeff 23)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_23))

theorem orbitP11_path_endpoint_24 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [0]
      (orbitP11RepresentativeCoeff 24) = orbitP11TargetCoeff 24 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv24 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 24))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 24)) ≃*
      CocycleGroup (orbitP11TargetCocycle 24)
        (orbitP11TargetCocycle_consistent 24) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [0] (orbitP11RepresentativeCoeff 24)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_24))

theorem orbitP11_path_endpoint_25 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [0]
      (orbitP11RepresentativeCoeff 25) = orbitP11TargetCoeff 25 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv25 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 25))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 25)) ≃*
      CocycleGroup (orbitP11TargetCocycle 25)
        (orbitP11TargetCocycle_consistent 25) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [0] (orbitP11RepresentativeCoeff 25)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_25))

theorem orbitP11_path_endpoint_26 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [1]
      (orbitP11RepresentativeCoeff 26) = orbitP11TargetCoeff 26 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv26 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 26))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 26)) ≃*
      CocycleGroup (orbitP11TargetCocycle 26)
        (orbitP11TargetCocycle_consistent 26) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [1] (orbitP11RepresentativeCoeff 26)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_26))

theorem orbitP11_path_endpoint_27 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [2]
      (orbitP11RepresentativeCoeff 27) = orbitP11TargetCoeff 27 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv27 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 27))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 27)) ≃*
      CocycleGroup (orbitP11TargetCocycle 27)
        (orbitP11TargetCocycle_consistent 27) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [2] (orbitP11RepresentativeCoeff 27)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_27))

theorem orbitP11_path_endpoint_28 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [0]
      (orbitP11RepresentativeCoeff 28) = orbitP11TargetCoeff 28 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv28 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 28))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 28)) ≃*
      CocycleGroup (orbitP11TargetCocycle 28)
        (orbitP11TargetCocycle_consistent 28) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [0] (orbitP11RepresentativeCoeff 28)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_28))

theorem orbitP11_path_endpoint_29 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [1]
      (orbitP11RepresentativeCoeff 29) = orbitP11TargetCoeff 29 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv29 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 29))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 29)) ≃*
      CocycleGroup (orbitP11TargetCocycle 29)
        (orbitP11TargetCocycle_consistent 29) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [1] (orbitP11RepresentativeCoeff 29)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_29))

theorem orbitP11_path_endpoint_30 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [0]
      (orbitP11RepresentativeCoeff 30) = orbitP11TargetCoeff 30 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv30 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 30))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 30)) ≃*
      CocycleGroup (orbitP11TargetCocycle 30)
        (orbitP11TargetCocycle_consistent 30) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [0] (orbitP11RepresentativeCoeff 30)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_30))

theorem orbitP11_path_endpoint_31 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [1]
      (orbitP11RepresentativeCoeff 31) = orbitP11TargetCoeff 31 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv31 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 31))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 31)) ≃*
      CocycleGroup (orbitP11TargetCocycle 31)
        (orbitP11TargetCocycle_consistent 31) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [1] (orbitP11RepresentativeCoeff 31)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_31))

end Smallgroups.UsefulTheorems.Order32Certificate
