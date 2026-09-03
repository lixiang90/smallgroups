/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11Core

set_option maxRecDepth 100000

/-! Checked short orbit paths for parent 11; generated part 4. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP11_path_endpoint_48 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [2, 5]
      (orbitP11RepresentativeCoeff 48) = orbitP11TargetCoeff 48 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv48 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 48))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 48)) ≃*
      CocycleGroup (orbitP11TargetCocycle 48)
        (orbitP11TargetCocycle_consistent 48) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [2, 5] (orbitP11RepresentativeCoeff 48)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_48))

theorem orbitP11_path_endpoint_49 :
    Order16Table.applyOrbitPath orbitP11ActionColumns []
      (orbitP11RepresentativeCoeff 49) = orbitP11TargetCoeff 49 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv49 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 49))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 49)) ≃*
      CocycleGroup (orbitP11TargetCocycle 49)
        (orbitP11TargetCocycle_consistent 49) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [] (orbitP11RepresentativeCoeff 49)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_49))

theorem orbitP11_path_endpoint_50 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [2]
      (orbitP11RepresentativeCoeff 50) = orbitP11TargetCoeff 50 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv50 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 50))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 50)) ≃*
      CocycleGroup (orbitP11TargetCocycle 50)
        (orbitP11TargetCocycle_consistent 50) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [2] (orbitP11RepresentativeCoeff 50)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_50))

theorem orbitP11_path_endpoint_51 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [5]
      (orbitP11RepresentativeCoeff 51) = orbitP11TargetCoeff 51 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv51 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 51))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 51)) ≃*
      CocycleGroup (orbitP11TargetCocycle 51)
        (orbitP11TargetCocycle_consistent 51) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [5] (orbitP11RepresentativeCoeff 51)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_51))

theorem orbitP11_path_endpoint_52 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [0]
      (orbitP11RepresentativeCoeff 52) = orbitP11TargetCoeff 52 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv52 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 52))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 52)) ≃*
      CocycleGroup (orbitP11TargetCocycle 52)
        (orbitP11TargetCocycle_consistent 52) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [0] (orbitP11RepresentativeCoeff 52)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_52))

theorem orbitP11_path_endpoint_53 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [0]
      (orbitP11RepresentativeCoeff 53) = orbitP11TargetCoeff 53 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv53 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 53))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 53)) ≃*
      CocycleGroup (orbitP11TargetCocycle 53)
        (orbitP11TargetCocycle_consistent 53) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [0] (orbitP11RepresentativeCoeff 53)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_53))

theorem orbitP11_path_endpoint_54 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [0, 5]
      (orbitP11RepresentativeCoeff 54) = orbitP11TargetCoeff 54 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv54 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 54))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 54)) ≃*
      CocycleGroup (orbitP11TargetCocycle 54)
        (orbitP11TargetCocycle_consistent 54) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [0, 5] (orbitP11RepresentativeCoeff 54)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_54))

theorem orbitP11_path_endpoint_55 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [0, 5]
      (orbitP11RepresentativeCoeff 55) = orbitP11TargetCoeff 55 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv55 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 55))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 55)) ≃*
      CocycleGroup (orbitP11TargetCocycle 55)
        (orbitP11TargetCocycle_consistent 55) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [0, 5] (orbitP11RepresentativeCoeff 55)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_55))

theorem orbitP11_path_endpoint_56 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [0]
      (orbitP11RepresentativeCoeff 56) = orbitP11TargetCoeff 56 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv56 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 56))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 56)) ≃*
      CocycleGroup (orbitP11TargetCocycle 56)
        (orbitP11TargetCocycle_consistent 56) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [0] (orbitP11RepresentativeCoeff 56)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_56))

theorem orbitP11_path_endpoint_57 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [1, 5]
      (orbitP11RepresentativeCoeff 57) = orbitP11TargetCoeff 57 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv57 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 57))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 57)) ≃*
      CocycleGroup (orbitP11TargetCocycle 57)
        (orbitP11TargetCocycle_consistent 57) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [1, 5] (orbitP11RepresentativeCoeff 57)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_57))

theorem orbitP11_path_endpoint_58 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [0, 5]
      (orbitP11RepresentativeCoeff 58) = orbitP11TargetCoeff 58 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv58 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 58))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 58)) ≃*
      CocycleGroup (orbitP11TargetCocycle 58)
        (orbitP11TargetCocycle_consistent 58) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [0, 5] (orbitP11RepresentativeCoeff 58)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_58))

theorem orbitP11_path_endpoint_59 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [1]
      (orbitP11RepresentativeCoeff 59) = orbitP11TargetCoeff 59 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv59 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 59))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 59)) ≃*
      CocycleGroup (orbitP11TargetCocycle 59)
        (orbitP11TargetCocycle_consistent 59) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [1] (orbitP11RepresentativeCoeff 59)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_59))

theorem orbitP11_path_endpoint_60 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [1, 5]
      (orbitP11RepresentativeCoeff 60) = orbitP11TargetCoeff 60 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv60 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 60))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 60)) ≃*
      CocycleGroup (orbitP11TargetCocycle 60)
        (orbitP11TargetCocycle_consistent 60) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [1, 5] (orbitP11RepresentativeCoeff 60)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_60))

theorem orbitP11_path_endpoint_61 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [2, 5]
      (orbitP11RepresentativeCoeff 61) = orbitP11TargetCoeff 61 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv61 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 61))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 61)) ≃*
      CocycleGroup (orbitP11TargetCocycle 61)
        (orbitP11TargetCocycle_consistent 61) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [2, 5] (orbitP11RepresentativeCoeff 61)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_61))

theorem orbitP11_path_endpoint_62 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [1]
      (orbitP11RepresentativeCoeff 62) = orbitP11TargetCoeff 62 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv62 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 62))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 62)) ≃*
      CocycleGroup (orbitP11TargetCocycle 62)
        (orbitP11TargetCocycle_consistent 62) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [1] (orbitP11RepresentativeCoeff 62)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_62))

theorem orbitP11_path_endpoint_63 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [2]
      (orbitP11RepresentativeCoeff 63) = orbitP11TargetCoeff 63 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv63 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 63))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 63)) ≃*
      CocycleGroup (orbitP11TargetCocycle 63)
        (orbitP11TargetCocycle_consistent 63) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [2] (orbitP11RepresentativeCoeff 63)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_63))

end Smallgroups.UsefulTheorems.Order32Certificate
