/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11Core

set_option maxRecDepth 100000

/-! Checked short orbit paths for parent 11; generated part 3. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP11_path_endpoint_32 :
    Order16Table.applyOrbitPath orbitP11ActionColumns []
      (orbitP11RepresentativeCoeff 32) = orbitP11TargetCoeff 32 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv32 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 32))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 32)) ≃*
      CocycleGroup (orbitP11TargetCocycle 32)
        (orbitP11TargetCocycle_consistent 32) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [] (orbitP11RepresentativeCoeff 32)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_32))

theorem orbitP11_path_endpoint_33 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [0, 2, 5]
      (orbitP11RepresentativeCoeff 33) = orbitP11TargetCoeff 33 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv33 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 33))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 33)) ≃*
      CocycleGroup (orbitP11TargetCocycle 33)
        (orbitP11TargetCocycle_consistent 33) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [0, 2, 5] (orbitP11RepresentativeCoeff 33)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_33))

theorem orbitP11_path_endpoint_34 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [5]
      (orbitP11RepresentativeCoeff 34) = orbitP11TargetCoeff 34 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv34 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 34))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 34)) ≃*
      CocycleGroup (orbitP11TargetCocycle 34)
        (orbitP11TargetCocycle_consistent 34) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [5] (orbitP11RepresentativeCoeff 34)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_34))

theorem orbitP11_path_endpoint_35 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [0, 2]
      (orbitP11RepresentativeCoeff 35) = orbitP11TargetCoeff 35 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv35 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 35))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 35)) ≃*
      CocycleGroup (orbitP11TargetCocycle 35)
        (orbitP11TargetCocycle_consistent 35) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [0, 2] (orbitP11RepresentativeCoeff 35)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_35))

theorem orbitP11_path_endpoint_36 :
    Order16Table.applyOrbitPath orbitP11ActionColumns []
      (orbitP11RepresentativeCoeff 36) = orbitP11TargetCoeff 36 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv36 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 36))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 36)) ≃*
      CocycleGroup (orbitP11TargetCocycle 36)
        (orbitP11TargetCocycle_consistent 36) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [] (orbitP11RepresentativeCoeff 36)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_36))

theorem orbitP11_path_endpoint_37 :
    Order16Table.applyOrbitPath orbitP11ActionColumns []
      (orbitP11RepresentativeCoeff 37) = orbitP11TargetCoeff 37 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv37 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 37))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 37)) ≃*
      CocycleGroup (orbitP11TargetCocycle 37)
        (orbitP11TargetCocycle_consistent 37) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [] (orbitP11RepresentativeCoeff 37)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_37))

theorem orbitP11_path_endpoint_38 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [5]
      (orbitP11RepresentativeCoeff 38) = orbitP11TargetCoeff 38 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv38 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 38))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 38)) ≃*
      CocycleGroup (orbitP11TargetCocycle 38)
        (orbitP11TargetCocycle_consistent 38) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [5] (orbitP11RepresentativeCoeff 38)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_38))

theorem orbitP11_path_endpoint_39 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [5]
      (orbitP11RepresentativeCoeff 39) = orbitP11TargetCoeff 39 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv39 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 39))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 39)) ≃*
      CocycleGroup (orbitP11TargetCocycle 39)
        (orbitP11TargetCocycle_consistent 39) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [5] (orbitP11RepresentativeCoeff 39)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_39))

theorem orbitP11_path_endpoint_40 :
    Order16Table.applyOrbitPath orbitP11ActionColumns []
      (orbitP11RepresentativeCoeff 40) = orbitP11TargetCoeff 40 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv40 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 40))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 40)) ≃*
      CocycleGroup (orbitP11TargetCocycle 40)
        (orbitP11TargetCocycle_consistent 40) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [] (orbitP11RepresentativeCoeff 40)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_40))

theorem orbitP11_path_endpoint_41 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [0, 1, 5]
      (orbitP11RepresentativeCoeff 41) = orbitP11TargetCoeff 41 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv41 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 41))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 41)) ≃*
      CocycleGroup (orbitP11TargetCocycle 41)
        (orbitP11TargetCocycle_consistent 41) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [0, 1, 5] (orbitP11RepresentativeCoeff 41)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_41))

theorem orbitP11_path_endpoint_42 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [5]
      (orbitP11RepresentativeCoeff 42) = orbitP11TargetCoeff 42 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv42 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 42))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 42)) ≃*
      CocycleGroup (orbitP11TargetCocycle 42)
        (orbitP11TargetCocycle_consistent 42) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [5] (orbitP11RepresentativeCoeff 42)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_42))

theorem orbitP11_path_endpoint_43 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [0, 1]
      (orbitP11RepresentativeCoeff 43) = orbitP11TargetCoeff 43 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv43 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 43))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 43)) ≃*
      CocycleGroup (orbitP11TargetCocycle 43)
        (orbitP11TargetCocycle_consistent 43) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [0, 1] (orbitP11RepresentativeCoeff 43)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_43))

theorem orbitP11_path_endpoint_44 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [0]
      (orbitP11RepresentativeCoeff 44) = orbitP11TargetCoeff 44 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv44 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 44))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 44)) ≃*
      CocycleGroup (orbitP11TargetCocycle 44)
        (orbitP11TargetCocycle_consistent 44) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [0] (orbitP11RepresentativeCoeff 44)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_44))

theorem orbitP11_path_endpoint_45 :
    Order16Table.applyOrbitPath orbitP11ActionColumns []
      (orbitP11RepresentativeCoeff 45) = orbitP11TargetCoeff 45 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv45 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 45))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 45)) ≃*
      CocycleGroup (orbitP11TargetCocycle 45)
        (orbitP11TargetCocycle_consistent 45) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [] (orbitP11RepresentativeCoeff 45)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_45))

theorem orbitP11_path_endpoint_46 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [0, 5]
      (orbitP11RepresentativeCoeff 46) = orbitP11TargetCoeff 46 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv46 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 46))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 46)) ≃*
      CocycleGroup (orbitP11TargetCocycle 46)
        (orbitP11TargetCocycle_consistent 46) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [0, 5] (orbitP11RepresentativeCoeff 46)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_46))

theorem orbitP11_path_endpoint_47 :
    Order16Table.applyOrbitPath orbitP11ActionColumns [5]
      (orbitP11RepresentativeCoeff 47) = orbitP11TargetCoeff 47 := by
  decide +kernel

noncomputable def orbitP11NormalizeEquiv47 :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index 47))
        (orbitP11SelectedCocycle_consistent (orbitP11Index 47)) ≃*
      CocycleGroup (orbitP11TargetCocycle 47)
        (orbitP11TargetCocycle_consistent 47) := by
  let e := Order16Table.orbitPathEquiv parent11Table coverageP11HBasis
    orbitP11ActionColumns orbitP11CorrectionColumns orbitP11_hbasis_cocycle
    orbitP11Aut orbitP11_action_linear [5] (orbitP11RepresentativeCoeff 47)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis)
      orbitP11_path_endpoint_47))

end Smallgroups.UsefulTheorems.Order32Certificate
