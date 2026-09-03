/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10Core

set_option maxRecDepth 100000

/-! Checked short orbit paths for parent 10; generated part 3. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP10_path_endpoint_32 :
    Order16Table.applyOrbitPath orbitP10ActionColumns []
      (orbitP10RepresentativeCoeff 32) = orbitP10TargetCoeff 32 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv32 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 32))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 32)) ≃*
      CocycleGroup (orbitP10TargetCocycle 32)
        (orbitP10TargetCocycle_consistent 32) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [] (orbitP10RepresentativeCoeff 32)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_32))

theorem orbitP10_path_endpoint_33 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [0]
      (orbitP10RepresentativeCoeff 33) = orbitP10TargetCoeff 33 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv33 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 33))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 33)) ≃*
      CocycleGroup (orbitP10TargetCocycle 33)
        (orbitP10TargetCocycle_consistent 33) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [0] (orbitP10RepresentativeCoeff 33)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_33))

theorem orbitP10_path_endpoint_34 :
    Order16Table.applyOrbitPath orbitP10ActionColumns []
      (orbitP10RepresentativeCoeff 34) = orbitP10TargetCoeff 34 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv34 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 34))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 34)) ≃*
      CocycleGroup (orbitP10TargetCocycle 34)
        (orbitP10TargetCocycle_consistent 34) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [] (orbitP10RepresentativeCoeff 34)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_34))

theorem orbitP10_path_endpoint_35 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [5, 0, 5]
      (orbitP10RepresentativeCoeff 35) = orbitP10TargetCoeff 35 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv35 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 35))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 35)) ≃*
      CocycleGroup (orbitP10TargetCocycle 35)
        (orbitP10TargetCocycle_consistent 35) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [5, 0, 5] (orbitP10RepresentativeCoeff 35)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_35))

theorem orbitP10_path_endpoint_36 :
    Order16Table.applyOrbitPath orbitP10ActionColumns []
      (orbitP10RepresentativeCoeff 36) = orbitP10TargetCoeff 36 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv36 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 36))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 36)) ≃*
      CocycleGroup (orbitP10TargetCocycle 36)
        (orbitP10TargetCocycle_consistent 36) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [] (orbitP10RepresentativeCoeff 36)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_36))

theorem orbitP10_path_endpoint_37 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [0]
      (orbitP10RepresentativeCoeff 37) = orbitP10TargetCoeff 37 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv37 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 37))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 37)) ≃*
      CocycleGroup (orbitP10TargetCocycle 37)
        (orbitP10TargetCocycle_consistent 37) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [0] (orbitP10RepresentativeCoeff 37)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_37))

theorem orbitP10_path_endpoint_38 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [2, 6, 0, 5]
      (orbitP10RepresentativeCoeff 38) = orbitP10TargetCoeff 38 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv38 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 38))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 38)) ≃*
      CocycleGroup (orbitP10TargetCocycle 38)
        (orbitP10TargetCocycle_consistent 38) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [2, 6, 0, 5] (orbitP10RepresentativeCoeff 38)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_38))

theorem orbitP10_path_endpoint_39 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [2, 5, 6]
      (orbitP10RepresentativeCoeff 39) = orbitP10TargetCoeff 39 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv39 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 39))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 39)) ≃*
      CocycleGroup (orbitP10TargetCocycle 39)
        (orbitP10TargetCocycle_consistent 39) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [2, 5, 6] (orbitP10RepresentativeCoeff 39)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_39))

theorem orbitP10_path_endpoint_40 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [0, 5]
      (orbitP10RepresentativeCoeff 40) = orbitP10TargetCoeff 40 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv40 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 40))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 40)) ≃*
      CocycleGroup (orbitP10TargetCocycle 40)
        (orbitP10TargetCocycle_consistent 40) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [0, 5] (orbitP10RepresentativeCoeff 40)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_40))

theorem orbitP10_path_endpoint_41 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [2]
      (orbitP10RepresentativeCoeff 41) = orbitP10TargetCoeff 41 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv41 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 41))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 41)) ≃*
      CocycleGroup (orbitP10TargetCocycle 41)
        (orbitP10TargetCocycle_consistent 41) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [2] (orbitP10RepresentativeCoeff 41)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_41))

theorem orbitP10_path_endpoint_42 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [5, 0]
      (orbitP10RepresentativeCoeff 42) = orbitP10TargetCoeff 42 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv42 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 42))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 42)) ≃*
      CocycleGroup (orbitP10TargetCocycle 42)
        (orbitP10TargetCocycle_consistent 42) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [5, 0] (orbitP10RepresentativeCoeff 42)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_42))

theorem orbitP10_path_endpoint_43 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [5]
      (orbitP10RepresentativeCoeff 43) = orbitP10TargetCoeff 43 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv43 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 43))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 43)) ≃*
      CocycleGroup (orbitP10TargetCocycle 43)
        (orbitP10TargetCocycle_consistent 43) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [5] (orbitP10RepresentativeCoeff 43)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_43))

theorem orbitP10_path_endpoint_44 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [0, 5]
      (orbitP10RepresentativeCoeff 44) = orbitP10TargetCoeff 44 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv44 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 44))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 44)) ≃*
      CocycleGroup (orbitP10TargetCocycle 44)
        (orbitP10TargetCocycle_consistent 44) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [0, 5] (orbitP10RepresentativeCoeff 44)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_44))

theorem orbitP10_path_endpoint_45 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [5]
      (orbitP10RepresentativeCoeff 45) = orbitP10TargetCoeff 45 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv45 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 45))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 45)) ≃*
      CocycleGroup (orbitP10TargetCocycle 45)
        (orbitP10TargetCocycle_consistent 45) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [5] (orbitP10RepresentativeCoeff 45)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_45))

theorem orbitP10_path_endpoint_46 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [2, 6]
      (orbitP10RepresentativeCoeff 46) = orbitP10TargetCoeff 46 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv46 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 46))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 46)) ≃*
      CocycleGroup (orbitP10TargetCocycle 46)
        (orbitP10TargetCocycle_consistent 46) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [2, 6] (orbitP10RepresentativeCoeff 46)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_46))

theorem orbitP10_path_endpoint_47 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [2, 6, 0]
      (orbitP10RepresentativeCoeff 47) = orbitP10TargetCoeff 47 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv47 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 47))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 47)) ≃*
      CocycleGroup (orbitP10TargetCocycle 47)
        (orbitP10TargetCocycle_consistent 47) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [2, 6, 0] (orbitP10RepresentativeCoeff 47)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_47))

end Smallgroups.UsefulTheorems.Order32Certificate
