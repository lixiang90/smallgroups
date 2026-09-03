/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10Core

set_option maxRecDepth 100000

/-! Checked short orbit paths for parent 10; generated part 4. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP10_path_endpoint_48 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [6]
      (orbitP10RepresentativeCoeff 48) = orbitP10TargetCoeff 48 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv48 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 48))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 48)) ≃*
      CocycleGroup (orbitP10TargetCocycle 48)
        (orbitP10TargetCocycle_consistent 48) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [6] (orbitP10RepresentativeCoeff 48)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_48))

theorem orbitP10_path_endpoint_49 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [2, 0, 5]
      (orbitP10RepresentativeCoeff 49) = orbitP10TargetCoeff 49 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv49 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 49))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 49)) ≃*
      CocycleGroup (orbitP10TargetCocycle 49)
        (orbitP10TargetCocycle_consistent 49) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [2, 0, 5] (orbitP10RepresentativeCoeff 49)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_49))

theorem orbitP10_path_endpoint_50 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [0, 2, 5]
      (orbitP10RepresentativeCoeff 50) = orbitP10TargetCoeff 50 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv50 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 50))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 50)) ≃*
      CocycleGroup (orbitP10TargetCocycle 50)
        (orbitP10TargetCocycle_consistent 50) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [0, 2, 5] (orbitP10RepresentativeCoeff 50)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_50))

theorem orbitP10_path_endpoint_51 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [2]
      (orbitP10RepresentativeCoeff 51) = orbitP10TargetCoeff 51 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv51 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 51))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 51)) ≃*
      CocycleGroup (orbitP10TargetCocycle 51)
        (orbitP10TargetCocycle_consistent 51) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [2] (orbitP10RepresentativeCoeff 51)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_51))

theorem orbitP10_path_endpoint_52 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [2, 0, 5, 0]
      (orbitP10RepresentativeCoeff 52) = orbitP10TargetCoeff 52 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv52 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 52))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 52)) ≃*
      CocycleGroup (orbitP10TargetCocycle 52)
        (orbitP10TargetCocycle_consistent 52) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [2, 0, 5, 0] (orbitP10RepresentativeCoeff 52)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_52))

theorem orbitP10_path_endpoint_53 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [2, 5]
      (orbitP10RepresentativeCoeff 53) = orbitP10TargetCoeff 53 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv53 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 53))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 53)) ≃*
      CocycleGroup (orbitP10TargetCocycle 53)
        (orbitP10TargetCocycle_consistent 53) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [2, 5] (orbitP10RepresentativeCoeff 53)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_53))

theorem orbitP10_path_endpoint_54 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [0, 2, 5, 0]
      (orbitP10RepresentativeCoeff 54) = orbitP10TargetCoeff 54 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv54 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 54))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 54)) ≃*
      CocycleGroup (orbitP10TargetCocycle 54)
        (orbitP10TargetCocycle_consistent 54) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [0, 2, 5, 0] (orbitP10RepresentativeCoeff 54)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_54))

theorem orbitP10_path_endpoint_55 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [2, 0]
      (orbitP10RepresentativeCoeff 55) = orbitP10TargetCoeff 55 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv55 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 55))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 55)) ≃*
      CocycleGroup (orbitP10TargetCocycle 55)
        (orbitP10TargetCocycle_consistent 55) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [2, 0] (orbitP10RepresentativeCoeff 55)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_55))

theorem orbitP10_path_endpoint_56 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [2, 0]
      (orbitP10RepresentativeCoeff 56) = orbitP10TargetCoeff 56 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv56 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 56))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 56)) ≃*
      CocycleGroup (orbitP10TargetCocycle 56)
        (orbitP10TargetCocycle_consistent 56) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [2, 0] (orbitP10RepresentativeCoeff 56)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_56))

theorem orbitP10_path_endpoint_57 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [5, 6]
      (orbitP10RepresentativeCoeff 57) = orbitP10TargetCoeff 57 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv57 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 57))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 57)) ≃*
      CocycleGroup (orbitP10TargetCocycle 57)
        (orbitP10TargetCocycle_consistent 57) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [5, 6] (orbitP10RepresentativeCoeff 57)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_57))

theorem orbitP10_path_endpoint_58 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [2, 5]
      (orbitP10RepresentativeCoeff 58) = orbitP10TargetCoeff 58 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv58 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 58))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 58)) ≃*
      CocycleGroup (orbitP10TargetCocycle 58)
        (orbitP10TargetCocycle_consistent 58) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [2, 5] (orbitP10RepresentativeCoeff 58)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_58))

theorem orbitP10_path_endpoint_59 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [0, 2]
      (orbitP10RepresentativeCoeff 59) = orbitP10TargetCoeff 59 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv59 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 59))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 59)) ≃*
      CocycleGroup (orbitP10TargetCocycle 59)
        (orbitP10TargetCocycle_consistent 59) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [0, 2] (orbitP10RepresentativeCoeff 59)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_59))

theorem orbitP10_path_endpoint_60 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [2]
      (orbitP10RepresentativeCoeff 60) = orbitP10TargetCoeff 60 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv60 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 60))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 60)) ≃*
      CocycleGroup (orbitP10TargetCocycle 60)
        (orbitP10TargetCocycle_consistent 60) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [2] (orbitP10RepresentativeCoeff 60)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_60))

theorem orbitP10_path_endpoint_61 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [5, 0, 2]
      (orbitP10RepresentativeCoeff 61) = orbitP10TargetCoeff 61 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv61 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 61))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 61)) ≃*
      CocycleGroup (orbitP10TargetCocycle 61)
        (orbitP10TargetCocycle_consistent 61) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [5, 0, 2] (orbitP10RepresentativeCoeff 61)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_61))

theorem orbitP10_path_endpoint_62 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [0, 2, 0]
      (orbitP10RepresentativeCoeff 62) = orbitP10TargetCoeff 62 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv62 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 62))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 62)) ≃*
      CocycleGroup (orbitP10TargetCocycle 62)
        (orbitP10TargetCocycle_consistent 62) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [0, 2, 0] (orbitP10RepresentativeCoeff 62)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_62))

theorem orbitP10_path_endpoint_63 :
    Order16Table.applyOrbitPath orbitP10ActionColumns [2, 5, 0]
      (orbitP10RepresentativeCoeff 63) = orbitP10TargetCoeff 63 := by
  decide +kernel

noncomputable def orbitP10NormalizeEquiv63 :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index 63))
        (orbitP10SelectedCocycle_consistent (orbitP10Index 63)) ≃*
      CocycleGroup (orbitP10TargetCocycle 63)
        (orbitP10TargetCocycle_consistent 63) := by
  let e := Order16Table.orbitPathEquiv parent10Table coverageP10HBasis
    orbitP10ActionColumns orbitP10CorrectionColumns orbitP10_hbasis_cocycle
    orbitP10Aut orbitP10_action_linear [2, 5, 0] (orbitP10RepresentativeCoeff 63)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis)
      orbitP10_path_endpoint_63))

end Smallgroups.UsefulTheorems.Order32Certificate
