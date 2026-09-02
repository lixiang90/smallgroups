/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart02

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 3. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_32 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 0, 1]
      (orbitP14RepresentativeCoeff 32) = orbitP14TargetCoeff 32 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv32 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 32))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 32)) ≃*
      CocycleGroup (orbitP14TargetCocycle 32)
        (orbitP14TargetCocycle_consistent 32) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 0, 1] (orbitP14RepresentativeCoeff 32)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_32))

theorem orbitP14_path_endpoint_33 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1]
      (orbitP14RepresentativeCoeff 33) = orbitP14TargetCoeff 33 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv33 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 33))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 33)) ≃*
      CocycleGroup (orbitP14TargetCocycle 33)
        (orbitP14TargetCocycle_consistent 33) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1] (orbitP14RepresentativeCoeff 33)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_33))

theorem orbitP14_path_endpoint_34 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 0, 2]
      (orbitP14RepresentativeCoeff 34) = orbitP14TargetCoeff 34 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv34 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 34))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 34)) ≃*
      CocycleGroup (orbitP14TargetCocycle 34)
        (orbitP14TargetCocycle_consistent 34) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 0, 2] (orbitP14RepresentativeCoeff 34)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_34))

theorem orbitP14_path_endpoint_35 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 0, 2, 1]
      (orbitP14RepresentativeCoeff 35) = orbitP14TargetCoeff 35 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv35 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 35))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 35)) ≃*
      CocycleGroup (orbitP14TargetCocycle 35)
        (orbitP14TargetCocycle_consistent 35) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 0, 2, 1] (orbitP14RepresentativeCoeff 35)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_35))

theorem orbitP14_path_endpoint_36 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 1, 2]
      (orbitP14RepresentativeCoeff 36) = orbitP14TargetCoeff 36 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv36 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 36))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 36)) ≃*
      CocycleGroup (orbitP14TargetCocycle 36)
        (orbitP14TargetCocycle_consistent 36) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 1, 2] (orbitP14RepresentativeCoeff 36)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_36))

theorem orbitP14_path_endpoint_37 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 0, 2, 1, 0]
      (orbitP14RepresentativeCoeff 37) = orbitP14TargetCoeff 37 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv37 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 37))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 37)) ≃*
      CocycleGroup (orbitP14TargetCocycle 37)
        (orbitP14TargetCocycle_consistent 37) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 0, 2, 1, 0] (orbitP14RepresentativeCoeff 37)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_37))

theorem orbitP14_path_endpoint_38 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1]
      (orbitP14RepresentativeCoeff 38) = orbitP14TargetCoeff 38 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv38 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 38))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 38)) ≃*
      CocycleGroup (orbitP14TargetCocycle 38)
        (orbitP14TargetCocycle_consistent 38) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1] (orbitP14RepresentativeCoeff 38)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_38))

theorem orbitP14_path_endpoint_39 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1]
      (orbitP14RepresentativeCoeff 39) = orbitP14TargetCoeff 39 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv39 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 39))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 39)) ≃*
      CocycleGroup (orbitP14TargetCocycle 39)
        (orbitP14TargetCocycle_consistent 39) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1] (orbitP14RepresentativeCoeff 39)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_39))

theorem orbitP14_path_endpoint_40 :
    Order16Table.applyOrbitPath orbitP14ActionColumns []
      (orbitP14RepresentativeCoeff 40) = orbitP14TargetCoeff 40 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv40 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 40))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 40)) ≃*
      CocycleGroup (orbitP14TargetCocycle 40)
        (orbitP14TargetCocycle_consistent 40) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [] (orbitP14RepresentativeCoeff 40)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_40))

theorem orbitP14_path_endpoint_41 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 0, 1, 2]
      (orbitP14RepresentativeCoeff 41) = orbitP14TargetCoeff 41 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv41 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 41))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 41)) ≃*
      CocycleGroup (orbitP14TargetCocycle 41)
        (orbitP14TargetCocycle_consistent 41) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 0, 1, 2] (orbitP14RepresentativeCoeff 41)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_41))

theorem orbitP14_path_endpoint_42 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2]
      (orbitP14RepresentativeCoeff 42) = orbitP14TargetCoeff 42 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv42 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 42))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 42)) ≃*
      CocycleGroup (orbitP14TargetCocycle 42)
        (orbitP14TargetCocycle_consistent 42) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2] (orbitP14RepresentativeCoeff 42)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_42))

theorem orbitP14_path_endpoint_43 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 43) = orbitP14TargetCoeff 43 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv43 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 43))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 43)) ≃*
      CocycleGroup (orbitP14TargetCocycle 43)
        (orbitP14TargetCocycle_consistent 43) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 43)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_43))

theorem orbitP14_path_endpoint_44 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 0]
      (orbitP14RepresentativeCoeff 44) = orbitP14TargetCoeff 44 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv44 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 44))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 44)) ≃*
      CocycleGroup (orbitP14TargetCocycle 44)
        (orbitP14TargetCocycle_consistent 44) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 0] (orbitP14RepresentativeCoeff 44)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_44))

theorem orbitP14_path_endpoint_45 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 1, 2]
      (orbitP14RepresentativeCoeff 45) = orbitP14TargetCoeff 45 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv45 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 45))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 45)) ≃*
      CocycleGroup (orbitP14TargetCocycle 45)
        (orbitP14TargetCocycle_consistent 45) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 1, 2] (orbitP14RepresentativeCoeff 45)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_45))

theorem orbitP14_path_endpoint_46 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 1, 1]
      (orbitP14RepresentativeCoeff 46) = orbitP14TargetCoeff 46 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv46 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 46))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 46)) ≃*
      CocycleGroup (orbitP14TargetCocycle 46)
        (orbitP14TargetCocycle_consistent 46) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 1, 1] (orbitP14RepresentativeCoeff 46)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_46))

theorem orbitP14_path_endpoint_47 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 0, 1, 0, 2]
      (orbitP14RepresentativeCoeff 47) = orbitP14TargetCoeff 47 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv47 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 47))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 47)) ≃*
      CocycleGroup (orbitP14TargetCocycle 47)
        (orbitP14TargetCocycle_consistent 47) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 0, 1, 0, 2] (orbitP14RepresentativeCoeff 47)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_47))

end Smallgroups.UsefulTheorems.Order32Certificate
