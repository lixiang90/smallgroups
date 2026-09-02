/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart04

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 5. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_64 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 1]
      (orbitP14RepresentativeCoeff 64) = orbitP14TargetCoeff 64 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv64 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 64))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 64)) ≃*
      CocycleGroup (orbitP14TargetCocycle 64)
        (orbitP14TargetCocycle_consistent 64) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 1] (orbitP14RepresentativeCoeff 64)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_64))

theorem orbitP14_path_endpoint_65 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 0, 2, 1, 2, 1]
      (orbitP14RepresentativeCoeff 65) = orbitP14TargetCoeff 65 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv65 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 65))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 65)) ≃*
      CocycleGroup (orbitP14TargetCocycle 65)
        (orbitP14TargetCocycle_consistent 65) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 0, 2, 1, 2, 1] (orbitP14RepresentativeCoeff 65)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_65))

theorem orbitP14_path_endpoint_66 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1]
      (orbitP14RepresentativeCoeff 66) = orbitP14TargetCoeff 66 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv66 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 66))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 66)) ≃*
      CocycleGroup (orbitP14TargetCocycle 66)
        (orbitP14TargetCocycle_consistent 66) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1] (orbitP14RepresentativeCoeff 66)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_66))

theorem orbitP14_path_endpoint_67 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 67) = orbitP14TargetCoeff 67 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv67 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 67))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 67)) ≃*
      CocycleGroup (orbitP14TargetCocycle 67)
        (orbitP14TargetCocycle_consistent 67) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 0] (orbitP14RepresentativeCoeff 67)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_67))

theorem orbitP14_path_endpoint_68 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 1, 1]
      (orbitP14RepresentativeCoeff 68) = orbitP14TargetCoeff 68 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv68 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 68))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 68)) ≃*
      CocycleGroup (orbitP14TargetCocycle 68)
        (orbitP14TargetCocycle_consistent 68) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 1, 1] (orbitP14RepresentativeCoeff 68)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_68))

theorem orbitP14_path_endpoint_69 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2]
      (orbitP14RepresentativeCoeff 69) = orbitP14TargetCoeff 69 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv69 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 69))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 69)) ≃*
      CocycleGroup (orbitP14TargetCocycle 69)
        (orbitP14TargetCocycle_consistent 69) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2] (orbitP14RepresentativeCoeff 69)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_69))

theorem orbitP14_path_endpoint_70 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 0, 1, 1, 1]
      (orbitP14RepresentativeCoeff 70) = orbitP14TargetCoeff 70 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv70 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 70))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 70)) ≃*
      CocycleGroup (orbitP14TargetCocycle 70)
        (orbitP14TargetCocycle_consistent 70) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 0, 1, 1, 1] (orbitP14RepresentativeCoeff 70)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_70))

theorem orbitP14_path_endpoint_71 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0]
      (orbitP14RepresentativeCoeff 71) = orbitP14TargetCoeff 71 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv71 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 71))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 71)) ≃*
      CocycleGroup (orbitP14TargetCocycle 71)
        (orbitP14TargetCocycle_consistent 71) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0] (orbitP14RepresentativeCoeff 71)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_71))

theorem orbitP14_path_endpoint_72 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0]
      (orbitP14RepresentativeCoeff 72) = orbitP14TargetCoeff 72 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv72 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 72))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 72)) ≃*
      CocycleGroup (orbitP14TargetCocycle 72)
        (orbitP14TargetCocycle_consistent 72) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0] (orbitP14RepresentativeCoeff 72)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_72))

theorem orbitP14_path_endpoint_73 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 73) = orbitP14TargetCoeff 73 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv73 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 73))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 73)) ≃*
      CocycleGroup (orbitP14TargetCocycle 73)
        (orbitP14TargetCocycle_consistent 73) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 0] (orbitP14RepresentativeCoeff 73)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_73))

theorem orbitP14_path_endpoint_74 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 1, 2, 1]
      (orbitP14RepresentativeCoeff 74) = orbitP14TargetCoeff 74 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv74 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 74))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 74)) ≃*
      CocycleGroup (orbitP14TargetCocycle 74)
        (orbitP14TargetCocycle_consistent 74) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 1, 2, 1] (orbitP14RepresentativeCoeff 74)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_74))

theorem orbitP14_path_endpoint_75 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 75) = orbitP14TargetCoeff 75 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv75 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 75))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 75)) ≃*
      CocycleGroup (orbitP14TargetCocycle 75)
        (orbitP14TargetCocycle_consistent 75) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1] (orbitP14RepresentativeCoeff 75)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_75))

theorem orbitP14_path_endpoint_76 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 76) = orbitP14TargetCoeff 76 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv76 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 76))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 76)) ≃*
      CocycleGroup (orbitP14TargetCocycle 76)
        (orbitP14TargetCocycle_consistent 76) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 1, 1, 2, 0] (orbitP14RepresentativeCoeff 76)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_76))

theorem orbitP14_path_endpoint_77 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 0, 1]
      (orbitP14RepresentativeCoeff 77) = orbitP14TargetCoeff 77 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv77 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 77))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 77)) ≃*
      CocycleGroup (orbitP14TargetCocycle 77)
        (orbitP14TargetCocycle_consistent 77) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 0, 1] (orbitP14RepresentativeCoeff 77)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_77))

theorem orbitP14_path_endpoint_78 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1]
      (orbitP14RepresentativeCoeff 78) = orbitP14TargetCoeff 78 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv78 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 78))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 78)) ≃*
      CocycleGroup (orbitP14TargetCocycle 78)
        (orbitP14TargetCocycle_consistent 78) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1] (orbitP14RepresentativeCoeff 78)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_78))

theorem orbitP14_path_endpoint_79 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 1, 1, 2]
      (orbitP14RepresentativeCoeff 79) = orbitP14TargetCoeff 79 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv79 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 79))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 79)) ≃*
      CocycleGroup (orbitP14TargetCocycle 79)
        (orbitP14TargetCocycle_consistent 79) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 1, 1, 2] (orbitP14RepresentativeCoeff 79)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_79))

end Smallgroups.UsefulTheorems.Order32Certificate
