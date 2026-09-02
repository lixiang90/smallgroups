/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart05

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 6. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_80 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 0, 1]
      (orbitP14RepresentativeCoeff 80) = orbitP14TargetCoeff 80 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv80 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 80))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 80)) ≃*
      CocycleGroup (orbitP14TargetCocycle 80)
        (orbitP14TargetCocycle_consistent 80) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 0, 1] (orbitP14RepresentativeCoeff 80)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_80))

theorem orbitP14_path_endpoint_81 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 0, 1]
      (orbitP14RepresentativeCoeff 81) = orbitP14TargetCoeff 81 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv81 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 81))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 81)) ≃*
      CocycleGroup (orbitP14TargetCocycle 81)
        (orbitP14TargetCocycle_consistent 81) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 0, 1] (orbitP14RepresentativeCoeff 81)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_81))

theorem orbitP14_path_endpoint_82 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 2, 0]
      (orbitP14RepresentativeCoeff 82) = orbitP14TargetCoeff 82 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv82 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 82))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 82)) ≃*
      CocycleGroup (orbitP14TargetCocycle 82)
        (orbitP14TargetCocycle_consistent 82) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 2, 0] (orbitP14RepresentativeCoeff 82)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_82))

theorem orbitP14_path_endpoint_83 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 83) = orbitP14TargetCoeff 83 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv83 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 83))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 83)) ≃*
      CocycleGroup (orbitP14TargetCocycle 83)
        (orbitP14TargetCocycle_consistent 83) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1] (orbitP14RepresentativeCoeff 83)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_83))

theorem orbitP14_path_endpoint_84 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 0, 1, 0, 2, 1, 0, 1]
      (orbitP14RepresentativeCoeff 84) = orbitP14TargetCoeff 84 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv84 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 84))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 84)) ≃*
      CocycleGroup (orbitP14TargetCocycle 84)
        (orbitP14TargetCocycle_consistent 84) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 0, 1, 0, 2, 1, 0, 1] (orbitP14RepresentativeCoeff 84)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_84))

theorem orbitP14_path_endpoint_85 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 85) = orbitP14TargetCoeff 85 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv85 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 85))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 85)) ≃*
      CocycleGroup (orbitP14TargetCocycle 85)
        (orbitP14TargetCocycle_consistent 85) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 85)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_85))

theorem orbitP14_path_endpoint_86 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 0, 1]
      (orbitP14RepresentativeCoeff 86) = orbitP14TargetCoeff 86 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv86 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 86))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 86)) ≃*
      CocycleGroup (orbitP14TargetCocycle 86)
        (orbitP14TargetCocycle_consistent 86) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 0, 1] (orbitP14RepresentativeCoeff 86)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_86))

theorem orbitP14_path_endpoint_87 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 87) = orbitP14TargetCoeff 87 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv87 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 87))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 87)) ≃*
      CocycleGroup (orbitP14TargetCocycle 87)
        (orbitP14TargetCocycle_consistent 87) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 87)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_87))

theorem orbitP14_path_endpoint_88 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 0, 1]
      (orbitP14RepresentativeCoeff 88) = orbitP14TargetCoeff 88 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv88 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 88))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 88)) ≃*
      CocycleGroup (orbitP14TargetCocycle 88)
        (orbitP14TargetCocycle_consistent 88) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 0, 1] (orbitP14RepresentativeCoeff 88)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_88))

theorem orbitP14_path_endpoint_89 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 0, 2, 0]
      (orbitP14RepresentativeCoeff 89) = orbitP14TargetCoeff 89 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv89 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 89))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 89)) ≃*
      CocycleGroup (orbitP14TargetCocycle 89)
        (orbitP14TargetCocycle_consistent 89) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 0, 2, 0] (orbitP14RepresentativeCoeff 89)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_89))

theorem orbitP14_path_endpoint_90 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1]
      (orbitP14RepresentativeCoeff 90) = orbitP14TargetCoeff 90 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv90 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 90))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 90)) ≃*
      CocycleGroup (orbitP14TargetCocycle 90)
        (orbitP14TargetCocycle_consistent 90) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1] (orbitP14RepresentativeCoeff 90)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_90))

theorem orbitP14_path_endpoint_91 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1]
      (orbitP14RepresentativeCoeff 91) = orbitP14TargetCoeff 91 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv91 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 91))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 91)) ≃*
      CocycleGroup (orbitP14TargetCocycle 91)
        (orbitP14TargetCocycle_consistent 91) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1] (orbitP14RepresentativeCoeff 91)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_91))

theorem orbitP14_path_endpoint_92 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 92) = orbitP14TargetCoeff 92 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv92 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 92))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 92)) ≃*
      CocycleGroup (orbitP14TargetCocycle 92)
        (orbitP14TargetCocycle_consistent 92) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 92)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_92))

theorem orbitP14_path_endpoint_93 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 0, 2, 0]
      (orbitP14RepresentativeCoeff 93) = orbitP14TargetCoeff 93 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv93 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 93))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 93)) ≃*
      CocycleGroup (orbitP14TargetCocycle 93)
        (orbitP14TargetCocycle_consistent 93) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 0, 2, 0] (orbitP14RepresentativeCoeff 93)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_93))

theorem orbitP14_path_endpoint_94 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 0]
      (orbitP14RepresentativeCoeff 94) = orbitP14TargetCoeff 94 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv94 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 94))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 94)) ≃*
      CocycleGroup (orbitP14TargetCocycle 94)
        (orbitP14TargetCocycle_consistent 94) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 0] (orbitP14RepresentativeCoeff 94)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_94))

theorem orbitP14_path_endpoint_95 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 95) = orbitP14TargetCoeff 95 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv95 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 95))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 95)) ≃*
      CocycleGroup (orbitP14TargetCocycle 95)
        (orbitP14TargetCocycle_consistent 95) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 95)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_95))

end Smallgroups.UsefulTheorems.Order32Certificate
