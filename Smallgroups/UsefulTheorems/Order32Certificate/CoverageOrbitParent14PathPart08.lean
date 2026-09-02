/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart07

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 8. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_112 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 2, 0, 1, 1]
      (orbitP14RepresentativeCoeff 112) = orbitP14TargetCoeff 112 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv112 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 112))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 112)) ≃*
      CocycleGroup (orbitP14TargetCocycle 112)
        (orbitP14TargetCocycle_consistent 112) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 2, 0, 1, 1] (orbitP14RepresentativeCoeff 112)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_112))

theorem orbitP14_path_endpoint_113 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 1, 2, 1, 1, 2, 1, 2]
      (orbitP14RepresentativeCoeff 113) = orbitP14TargetCoeff 113 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv113 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 113))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 113)) ≃*
      CocycleGroup (orbitP14TargetCocycle 113)
        (orbitP14TargetCocycle_consistent 113) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 1, 2, 1, 1, 2, 1, 2] (orbitP14RepresentativeCoeff 113)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_113))

theorem orbitP14_path_endpoint_114 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 114) = orbitP14TargetCoeff 114 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv114 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 114))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 114)) ≃*
      CocycleGroup (orbitP14TargetCocycle 114)
        (orbitP14TargetCocycle_consistent 114) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 0, 1, 2] (orbitP14RepresentativeCoeff 114)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_114))

theorem orbitP14_path_endpoint_115 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 115) = orbitP14TargetCoeff 115 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv115 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 115))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 115)) ≃*
      CocycleGroup (orbitP14TargetCocycle 115)
        (orbitP14TargetCocycle_consistent 115) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 0, 1, 2] (orbitP14RepresentativeCoeff 115)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_115))

theorem orbitP14_path_endpoint_116 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 0, 1, 0, 1]
      (orbitP14RepresentativeCoeff 116) = orbitP14TargetCoeff 116 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv116 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 116))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 116)) ≃*
      CocycleGroup (orbitP14TargetCocycle 116)
        (orbitP14TargetCocycle_consistent 116) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 0, 1, 0, 1] (orbitP14RepresentativeCoeff 116)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_116))

theorem orbitP14_path_endpoint_117 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 0, 2, 1]
      (orbitP14RepresentativeCoeff 117) = orbitP14TargetCoeff 117 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv117 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 117))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 117)) ≃*
      CocycleGroup (orbitP14TargetCocycle 117)
        (orbitP14TargetCocycle_consistent 117) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 0, 2, 1] (orbitP14RepresentativeCoeff 117)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_117))

theorem orbitP14_path_endpoint_118 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 0, 1, 0, 2, 1, 0, 2, 0]
      (orbitP14RepresentativeCoeff 118) = orbitP14TargetCoeff 118 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv118 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 118))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 118)) ≃*
      CocycleGroup (orbitP14TargetCocycle 118)
        (orbitP14TargetCocycle_consistent 118) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 0, 1, 0, 2, 1, 0, 2, 0] (orbitP14RepresentativeCoeff 118)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_118))

theorem orbitP14_path_endpoint_119 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 0, 1, 1, 0]
      (orbitP14RepresentativeCoeff 119) = orbitP14TargetCoeff 119 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv119 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 119))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 119)) ≃*
      CocycleGroup (orbitP14TargetCocycle 119)
        (orbitP14TargetCocycle_consistent 119) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 0, 1, 1, 0] (orbitP14RepresentativeCoeff 119)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_119))

theorem orbitP14_path_endpoint_120 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 120) = orbitP14TargetCoeff 120 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv120 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 120))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 120)) ≃*
      CocycleGroup (orbitP14TargetCocycle 120)
        (orbitP14TargetCocycle_consistent 120) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 120)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_120))

theorem orbitP14_path_endpoint_121 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 121) = orbitP14TargetCoeff 121 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv121 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 121))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 121)) ≃*
      CocycleGroup (orbitP14TargetCocycle 121)
        (orbitP14TargetCocycle_consistent 121) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 1, 2, 0] (orbitP14RepresentativeCoeff 121)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_121))

theorem orbitP14_path_endpoint_122 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 0, 1]
      (orbitP14RepresentativeCoeff 122) = orbitP14TargetCoeff 122 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv122 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 122))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 122)) ≃*
      CocycleGroup (orbitP14TargetCocycle 122)
        (orbitP14TargetCocycle_consistent 122) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 0, 1] (orbitP14RepresentativeCoeff 122)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_122))

theorem orbitP14_path_endpoint_123 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 0, 1, 0, 2, 1]
      (orbitP14RepresentativeCoeff 123) = orbitP14TargetCoeff 123 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv123 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 123))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 123)) ≃*
      CocycleGroup (orbitP14TargetCocycle 123)
        (orbitP14TargetCocycle_consistent 123) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 0, 1, 0, 2, 1] (orbitP14RepresentativeCoeff 123)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_123))

theorem orbitP14_path_endpoint_124 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 0, 1, 1, 2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 124) = orbitP14TargetCoeff 124 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv124 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 124))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 124)) ≃*
      CocycleGroup (orbitP14TargetCocycle 124)
        (orbitP14TargetCocycle_consistent 124) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 0, 1, 1, 2, 0, 1, 2] (orbitP14RepresentativeCoeff 124)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_124))

theorem orbitP14_path_endpoint_125 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 2, 1, 1]
      (orbitP14RepresentativeCoeff 125) = orbitP14TargetCoeff 125 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv125 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 125))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 125)) ≃*
      CocycleGroup (orbitP14TargetCocycle 125)
        (orbitP14TargetCocycle_consistent 125) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 2, 1, 1] (orbitP14RepresentativeCoeff 125)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_125))

theorem orbitP14_path_endpoint_126 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 2, 1, 1, 1, 2]
      (orbitP14RepresentativeCoeff 126) = orbitP14TargetCoeff 126 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv126 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 126))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 126)) ≃*
      CocycleGroup (orbitP14TargetCocycle 126)
        (orbitP14TargetCocycle_consistent 126) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 2, 1, 1, 1, 2] (orbitP14RepresentativeCoeff 126)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_126))

theorem orbitP14_path_endpoint_127 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 1, 1, 0, 1, 2]
      (orbitP14RepresentativeCoeff 127) = orbitP14TargetCoeff 127 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv127 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 127))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 127)) ≃*
      CocycleGroup (orbitP14TargetCocycle 127)
        (orbitP14TargetCocycle_consistent 127) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 1, 1, 0, 1, 2] (orbitP14RepresentativeCoeff 127)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_127))

end Smallgroups.UsefulTheorems.Order32Certificate
