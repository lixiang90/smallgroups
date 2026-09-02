/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart08

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 9. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_128 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1]
      (orbitP14RepresentativeCoeff 128) = orbitP14TargetCoeff 128 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv128 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 128))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 128)) ≃*
      CocycleGroup (orbitP14TargetCocycle 128)
        (orbitP14TargetCocycle_consistent 128) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1] (orbitP14RepresentativeCoeff 128)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_128))

theorem orbitP14_path_endpoint_129 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0]
      (orbitP14RepresentativeCoeff 129) = orbitP14TargetCoeff 129 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv129 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 129))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 129)) ≃*
      CocycleGroup (orbitP14TargetCocycle 129)
        (orbitP14TargetCocycle_consistent 129) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0] (orbitP14RepresentativeCoeff 129)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_129))

theorem orbitP14_path_endpoint_130 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0]
      (orbitP14RepresentativeCoeff 130) = orbitP14TargetCoeff 130 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv130 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 130))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 130)) ≃*
      CocycleGroup (orbitP14TargetCocycle 130)
        (orbitP14TargetCocycle_consistent 130) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0] (orbitP14RepresentativeCoeff 130)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_130))

theorem orbitP14_path_endpoint_131 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 1]
      (orbitP14RepresentativeCoeff 131) = orbitP14TargetCoeff 131 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv131 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 131))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 131)) ≃*
      CocycleGroup (orbitP14TargetCocycle 131)
        (orbitP14TargetCocycle_consistent 131) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 1] (orbitP14RepresentativeCoeff 131)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_131))

theorem orbitP14_path_endpoint_132 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1]
      (orbitP14RepresentativeCoeff 132) = orbitP14TargetCoeff 132 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv132 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 132))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 132)) ≃*
      CocycleGroup (orbitP14TargetCocycle 132)
        (orbitP14TargetCocycle_consistent 132) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1] (orbitP14RepresentativeCoeff 132)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_132))

theorem orbitP14_path_endpoint_133 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0]
      (orbitP14RepresentativeCoeff 133) = orbitP14TargetCoeff 133 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv133 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 133))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 133)) ≃*
      CocycleGroup (orbitP14TargetCocycle 133)
        (orbitP14TargetCocycle_consistent 133) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0] (orbitP14RepresentativeCoeff 133)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_133))

theorem orbitP14_path_endpoint_134 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 0, 2]
      (orbitP14RepresentativeCoeff 134) = orbitP14TargetCoeff 134 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv134 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 134))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 134)) ≃*
      CocycleGroup (orbitP14TargetCocycle 134)
        (orbitP14TargetCocycle_consistent 134) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 0, 2] (orbitP14RepresentativeCoeff 134)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_134))

theorem orbitP14_path_endpoint_135 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 0, 2, 0, 1]
      (orbitP14RepresentativeCoeff 135) = orbitP14TargetCoeff 135 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv135 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 135))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 135)) ≃*
      CocycleGroup (orbitP14TargetCocycle 135)
        (orbitP14TargetCocycle_consistent 135) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 0, 2, 0, 1] (orbitP14RepresentativeCoeff 135)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_135))

theorem orbitP14_path_endpoint_136 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 1, 2]
      (orbitP14RepresentativeCoeff 136) = orbitP14TargetCoeff 136 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv136 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 136))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 136)) ≃*
      CocycleGroup (orbitP14TargetCocycle 136)
        (orbitP14TargetCocycle_consistent 136) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 1, 2] (orbitP14RepresentativeCoeff 136)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_136))

theorem orbitP14_path_endpoint_137 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2]
      (orbitP14RepresentativeCoeff 137) = orbitP14TargetCoeff 137 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv137 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 137))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 137)) ≃*
      CocycleGroup (orbitP14TargetCocycle 137)
        (orbitP14TargetCocycle_consistent 137) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2] (orbitP14RepresentativeCoeff 137)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_137))

theorem orbitP14_path_endpoint_138 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 2, 1, 2, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 138) = orbitP14TargetCoeff 138 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv138 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 138))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 138)) ≃*
      CocycleGroup (orbitP14TargetCocycle 138)
        (orbitP14TargetCocycle_consistent 138) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 2, 1, 2, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 138)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_138))

theorem orbitP14_path_endpoint_139 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 2, 1, 2, 1, 1, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 139) = orbitP14TargetCoeff 139 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv139 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 139))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 139)) ≃*
      CocycleGroup (orbitP14TargetCocycle 139)
        (orbitP14TargetCocycle_consistent 139) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 2, 1, 2, 1, 1, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 139)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_139))

theorem orbitP14_path_endpoint_140 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 0, 1, 1, 1]
      (orbitP14RepresentativeCoeff 140) = orbitP14TargetCoeff 140 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv140 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 140))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 140)) ≃*
      CocycleGroup (orbitP14TargetCocycle 140)
        (orbitP14TargetCocycle_consistent 140) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 0, 1, 1, 1] (orbitP14RepresentativeCoeff 140)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_140))

theorem orbitP14_path_endpoint_141 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 141) = orbitP14TargetCoeff 141 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv141 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 141))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 141)) ≃*
      CocycleGroup (orbitP14TargetCocycle 141)
        (orbitP14TargetCocycle_consistent 141) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 141)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_141))

theorem orbitP14_path_endpoint_142 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 2, 0, 1, 2, 1, 1, 0, 2, 1]
      (orbitP14RepresentativeCoeff 142) = orbitP14TargetCoeff 142 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv142 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 142))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 142)) ≃*
      CocycleGroup (orbitP14TargetCocycle 142)
        (orbitP14TargetCocycle_consistent 142) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 2, 0, 1, 2, 1, 1, 0, 2, 1] (orbitP14RepresentativeCoeff 142)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_142))

theorem orbitP14_path_endpoint_143 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 0, 1, 2, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 143) = orbitP14TargetCoeff 143 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv143 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 143))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 143)) ≃*
      CocycleGroup (orbitP14TargetCocycle 143)
        (orbitP14TargetCocycle_consistent 143) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 0, 1, 2, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 143)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_143))

end Smallgroups.UsefulTheorems.Order32Certificate
