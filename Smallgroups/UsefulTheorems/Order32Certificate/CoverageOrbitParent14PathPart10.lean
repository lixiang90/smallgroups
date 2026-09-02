/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart09

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 10. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_144 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1]
      (orbitP14RepresentativeCoeff 144) = orbitP14TargetCoeff 144 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv144 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 144))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 144)) ≃*
      CocycleGroup (orbitP14TargetCocycle 144)
        (orbitP14TargetCocycle_consistent 144) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1] (orbitP14RepresentativeCoeff 144)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_144))

theorem orbitP14_path_endpoint_145 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 1, 0, 2]
      (orbitP14RepresentativeCoeff 145) = orbitP14TargetCoeff 145 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv145 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 145))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 145)) ≃*
      CocycleGroup (orbitP14TargetCocycle 145)
        (orbitP14TargetCocycle_consistent 145) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 1, 0, 2] (orbitP14RepresentativeCoeff 145)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_145))

theorem orbitP14_path_endpoint_146 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 0]
      (orbitP14RepresentativeCoeff 146) = orbitP14TargetCoeff 146 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv146 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 146))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 146)) ≃*
      CocycleGroup (orbitP14TargetCocycle 146)
        (orbitP14TargetCocycle_consistent 146) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 0] (orbitP14RepresentativeCoeff 146)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_146))

theorem orbitP14_path_endpoint_147 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 147) = orbitP14TargetCoeff 147 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv147 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 147))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 147)) ≃*
      CocycleGroup (orbitP14TargetCocycle 147)
        (orbitP14TargetCocycle_consistent 147) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 1, 1, 2, 0] (orbitP14RepresentativeCoeff 147)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_147))

theorem orbitP14_path_endpoint_148 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2]
      (orbitP14RepresentativeCoeff 148) = orbitP14TargetCoeff 148 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv148 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 148))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 148)) ≃*
      CocycleGroup (orbitP14TargetCocycle 148)
        (orbitP14TargetCocycle_consistent 148) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2] (orbitP14RepresentativeCoeff 148)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_148))

theorem orbitP14_path_endpoint_149 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 1, 1, 2]
      (orbitP14RepresentativeCoeff 149) = orbitP14TargetCoeff 149 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv149 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 149))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 149)) ≃*
      CocycleGroup (orbitP14TargetCocycle 149)
        (orbitP14TargetCocycle_consistent 149) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 1, 1, 2] (orbitP14RepresentativeCoeff 149)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_149))

theorem orbitP14_path_endpoint_150 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 2, 1, 0, 2]
      (orbitP14RepresentativeCoeff 150) = orbitP14TargetCoeff 150 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv150 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 150))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 150)) ≃*
      CocycleGroup (orbitP14TargetCocycle 150)
        (orbitP14TargetCocycle_consistent 150) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 2, 1, 0, 2] (orbitP14RepresentativeCoeff 150)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_150))

theorem orbitP14_path_endpoint_151 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 2, 1, 0, 2]
      (orbitP14RepresentativeCoeff 151) = orbitP14TargetCoeff 151 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv151 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 151))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 151)) ≃*
      CocycleGroup (orbitP14TargetCocycle 151)
        (orbitP14TargetCocycle_consistent 151) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 2, 1, 0, 2] (orbitP14RepresentativeCoeff 151)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_151))

theorem orbitP14_path_endpoint_152 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 152) = orbitP14TargetCoeff 152 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv152 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 152))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 152)) ≃*
      CocycleGroup (orbitP14TargetCocycle 152)
        (orbitP14TargetCocycle_consistent 152) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 152)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_152))

theorem orbitP14_path_endpoint_153 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 2, 1, 1, 0, 1]
      (orbitP14RepresentativeCoeff 153) = orbitP14TargetCoeff 153 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv153 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 153))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 153)) ≃*
      CocycleGroup (orbitP14TargetCocycle 153)
        (orbitP14TargetCocycle_consistent 153) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 2, 1, 1, 0, 1] (orbitP14RepresentativeCoeff 153)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_153))

theorem orbitP14_path_endpoint_154 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 1, 2, 1, 2]
      (orbitP14RepresentativeCoeff 154) = orbitP14TargetCoeff 154 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv154 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 154))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 154)) ≃*
      CocycleGroup (orbitP14TargetCocycle 154)
        (orbitP14TargetCocycle_consistent 154) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 1, 2, 1, 2] (orbitP14RepresentativeCoeff 154)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_154))

theorem orbitP14_path_endpoint_155 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 155) = orbitP14TargetCoeff 155 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv155 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 155))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 155)) ≃*
      CocycleGroup (orbitP14TargetCocycle 155)
        (orbitP14TargetCocycle_consistent 155) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 155)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_155))

theorem orbitP14_path_endpoint_156 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 1, 2, 1, 2, 0]
      (orbitP14RepresentativeCoeff 156) = orbitP14TargetCoeff 156 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv156 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 156))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 156)) ≃*
      CocycleGroup (orbitP14TargetCocycle 156)
        (orbitP14TargetCocycle_consistent 156) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 1, 2, 1, 2, 0] (orbitP14RepresentativeCoeff 156)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_156))

theorem orbitP14_path_endpoint_157 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 157) = orbitP14TargetCoeff 157 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv157 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 157))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 157)) ≃*
      CocycleGroup (orbitP14TargetCocycle 157)
        (orbitP14TargetCocycle_consistent 157) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 157)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_157))

theorem orbitP14_path_endpoint_158 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 158) = orbitP14TargetCoeff 158 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv158 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 158))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 158)) ≃*
      CocycleGroup (orbitP14TargetCocycle 158)
        (orbitP14TargetCocycle_consistent 158) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 158)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_158))

theorem orbitP14_path_endpoint_159 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 0, 1, 0, 2, 0, 1]
      (orbitP14RepresentativeCoeff 159) = orbitP14TargetCoeff 159 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv159 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 159))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 159)) ≃*
      CocycleGroup (orbitP14TargetCocycle 159)
        (orbitP14TargetCocycle_consistent 159) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 0, 1, 0, 2, 0, 1] (orbitP14RepresentativeCoeff 159)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_159))

end Smallgroups.UsefulTheorems.Order32Certificate
