/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart10

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 11. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_160 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0]
      (orbitP14RepresentativeCoeff 160) = orbitP14TargetCoeff 160 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv160 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 160))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 160)) ≃*
      CocycleGroup (orbitP14TargetCocycle 160)
        (orbitP14TargetCocycle_consistent 160) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0] (orbitP14RepresentativeCoeff 160)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_160))

theorem orbitP14_path_endpoint_161 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 0, 2]
      (orbitP14RepresentativeCoeff 161) = orbitP14TargetCoeff 161 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv161 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 161))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 161)) ≃*
      CocycleGroup (orbitP14TargetCocycle 161)
        (orbitP14TargetCocycle_consistent 161) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 0, 2] (orbitP14RepresentativeCoeff 161)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_161))

theorem orbitP14_path_endpoint_162 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 0, 2]
      (orbitP14RepresentativeCoeff 162) = orbitP14TargetCoeff 162 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv162 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 162))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 162)) ≃*
      CocycleGroup (orbitP14TargetCocycle 162)
        (orbitP14TargetCocycle_consistent 162) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 0, 2] (orbitP14RepresentativeCoeff 162)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_162))

theorem orbitP14_path_endpoint_163 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2]
      (orbitP14RepresentativeCoeff 163) = orbitP14TargetCoeff 163 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv163 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 163))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 163)) ≃*
      CocycleGroup (orbitP14TargetCocycle 163)
        (orbitP14TargetCocycle_consistent 163) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2] (orbitP14RepresentativeCoeff 163)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_163))

theorem orbitP14_path_endpoint_164 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 1, 0]
      (orbitP14RepresentativeCoeff 164) = orbitP14TargetCoeff 164 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv164 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 164))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 164)) ≃*
      CocycleGroup (orbitP14TargetCocycle 164)
        (orbitP14TargetCocycle_consistent 164) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 1, 0] (orbitP14RepresentativeCoeff 164)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_164))

theorem orbitP14_path_endpoint_165 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 1, 1, 2]
      (orbitP14RepresentativeCoeff 165) = orbitP14TargetCoeff 165 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv165 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 165))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 165)) ≃*
      CocycleGroup (orbitP14TargetCocycle 165)
        (orbitP14TargetCocycle_consistent 165) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 1, 1, 2] (orbitP14RepresentativeCoeff 165)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_165))

theorem orbitP14_path_endpoint_166 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 0]
      (orbitP14RepresentativeCoeff 166) = orbitP14TargetCoeff 166 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv166 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 166))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 166)) ≃*
      CocycleGroup (orbitP14TargetCocycle 166)
        (orbitP14TargetCocycle_consistent 166) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 0] (orbitP14RepresentativeCoeff 166)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_166))

theorem orbitP14_path_endpoint_167 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 0, 1]
      (orbitP14RepresentativeCoeff 167) = orbitP14TargetCoeff 167 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv167 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 167))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 167)) ≃*
      CocycleGroup (orbitP14TargetCocycle 167)
        (orbitP14TargetCocycle_consistent 167) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 0, 1] (orbitP14RepresentativeCoeff 167)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_167))

theorem orbitP14_path_endpoint_168 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 1, 0, 1]
      (orbitP14RepresentativeCoeff 168) = orbitP14TargetCoeff 168 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv168 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 168))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 168)) ≃*
      CocycleGroup (orbitP14TargetCocycle 168)
        (orbitP14TargetCocycle_consistent 168) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 1, 0, 1] (orbitP14RepresentativeCoeff 168)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_168))

theorem orbitP14_path_endpoint_169 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 169) = orbitP14TargetCoeff 169 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv169 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 169))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 169)) ≃*
      CocycleGroup (orbitP14TargetCocycle 169)
        (orbitP14TargetCocycle_consistent 169) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 169)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_169))

theorem orbitP14_path_endpoint_170 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0]
      (orbitP14RepresentativeCoeff 170) = orbitP14TargetCoeff 170 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv170 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 170))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 170)) ≃*
      CocycleGroup (orbitP14TargetCocycle 170)
        (orbitP14TargetCocycle_consistent 170) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0] (orbitP14RepresentativeCoeff 170)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_170))

theorem orbitP14_path_endpoint_171 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 1, 0, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 171) = orbitP14TargetCoeff 171 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv171 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 171))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 171)) ≃*
      CocycleGroup (orbitP14TargetCocycle 171)
        (orbitP14TargetCocycle_consistent 171) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 1, 0, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 171)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_171))

theorem orbitP14_path_endpoint_172 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 1, 0, 1]
      (orbitP14RepresentativeCoeff 172) = orbitP14TargetCoeff 172 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv172 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 172))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 172)) ≃*
      CocycleGroup (orbitP14TargetCocycle 172)
        (orbitP14TargetCocycle_consistent 172) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 1, 0, 1] (orbitP14RepresentativeCoeff 172)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_172))

theorem orbitP14_path_endpoint_173 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 0, 1, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 173) = orbitP14TargetCoeff 173 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv173 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 173))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 173)) ≃*
      CocycleGroup (orbitP14TargetCocycle 173)
        (orbitP14TargetCocycle_consistent 173) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 0, 1, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 173)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_173))

theorem orbitP14_path_endpoint_174 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 1, 2, 1, 0, 2]
      (orbitP14RepresentativeCoeff 174) = orbitP14TargetCoeff 174 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv174 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 174))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 174)) ≃*
      CocycleGroup (orbitP14TargetCocycle 174)
        (orbitP14TargetCocycle_consistent 174) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 1, 2, 1, 0, 2] (orbitP14RepresentativeCoeff 174)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_174))

theorem orbitP14_path_endpoint_175 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 0]
      (orbitP14RepresentativeCoeff 175) = orbitP14TargetCoeff 175 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv175 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 175))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 175)) ≃*
      CocycleGroup (orbitP14TargetCocycle 175)
        (orbitP14TargetCocycle_consistent 175) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 0] (orbitP14RepresentativeCoeff 175)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_175))

end Smallgroups.UsefulTheorems.Order32Certificate
