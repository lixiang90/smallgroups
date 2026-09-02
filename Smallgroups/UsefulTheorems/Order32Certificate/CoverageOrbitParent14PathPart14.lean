/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart13

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 14. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_208 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 0, 1]
      (orbitP14RepresentativeCoeff 208) = orbitP14TargetCoeff 208 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv208 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 208))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 208)) ≃*
      CocycleGroup (orbitP14TargetCocycle 208)
        (orbitP14TargetCocycle_consistent 208) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 0, 1] (orbitP14RepresentativeCoeff 208)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_208))

theorem orbitP14_path_endpoint_209 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 2]
      (orbitP14RepresentativeCoeff 209) = orbitP14TargetCoeff 209 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv209 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 209))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 209)) ≃*
      CocycleGroup (orbitP14TargetCocycle 209)
        (orbitP14TargetCocycle_consistent 209) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 2] (orbitP14RepresentativeCoeff 209)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_209))

theorem orbitP14_path_endpoint_210 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 2, 0, 1, 2, 1, 2, 1]
      (orbitP14RepresentativeCoeff 210) = orbitP14TargetCoeff 210 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv210 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 210))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 210)) ≃*
      CocycleGroup (orbitP14TargetCocycle 210)
        (orbitP14TargetCocycle_consistent 210) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 2, 0, 1, 2, 1, 2, 1] (orbitP14RepresentativeCoeff 210)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_210))

theorem orbitP14_path_endpoint_211 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 0, 2, 1]
      (orbitP14RepresentativeCoeff 211) = orbitP14TargetCoeff 211 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv211 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 211))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 211)) ≃*
      CocycleGroup (orbitP14TargetCocycle 211)
        (orbitP14TargetCocycle_consistent 211) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 0, 2, 1] (orbitP14RepresentativeCoeff 211)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_211))

theorem orbitP14_path_endpoint_212 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 212) = orbitP14TargetCoeff 212 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv212 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 212))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 212)) ≃*
      CocycleGroup (orbitP14TargetCocycle 212)
        (orbitP14TargetCocycle_consistent 212) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 212)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_212))

theorem orbitP14_path_endpoint_213 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 1, 2, 1, 0, 2, 1]
      (orbitP14RepresentativeCoeff 213) = orbitP14TargetCoeff 213 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv213 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 213))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 213)) ≃*
      CocycleGroup (orbitP14TargetCocycle 213)
        (orbitP14TargetCocycle_consistent 213) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 1, 2, 1, 0, 2, 1] (orbitP14RepresentativeCoeff 213)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_213))

theorem orbitP14_path_endpoint_214 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 1, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 214) = orbitP14TargetCoeff 214 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv214 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 214))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 214)) ≃*
      CocycleGroup (orbitP14TargetCocycle 214)
        (orbitP14TargetCocycle_consistent 214) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 1, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 214)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_214))

theorem orbitP14_path_endpoint_215 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 0, 1, 0]
      (orbitP14RepresentativeCoeff 215) = orbitP14TargetCoeff 215 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv215 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 215))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 215)) ≃*
      CocycleGroup (orbitP14TargetCocycle 215)
        (orbitP14TargetCocycle_consistent 215) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 0, 1, 0] (orbitP14RepresentativeCoeff 215)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_215))

theorem orbitP14_path_endpoint_216 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 0, 2, 0, 1, 2, 1, 2]
      (orbitP14RepresentativeCoeff 216) = orbitP14TargetCoeff 216 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv216 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 216))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 216)) ≃*
      CocycleGroup (orbitP14TargetCocycle 216)
        (orbitP14TargetCocycle_consistent 216) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 0, 2, 0, 1, 2, 1, 2] (orbitP14RepresentativeCoeff 216)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_216))

theorem orbitP14_path_endpoint_217 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 0, 2, 0]
      (orbitP14RepresentativeCoeff 217) = orbitP14TargetCoeff 217 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv217 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 217))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 217)) ≃*
      CocycleGroup (orbitP14TargetCocycle 217)
        (orbitP14TargetCocycle_consistent 217) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 0, 2, 0] (orbitP14RepresentativeCoeff 217)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_217))

theorem orbitP14_path_endpoint_218 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 218) = orbitP14TargetCoeff 218 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv218 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 218))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 218)) ≃*
      CocycleGroup (orbitP14TargetCocycle 218)
        (orbitP14TargetCocycle_consistent 218) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 218)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_218))

theorem orbitP14_path_endpoint_219 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1]
      (orbitP14RepresentativeCoeff 219) = orbitP14TargetCoeff 219 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv219 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 219))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 219)) ≃*
      CocycleGroup (orbitP14TargetCocycle 219)
        (orbitP14TargetCocycle_consistent 219) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1] (orbitP14RepresentativeCoeff 219)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_219))

theorem orbitP14_path_endpoint_220 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 0, 1, 0]
      (orbitP14RepresentativeCoeff 220) = orbitP14TargetCoeff 220 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv220 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 220))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 220)) ≃*
      CocycleGroup (orbitP14TargetCocycle 220)
        (orbitP14TargetCocycle_consistent 220) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 0, 1, 0] (orbitP14RepresentativeCoeff 220)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_220))

theorem orbitP14_path_endpoint_221 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 0, 2, 1, 1, 0]
      (orbitP14RepresentativeCoeff 221) = orbitP14TargetCoeff 221 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv221 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 221))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 221)) ≃*
      CocycleGroup (orbitP14TargetCocycle 221)
        (orbitP14TargetCocycle_consistent 221) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 0, 2, 1, 1, 0] (orbitP14RepresentativeCoeff 221)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_221))

theorem orbitP14_path_endpoint_222 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 222) = orbitP14TargetCoeff 222 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv222 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 222))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 222)) ≃*
      CocycleGroup (orbitP14TargetCocycle 222)
        (orbitP14TargetCocycle_consistent 222) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 222)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_222))

theorem orbitP14_path_endpoint_223 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 1, 2, 1, 0, 2, 1]
      (orbitP14RepresentativeCoeff 223) = orbitP14TargetCoeff 223 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv223 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 223))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 223)) ≃*
      CocycleGroup (orbitP14TargetCocycle 223)
        (orbitP14TargetCocycle_consistent 223) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 1, 2, 1, 0, 2, 1] (orbitP14RepresentativeCoeff 223)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_223))

end Smallgroups.UsefulTheorems.Order32Certificate
