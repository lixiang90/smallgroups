/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart16

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 17. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_256 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 256) = orbitP14TargetCoeff 256 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv256 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 256))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 256)) ≃*
      CocycleGroup (orbitP14TargetCocycle 256)
        (orbitP14TargetCocycle_consistent 256) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 1] (orbitP14RepresentativeCoeff 256)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_256))

theorem orbitP14_path_endpoint_257 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 0, 2, 1, 0, 2]
      (orbitP14RepresentativeCoeff 257) = orbitP14TargetCoeff 257 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv257 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 257))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 257)) ≃*
      CocycleGroup (orbitP14TargetCocycle 257)
        (orbitP14TargetCocycle_consistent 257) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 0, 2, 1, 0, 2] (orbitP14RepresentativeCoeff 257)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_257))

theorem orbitP14_path_endpoint_258 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 1]
      (orbitP14RepresentativeCoeff 258) = orbitP14TargetCoeff 258 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv258 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 258))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 258)) ≃*
      CocycleGroup (orbitP14TargetCocycle 258)
        (orbitP14TargetCocycle_consistent 258) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 1] (orbitP14RepresentativeCoeff 258)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_258))

theorem orbitP14_path_endpoint_259 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0]
      (orbitP14RepresentativeCoeff 259) = orbitP14TargetCoeff 259 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv259 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 259))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 259)) ≃*
      CocycleGroup (orbitP14TargetCocycle 259)
        (orbitP14TargetCocycle_consistent 259) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0] (orbitP14RepresentativeCoeff 259)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_259))

theorem orbitP14_path_endpoint_260 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 260) = orbitP14TargetCoeff 260 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv260 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 260))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 260)) ≃*
      CocycleGroup (orbitP14TargetCocycle 260)
        (orbitP14TargetCocycle_consistent 260) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 0] (orbitP14RepresentativeCoeff 260)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_260))

theorem orbitP14_path_endpoint_261 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2]
      (orbitP14RepresentativeCoeff 261) = orbitP14TargetCoeff 261 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv261 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 261))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 261)) ≃*
      CocycleGroup (orbitP14TargetCocycle 261)
        (orbitP14TargetCocycle_consistent 261) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2] (orbitP14RepresentativeCoeff 261)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_261))

theorem orbitP14_path_endpoint_262 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 0, 1]
      (orbitP14RepresentativeCoeff 262) = orbitP14TargetCoeff 262 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv262 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 262))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 262)) ≃*
      CocycleGroup (orbitP14TargetCocycle 262)
        (orbitP14TargetCocycle_consistent 262) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 0, 1] (orbitP14RepresentativeCoeff 262)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_262))

theorem orbitP14_path_endpoint_263 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2]
      (orbitP14RepresentativeCoeff 263) = orbitP14TargetCoeff 263 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv263 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 263))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 263)) ≃*
      CocycleGroup (orbitP14TargetCocycle 263)
        (orbitP14TargetCocycle_consistent 263) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2] (orbitP14RepresentativeCoeff 263)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_263))

theorem orbitP14_path_endpoint_264 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2]
      (orbitP14RepresentativeCoeff 264) = orbitP14TargetCoeff 264 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv264 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 264))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 264)) ≃*
      CocycleGroup (orbitP14TargetCocycle 264)
        (orbitP14TargetCocycle_consistent 264) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2] (orbitP14RepresentativeCoeff 264)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_264))

theorem orbitP14_path_endpoint_265 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2]
      (orbitP14RepresentativeCoeff 265) = orbitP14TargetCoeff 265 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv265 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 265))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 265)) ≃*
      CocycleGroup (orbitP14TargetCocycle 265)
        (orbitP14TargetCocycle_consistent 265) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2] (orbitP14RepresentativeCoeff 265)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_265))

theorem orbitP14_path_endpoint_266 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 1, 1, 2]
      (orbitP14RepresentativeCoeff 266) = orbitP14TargetCoeff 266 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv266 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 266))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 266)) ≃*
      CocycleGroup (orbitP14TargetCocycle 266)
        (orbitP14TargetCocycle_consistent 266) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 1, 1, 2] (orbitP14RepresentativeCoeff 266)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_266))

theorem orbitP14_path_endpoint_267 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 0, 1, 0]
      (orbitP14RepresentativeCoeff 267) = orbitP14TargetCoeff 267 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv267 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 267))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 267)) ≃*
      CocycleGroup (orbitP14TargetCocycle 267)
        (orbitP14TargetCocycle_consistent 267) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 0, 1, 0] (orbitP14RepresentativeCoeff 267)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_267))

theorem orbitP14_path_endpoint_268 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 0, 2, 1, 2]
      (orbitP14RepresentativeCoeff 268) = orbitP14TargetCoeff 268 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv268 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 268))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 268)) ≃*
      CocycleGroup (orbitP14TargetCocycle 268)
        (orbitP14TargetCocycle_consistent 268) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 0, 2, 1, 2] (orbitP14RepresentativeCoeff 268)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_268))

theorem orbitP14_path_endpoint_269 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 269) = orbitP14TargetCoeff 269 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv269 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 269))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 269)) ≃*
      CocycleGroup (orbitP14TargetCocycle 269)
        (orbitP14TargetCocycle_consistent 269) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 269)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_269))

theorem orbitP14_path_endpoint_270 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0]
      (orbitP14RepresentativeCoeff 270) = orbitP14TargetCoeff 270 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv270 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 270))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 270)) ≃*
      CocycleGroup (orbitP14TargetCocycle 270)
        (orbitP14TargetCocycle_consistent 270) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0] (orbitP14RepresentativeCoeff 270)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_270))

theorem orbitP14_path_endpoint_271 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 0, 2, 1]
      (orbitP14RepresentativeCoeff 271) = orbitP14TargetCoeff 271 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv271 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 271))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 271)) ≃*
      CocycleGroup (orbitP14TargetCocycle 271)
        (orbitP14TargetCocycle_consistent 271) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 0, 2, 1] (orbitP14RepresentativeCoeff 271)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_271))

end Smallgroups.UsefulTheorems.Order32Certificate
