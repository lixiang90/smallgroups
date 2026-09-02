/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart17

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 18. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_272 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 1, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 272) = orbitP14TargetCoeff 272 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv272 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 272))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 272)) ≃*
      CocycleGroup (orbitP14TargetCocycle 272)
        (orbitP14TargetCocycle_consistent 272) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 1, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 272)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_272))

theorem orbitP14_path_endpoint_273 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 2, 1, 1, 0]
      (orbitP14RepresentativeCoeff 273) = orbitP14TargetCoeff 273 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv273 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 273))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 273)) ≃*
      CocycleGroup (orbitP14TargetCocycle 273)
        (orbitP14TargetCocycle_consistent 273) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 2, 1, 1, 0] (orbitP14RepresentativeCoeff 273)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_273))

theorem orbitP14_path_endpoint_274 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 0, 2, 0]
      (orbitP14RepresentativeCoeff 274) = orbitP14TargetCoeff 274 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv274 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 274))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 274)) ≃*
      CocycleGroup (orbitP14TargetCocycle 274)
        (orbitP14TargetCocycle_consistent 274) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 0, 2, 0] (orbitP14RepresentativeCoeff 274)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_274))

theorem orbitP14_path_endpoint_275 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0]
      (orbitP14RepresentativeCoeff 275) = orbitP14TargetCoeff 275 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv275 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 275))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 275)) ≃*
      CocycleGroup (orbitP14TargetCocycle 275)
        (orbitP14TargetCocycle_consistent 275) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0] (orbitP14RepresentativeCoeff 275)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_275))

theorem orbitP14_path_endpoint_276 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 0, 1, 1, 2, 0, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 276) = orbitP14TargetCoeff 276 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv276 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 276))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 276)) ≃*
      CocycleGroup (orbitP14TargetCocycle 276)
        (orbitP14TargetCocycle_consistent 276) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 0, 1, 1, 2, 0, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 276)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_276))

theorem orbitP14_path_endpoint_277 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 2, 1, 2, 0, 1, 1]
      (orbitP14RepresentativeCoeff 277) = orbitP14TargetCoeff 277 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv277 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 277))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 277)) ≃*
      CocycleGroup (orbitP14TargetCocycle 277)
        (orbitP14TargetCocycle_consistent 277) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 2, 1, 2, 0, 1, 1] (orbitP14RepresentativeCoeff 277)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_277))

theorem orbitP14_path_endpoint_278 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 1, 0]
      (orbitP14RepresentativeCoeff 278) = orbitP14TargetCoeff 278 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv278 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 278))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 278)) ≃*
      CocycleGroup (orbitP14TargetCocycle 278)
        (orbitP14TargetCocycle_consistent 278) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 1, 0] (orbitP14RepresentativeCoeff 278)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_278))

theorem orbitP14_path_endpoint_279 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 1, 0, 2, 1]
      (orbitP14RepresentativeCoeff 279) = orbitP14TargetCoeff 279 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv279 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 279))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 279)) ≃*
      CocycleGroup (orbitP14TargetCocycle 279)
        (orbitP14TargetCocycle_consistent 279) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 1, 0, 2, 1] (orbitP14RepresentativeCoeff 279)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_279))

theorem orbitP14_path_endpoint_280 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 2, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 280) = orbitP14TargetCoeff 280 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv280 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 280))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 280)) ≃*
      CocycleGroup (orbitP14TargetCocycle 280)
        (orbitP14TargetCocycle_consistent 280) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 2, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 280)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_280))

theorem orbitP14_path_endpoint_281 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 2, 0, 1, 2, 1, 2]
      (orbitP14RepresentativeCoeff 281) = orbitP14TargetCoeff 281 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv281 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 281))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 281)) ≃*
      CocycleGroup (orbitP14TargetCocycle 281)
        (orbitP14TargetCocycle_consistent 281) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 2, 0, 1, 2, 1, 2] (orbitP14RepresentativeCoeff 281)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_281))

theorem orbitP14_path_endpoint_282 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 0]
      (orbitP14RepresentativeCoeff 282) = orbitP14TargetCoeff 282 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv282 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 282))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 282)) ≃*
      CocycleGroup (orbitP14TargetCocycle 282)
        (orbitP14TargetCocycle_consistent 282) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 0] (orbitP14RepresentativeCoeff 282)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_282))

theorem orbitP14_path_endpoint_283 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 1, 0, 1]
      (orbitP14RepresentativeCoeff 283) = orbitP14TargetCoeff 283 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv283 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 283))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 283)) ≃*
      CocycleGroup (orbitP14TargetCocycle 283)
        (orbitP14TargetCocycle_consistent 283) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 1, 0, 1] (orbitP14RepresentativeCoeff 283)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_283))

theorem orbitP14_path_endpoint_284 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 0, 2, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 284) = orbitP14TargetCoeff 284 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv284 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 284))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 284)) ≃*
      CocycleGroup (orbitP14TargetCocycle 284)
        (orbitP14TargetCocycle_consistent 284) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 0, 2, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 284)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_284))

theorem orbitP14_path_endpoint_285 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 285) = orbitP14TargetCoeff 285 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv285 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 285))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 285)) ≃*
      CocycleGroup (orbitP14TargetCocycle 285)
        (orbitP14TargetCocycle_consistent 285) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 285)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_285))

theorem orbitP14_path_endpoint_286 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0]
      (orbitP14RepresentativeCoeff 286) = orbitP14TargetCoeff 286 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv286 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 286))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 286)) ≃*
      CocycleGroup (orbitP14TargetCocycle 286)
        (orbitP14TargetCocycle_consistent 286) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0] (orbitP14RepresentativeCoeff 286)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_286))

theorem orbitP14_path_endpoint_287 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1]
      (orbitP14RepresentativeCoeff 287) = orbitP14TargetCoeff 287 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv287 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 287))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 287)) ≃*
      CocycleGroup (orbitP14TargetCocycle 287)
        (orbitP14TargetCocycle_consistent 287) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1] (orbitP14RepresentativeCoeff 287)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_287))

end Smallgroups.UsefulTheorems.Order32Certificate
