/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart20

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 21. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_320 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 1, 0, 1]
      (orbitP14RepresentativeCoeff 320) = orbitP14TargetCoeff 320 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv320 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 320))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 320)) ≃*
      CocycleGroup (orbitP14TargetCocycle 320)
        (orbitP14TargetCocycle_consistent 320) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 1, 0, 1] (orbitP14RepresentativeCoeff 320)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_320))

theorem orbitP14_path_endpoint_321 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 2, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 321) = orbitP14TargetCoeff 321 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv321 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 321))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 321)) ≃*
      CocycleGroup (orbitP14TargetCocycle 321)
        (orbitP14TargetCocycle_consistent 321) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 2, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 321)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_321))

theorem orbitP14_path_endpoint_322 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2]
      (orbitP14RepresentativeCoeff 322) = orbitP14TargetCoeff 322 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv322 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 322))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 322)) ≃*
      CocycleGroup (orbitP14TargetCocycle 322)
        (orbitP14TargetCocycle_consistent 322) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2] (orbitP14RepresentativeCoeff 322)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_322))

theorem orbitP14_path_endpoint_323 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 1, 1]
      (orbitP14RepresentativeCoeff 323) = orbitP14TargetCoeff 323 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv323 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 323))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 323)) ≃*
      CocycleGroup (orbitP14TargetCocycle 323)
        (orbitP14TargetCocycle_consistent 323) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 1, 1] (orbitP14RepresentativeCoeff 323)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_323))

theorem orbitP14_path_endpoint_324 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 324) = orbitP14TargetCoeff 324 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv324 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 324))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 324)) ≃*
      CocycleGroup (orbitP14TargetCocycle 324)
        (orbitP14TargetCocycle_consistent 324) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 1] (orbitP14RepresentativeCoeff 324)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_324))

theorem orbitP14_path_endpoint_325 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 1, 0, 2]
      (orbitP14RepresentativeCoeff 325) = orbitP14TargetCoeff 325 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv325 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 325))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 325)) ≃*
      CocycleGroup (orbitP14TargetCocycle 325)
        (orbitP14TargetCocycle_consistent 325) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 1, 0, 2] (orbitP14RepresentativeCoeff 325)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_325))

theorem orbitP14_path_endpoint_326 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 326) = orbitP14TargetCoeff 326 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv326 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 326))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 326)) ≃*
      CocycleGroup (orbitP14TargetCocycle 326)
        (orbitP14TargetCocycle_consistent 326) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1] (orbitP14RepresentativeCoeff 326)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_326))

theorem orbitP14_path_endpoint_327 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 1, 2, 1, 2, 0, 1, 1]
      (orbitP14RepresentativeCoeff 327) = orbitP14TargetCoeff 327 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv327 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 327))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 327)) ≃*
      CocycleGroup (orbitP14TargetCocycle 327)
        (orbitP14TargetCocycle_consistent 327) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 1, 2, 1, 2, 0, 1, 1] (orbitP14RepresentativeCoeff 327)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_327))

theorem orbitP14_path_endpoint_328 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 1, 0, 2]
      (orbitP14RepresentativeCoeff 328) = orbitP14TargetCoeff 328 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv328 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 328))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 328)) ≃*
      CocycleGroup (orbitP14TargetCocycle 328)
        (orbitP14TargetCocycle_consistent 328) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 1, 0, 2] (orbitP14RepresentativeCoeff 328)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_328))

theorem orbitP14_path_endpoint_329 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 1, 2, 1, 2, 0, 1, 1]
      (orbitP14RepresentativeCoeff 329) = orbitP14TargetCoeff 329 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv329 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 329))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 329)) ≃*
      CocycleGroup (orbitP14TargetCocycle 329)
        (orbitP14TargetCocycle_consistent 329) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 1, 2, 1, 2, 0, 1, 1] (orbitP14RepresentativeCoeff 329)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_329))

theorem orbitP14_path_endpoint_330 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 330) = orbitP14TargetCoeff 330 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv330 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 330))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 330)) ≃*
      CocycleGroup (orbitP14TargetCocycle 330)
        (orbitP14TargetCocycle_consistent 330) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 330)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_330))

theorem orbitP14_path_endpoint_331 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 0]
      (orbitP14RepresentativeCoeff 331) = orbitP14TargetCoeff 331 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv331 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 331))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 331)) ≃*
      CocycleGroup (orbitP14TargetCocycle 331)
        (orbitP14TargetCocycle_consistent 331) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 0] (orbitP14RepresentativeCoeff 331)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_331))

theorem orbitP14_path_endpoint_332 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 1, 2]
      (orbitP14RepresentativeCoeff 332) = orbitP14TargetCoeff 332 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv332 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 332))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 332)) ≃*
      CocycleGroup (orbitP14TargetCocycle 332)
        (orbitP14TargetCocycle_consistent 332) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 1, 2] (orbitP14RepresentativeCoeff 332)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_332))

theorem orbitP14_path_endpoint_333 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2]
      (orbitP14RepresentativeCoeff 333) = orbitP14TargetCoeff 333 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv333 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 333))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 333)) ≃*
      CocycleGroup (orbitP14TargetCocycle 333)
        (orbitP14TargetCocycle_consistent 333) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2] (orbitP14RepresentativeCoeff 333)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_333))

theorem orbitP14_path_endpoint_334 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 2, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 334) = orbitP14TargetCoeff 334 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv334 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 334))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 334)) ≃*
      CocycleGroup (orbitP14TargetCocycle 334)
        (orbitP14TargetCocycle_consistent 334) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 2, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 334)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_334))

theorem orbitP14_path_endpoint_335 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 1, 1, 2]
      (orbitP14RepresentativeCoeff 335) = orbitP14TargetCoeff 335 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv335 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 335))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 335)) ≃*
      CocycleGroup (orbitP14TargetCocycle 335)
        (orbitP14TargetCocycle_consistent 335) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 1, 1, 2] (orbitP14RepresentativeCoeff 335)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_335))

end Smallgroups.UsefulTheorems.Order32Certificate
