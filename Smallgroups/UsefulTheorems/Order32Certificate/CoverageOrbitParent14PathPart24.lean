/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart23

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 24. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_368 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 0]
      (orbitP14RepresentativeCoeff 368) = orbitP14TargetCoeff 368 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv368 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 368))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 368)) ≃*
      CocycleGroup (orbitP14TargetCocycle 368)
        (orbitP14TargetCocycle_consistent 368) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 0] (orbitP14RepresentativeCoeff 368)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_368))

theorem orbitP14_path_endpoint_369 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 1, 2, 1, 0, 2]
      (orbitP14RepresentativeCoeff 369) = orbitP14TargetCoeff 369 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv369 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 369))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 369)) ≃*
      CocycleGroup (orbitP14TargetCocycle 369)
        (orbitP14TargetCocycle_consistent 369) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 1, 2, 1, 0, 2] (orbitP14RepresentativeCoeff 369)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_369))

theorem orbitP14_path_endpoint_370 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 0, 1]
      (orbitP14RepresentativeCoeff 370) = orbitP14TargetCoeff 370 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv370 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 370))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 370)) ≃*
      CocycleGroup (orbitP14TargetCocycle 370)
        (orbitP14TargetCocycle_consistent 370) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 0, 1] (orbitP14RepresentativeCoeff 370)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_370))

theorem orbitP14_path_endpoint_371 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 371) = orbitP14TargetCoeff 371 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv371 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 371))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 371)) ≃*
      CocycleGroup (orbitP14TargetCocycle 371)
        (orbitP14TargetCocycle_consistent 371) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 371)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_371))

theorem orbitP14_path_endpoint_372 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 0, 2, 1]
      (orbitP14RepresentativeCoeff 372) = orbitP14TargetCoeff 372 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv372 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 372))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 372)) ≃*
      CocycleGroup (orbitP14TargetCocycle 372)
        (orbitP14TargetCocycle_consistent 372) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 0, 2, 1] (orbitP14RepresentativeCoeff 372)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_372))

theorem orbitP14_path_endpoint_373 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 373) = orbitP14TargetCoeff 373 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv373 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 373))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 373)) ≃*
      CocycleGroup (orbitP14TargetCocycle 373)
        (orbitP14TargetCocycle_consistent 373) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 373)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_373))

theorem orbitP14_path_endpoint_374 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 2, 1, 0, 1]
      (orbitP14RepresentativeCoeff 374) = orbitP14TargetCoeff 374 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv374 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 374))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 374)) ≃*
      CocycleGroup (orbitP14TargetCocycle 374)
        (orbitP14TargetCocycle_consistent 374) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 2, 1, 0, 1] (orbitP14RepresentativeCoeff 374)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_374))

theorem orbitP14_path_endpoint_375 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 375) = orbitP14TargetCoeff 375 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv375 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 375))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 375)) ≃*
      CocycleGroup (orbitP14TargetCocycle 375)
        (orbitP14TargetCocycle_consistent 375) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 375)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_375))

theorem orbitP14_path_endpoint_376 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 376) = orbitP14TargetCoeff 376 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv376 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 376))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 376)) ≃*
      CocycleGroup (orbitP14TargetCocycle 376)
        (orbitP14TargetCocycle_consistent 376) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 376)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_376))

theorem orbitP14_path_endpoint_377 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 377) = orbitP14TargetCoeff 377 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv377 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 377))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 377)) ≃*
      CocycleGroup (orbitP14TargetCocycle 377)
        (orbitP14TargetCocycle_consistent 377) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 377)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_377))

theorem orbitP14_path_endpoint_378 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 378) = orbitP14TargetCoeff 378 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv378 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 378))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 378)) ≃*
      CocycleGroup (orbitP14TargetCocycle 378)
        (orbitP14TargetCocycle_consistent 378) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 378)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_378))

theorem orbitP14_path_endpoint_379 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 379) = orbitP14TargetCoeff 379 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv379 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 379))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 379)) ≃*
      CocycleGroup (orbitP14TargetCocycle 379)
        (orbitP14TargetCocycle_consistent 379) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 379)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_379))

theorem orbitP14_path_endpoint_380 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 1, 2, 1, 2]
      (orbitP14RepresentativeCoeff 380) = orbitP14TargetCoeff 380 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv380 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 380))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 380)) ≃*
      CocycleGroup (orbitP14TargetCocycle 380)
        (orbitP14TargetCocycle_consistent 380) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 1, 2, 1, 2] (orbitP14RepresentativeCoeff 380)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_380))

theorem orbitP14_path_endpoint_381 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 381) = orbitP14TargetCoeff 381 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv381 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 381))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 381)) ≃*
      CocycleGroup (orbitP14TargetCocycle 381)
        (orbitP14TargetCocycle_consistent 381) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 2, 0] (orbitP14RepresentativeCoeff 381)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_381))

theorem orbitP14_path_endpoint_382 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 2, 1, 0, 1]
      (orbitP14RepresentativeCoeff 382) = orbitP14TargetCoeff 382 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv382 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 382))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 382)) ≃*
      CocycleGroup (orbitP14TargetCocycle 382)
        (orbitP14TargetCocycle_consistent 382) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 2, 1, 0, 1] (orbitP14RepresentativeCoeff 382)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_382))

theorem orbitP14_path_endpoint_383 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 2, 1]
      (orbitP14RepresentativeCoeff 383) = orbitP14TargetCoeff 383 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv383 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 383))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 383)) ≃*
      CocycleGroup (orbitP14TargetCocycle 383)
        (orbitP14TargetCocycle_consistent 383) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 2, 1] (orbitP14RepresentativeCoeff 383)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_383))

end Smallgroups.UsefulTheorems.Order32Certificate
