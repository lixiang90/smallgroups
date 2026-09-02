/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart21

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 22. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_336 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 0, 1, 0, 1]
      (orbitP14RepresentativeCoeff 336) = orbitP14TargetCoeff 336 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv336 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 336))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 336)) ≃*
      CocycleGroup (orbitP14TargetCocycle 336)
        (orbitP14TargetCocycle_consistent 336) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 0, 1, 0, 1] (orbitP14RepresentativeCoeff 336)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_336))

theorem orbitP14_path_endpoint_337 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 0, 2, 0, 1, 2, 1, 0, 2]
      (orbitP14RepresentativeCoeff 337) = orbitP14TargetCoeff 337 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv337 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 337))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 337)) ≃*
      CocycleGroup (orbitP14TargetCocycle 337)
        (orbitP14TargetCocycle_consistent 337) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 0, 2, 0, 1, 2, 1, 0, 2] (orbitP14RepresentativeCoeff 337)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_337))

theorem orbitP14_path_endpoint_338 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1]
      (orbitP14RepresentativeCoeff 338) = orbitP14TargetCoeff 338 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv338 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 338))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 338)) ≃*
      CocycleGroup (orbitP14TargetCocycle 338)
        (orbitP14TargetCocycle_consistent 338) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1] (orbitP14RepresentativeCoeff 338)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_338))

theorem orbitP14_path_endpoint_339 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 1, 0, 2, 0]
      (orbitP14RepresentativeCoeff 339) = orbitP14TargetCoeff 339 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv339 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 339))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 339)) ≃*
      CocycleGroup (orbitP14TargetCocycle 339)
        (orbitP14TargetCocycle_consistent 339) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 1, 0, 2, 0] (orbitP14RepresentativeCoeff 339)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_339))

theorem orbitP14_path_endpoint_340 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 0, 1, 1]
      (orbitP14RepresentativeCoeff 340) = orbitP14TargetCoeff 340 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv340 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 340))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 340)) ≃*
      CocycleGroup (orbitP14TargetCocycle 340)
        (orbitP14TargetCocycle_consistent 340) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 0, 1, 1] (orbitP14RepresentativeCoeff 340)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_340))

theorem orbitP14_path_endpoint_341 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 341) = orbitP14TargetCoeff 341 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv341 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 341))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 341)) ≃*
      CocycleGroup (orbitP14TargetCocycle 341)
        (orbitP14TargetCocycle_consistent 341) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 341)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_341))

theorem orbitP14_path_endpoint_342 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 2, 0, 1, 2, 1, 1, 2]
      (orbitP14RepresentativeCoeff 342) = orbitP14TargetCoeff 342 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv342 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 342))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 342)) ≃*
      CocycleGroup (orbitP14TargetCocycle 342)
        (orbitP14TargetCocycle_consistent 342) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 2, 0, 1, 2, 1, 1, 2] (orbitP14RepresentativeCoeff 342)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_342))

theorem orbitP14_path_endpoint_343 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 343) = orbitP14TargetCoeff 343 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv343 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 343))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 343)) ≃*
      CocycleGroup (orbitP14TargetCocycle 343)
        (orbitP14TargetCocycle_consistent 343) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 343)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_343))

theorem orbitP14_path_endpoint_344 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 2, 1, 2]
      (orbitP14RepresentativeCoeff 344) = orbitP14TargetCoeff 344 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv344 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 344))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 344)) ≃*
      CocycleGroup (orbitP14TargetCocycle 344)
        (orbitP14TargetCocycle_consistent 344) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 2, 1, 2] (orbitP14RepresentativeCoeff 344)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_344))

theorem orbitP14_path_endpoint_345 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 1, 1, 0, 2]
      (orbitP14RepresentativeCoeff 345) = orbitP14TargetCoeff 345 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv345 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 345))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 345)) ≃*
      CocycleGroup (orbitP14TargetCocycle 345)
        (orbitP14TargetCocycle_consistent 345) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 1, 1, 0, 2] (orbitP14RepresentativeCoeff 345)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_345))

theorem orbitP14_path_endpoint_346 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 0, 2, 0]
      (orbitP14RepresentativeCoeff 346) = orbitP14TargetCoeff 346 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv346 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 346))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 346)) ≃*
      CocycleGroup (orbitP14TargetCocycle 346)
        (orbitP14TargetCocycle_consistent 346) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 0, 2, 0] (orbitP14RepresentativeCoeff 346)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_346))

theorem orbitP14_path_endpoint_347 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 347) = orbitP14TargetCoeff 347 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv347 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 347))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 347)) ≃*
      CocycleGroup (orbitP14TargetCocycle 347)
        (orbitP14TargetCocycle_consistent 347) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 1, 1, 2, 0] (orbitP14RepresentativeCoeff 347)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_347))

theorem orbitP14_path_endpoint_348 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 1, 0, 2, 0]
      (orbitP14RepresentativeCoeff 348) = orbitP14TargetCoeff 348 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv348 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 348))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 348)) ≃*
      CocycleGroup (orbitP14TargetCocycle 348)
        (orbitP14TargetCocycle_consistent 348) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 1, 0, 2, 0] (orbitP14RepresentativeCoeff 348)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_348))

theorem orbitP14_path_endpoint_349 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 1]
      (orbitP14RepresentativeCoeff 349) = orbitP14TargetCoeff 349 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv349 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 349))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 349)) ≃*
      CocycleGroup (orbitP14TargetCocycle 349)
        (orbitP14TargetCocycle_consistent 349) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 1] (orbitP14RepresentativeCoeff 349)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_349))

theorem orbitP14_path_endpoint_350 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 2, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 350) = orbitP14TargetCoeff 350 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv350 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 350))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 350)) ≃*
      CocycleGroup (orbitP14TargetCocycle 350)
        (orbitP14TargetCocycle_consistent 350) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 2, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 350)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_350))

theorem orbitP14_path_endpoint_351 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 351) = orbitP14TargetCoeff 351 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv351 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 351))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 351)) ≃*
      CocycleGroup (orbitP14TargetCocycle 351)
        (orbitP14TargetCocycle_consistent 351) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 1, 1, 2, 0] (orbitP14RepresentativeCoeff 351)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_351))

end Smallgroups.UsefulTheorems.Order32Certificate
