/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart26

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 27. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_416 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 0, 2, 0, 1, 1]
      (orbitP14RepresentativeCoeff 416) = orbitP14TargetCoeff 416 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv416 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 416))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 416)) ≃*
      CocycleGroup (orbitP14TargetCocycle 416)
        (orbitP14TargetCocycle_consistent 416) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 0, 2, 0, 1, 1] (orbitP14RepresentativeCoeff 416)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_416))

theorem orbitP14_path_endpoint_417 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 0]
      (orbitP14RepresentativeCoeff 417) = orbitP14TargetCoeff 417 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv417 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 417))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 417)) ≃*
      CocycleGroup (orbitP14TargetCocycle 417)
        (orbitP14TargetCocycle_consistent 417) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 0] (orbitP14RepresentativeCoeff 417)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_417))

theorem orbitP14_path_endpoint_418 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 418) = orbitP14TargetCoeff 418 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv418 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 418))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 418)) ≃*
      CocycleGroup (orbitP14TargetCocycle 418)
        (orbitP14TargetCocycle_consistent 418) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 418)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_418))

theorem orbitP14_path_endpoint_419 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 0, 1, 1, 2]
      (orbitP14RepresentativeCoeff 419) = orbitP14TargetCoeff 419 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv419 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 419))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 419)) ≃*
      CocycleGroup (orbitP14TargetCocycle 419)
        (orbitP14TargetCocycle_consistent 419) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 0, 1, 1, 2] (orbitP14RepresentativeCoeff 419)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_419))

theorem orbitP14_path_endpoint_420 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 420) = orbitP14TargetCoeff 420 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv420 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 420))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 420)) ≃*
      CocycleGroup (orbitP14TargetCocycle 420)
        (orbitP14TargetCocycle_consistent 420) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 420)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_420))

theorem orbitP14_path_endpoint_421 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 421) = orbitP14TargetCoeff 421 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv421 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 421))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 421)) ≃*
      CocycleGroup (orbitP14TargetCocycle 421)
        (orbitP14TargetCocycle_consistent 421) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 421)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_421))

theorem orbitP14_path_endpoint_422 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 0, 1, 0, 2, 1, 0, 2]
      (orbitP14RepresentativeCoeff 422) = orbitP14TargetCoeff 422 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv422 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 422))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 422)) ≃*
      CocycleGroup (orbitP14TargetCocycle 422)
        (orbitP14TargetCocycle_consistent 422) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 0, 1, 0, 2, 1, 0, 2] (orbitP14RepresentativeCoeff 422)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_422))

theorem orbitP14_path_endpoint_423 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 0, 1, 1]
      (orbitP14RepresentativeCoeff 423) = orbitP14TargetCoeff 423 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv423 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 423))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 423)) ≃*
      CocycleGroup (orbitP14TargetCocycle 423)
        (orbitP14TargetCocycle_consistent 423) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 0, 1, 1] (orbitP14RepresentativeCoeff 423)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_423))

theorem orbitP14_path_endpoint_424 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 0, 1, 1]
      (orbitP14RepresentativeCoeff 424) = orbitP14TargetCoeff 424 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv424 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 424))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 424)) ≃*
      CocycleGroup (orbitP14TargetCocycle 424)
        (orbitP14TargetCocycle_consistent 424) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 0, 1, 1] (orbitP14RepresentativeCoeff 424)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_424))

theorem orbitP14_path_endpoint_425 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 1, 2]
      (orbitP14RepresentativeCoeff 425) = orbitP14TargetCoeff 425 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv425 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 425))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 425)) ≃*
      CocycleGroup (orbitP14TargetCocycle 425)
        (orbitP14TargetCocycle_consistent 425) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 1, 2] (orbitP14RepresentativeCoeff 425)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_425))

theorem orbitP14_path_endpoint_426 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 0, 1, 1, 2, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 426) = orbitP14TargetCoeff 426 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv426 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 426))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 426)) ≃*
      CocycleGroup (orbitP14TargetCocycle 426)
        (orbitP14TargetCocycle_consistent 426) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 0, 1, 1, 2, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 426)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_426))

theorem orbitP14_path_endpoint_427 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 2, 0, 1]
      (orbitP14RepresentativeCoeff 427) = orbitP14TargetCoeff 427 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv427 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 427))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 427)) ≃*
      CocycleGroup (orbitP14TargetCocycle 427)
        (orbitP14TargetCocycle_consistent 427) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 2, 0, 1] (orbitP14RepresentativeCoeff 427)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_427))

theorem orbitP14_path_endpoint_428 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 428) = orbitP14TargetCoeff 428 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv428 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 428))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 428)) ≃*
      CocycleGroup (orbitP14TargetCocycle 428)
        (orbitP14TargetCocycle_consistent 428) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 428)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_428))

theorem orbitP14_path_endpoint_429 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 0, 1, 0, 2, 1, 0]
      (orbitP14RepresentativeCoeff 429) = orbitP14TargetCoeff 429 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv429 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 429))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 429)) ≃*
      CocycleGroup (orbitP14TargetCocycle 429)
        (orbitP14TargetCocycle_consistent 429) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 0, 1, 0, 2, 1, 0] (orbitP14RepresentativeCoeff 429)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_429))

theorem orbitP14_path_endpoint_430 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 430) = orbitP14TargetCoeff 430 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv430 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 430))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 430)) ≃*
      CocycleGroup (orbitP14TargetCocycle 430)
        (orbitP14TargetCocycle_consistent 430) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 430)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_430))

theorem orbitP14_path_endpoint_431 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 0, 1, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 431) = orbitP14TargetCoeff 431 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv431 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 431))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 431)) ≃*
      CocycleGroup (orbitP14TargetCocycle 431)
        (orbitP14TargetCocycle_consistent 431) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 0, 1, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 431)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_431))

end Smallgroups.UsefulTheorems.Order32Certificate
