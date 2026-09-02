/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart24

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 25. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_384 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 0, 1]
      (orbitP14RepresentativeCoeff 384) = orbitP14TargetCoeff 384 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv384 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 384))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 384)) ≃*
      CocycleGroup (orbitP14TargetCocycle 384)
        (orbitP14TargetCocycle_consistent 384) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 0, 1] (orbitP14RepresentativeCoeff 384)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_384))

theorem orbitP14_path_endpoint_385 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 1, 1]
      (orbitP14RepresentativeCoeff 385) = orbitP14TargetCoeff 385 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv385 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 385))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 385)) ≃*
      CocycleGroup (orbitP14TargetCocycle 385)
        (orbitP14TargetCocycle_consistent 385) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 1, 1] (orbitP14RepresentativeCoeff 385)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_385))

theorem orbitP14_path_endpoint_386 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 0, 1, 0, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 386) = orbitP14TargetCoeff 386 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv386 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 386))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 386)) ≃*
      CocycleGroup (orbitP14TargetCocycle 386)
        (orbitP14TargetCocycle_consistent 386) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 0, 1, 0, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 386)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_386))

theorem orbitP14_path_endpoint_387 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 387) = orbitP14TargetCoeff 387 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv387 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 387))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 387)) ≃*
      CocycleGroup (orbitP14TargetCocycle 387)
        (orbitP14TargetCocycle_consistent 387) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 387)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_387))

theorem orbitP14_path_endpoint_388 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 2]
      (orbitP14RepresentativeCoeff 388) = orbitP14TargetCoeff 388 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv388 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 388))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 388)) ≃*
      CocycleGroup (orbitP14TargetCocycle 388)
        (orbitP14TargetCocycle_consistent 388) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 2] (orbitP14RepresentativeCoeff 388)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_388))

theorem orbitP14_path_endpoint_389 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 389) = orbitP14TargetCoeff 389 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv389 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 389))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 389)) ≃*
      CocycleGroup (orbitP14TargetCocycle 389)
        (orbitP14TargetCocycle_consistent 389) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 389)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_389))

theorem orbitP14_path_endpoint_390 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 0, 1, 1, 1]
      (orbitP14RepresentativeCoeff 390) = orbitP14TargetCoeff 390 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv390 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 390))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 390)) ≃*
      CocycleGroup (orbitP14TargetCocycle 390)
        (orbitP14TargetCocycle_consistent 390) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 0, 1, 1, 1] (orbitP14RepresentativeCoeff 390)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_390))

theorem orbitP14_path_endpoint_391 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 1, 0, 1, 2]
      (orbitP14RepresentativeCoeff 391) = orbitP14TargetCoeff 391 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv391 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 391))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 391)) ≃*
      CocycleGroup (orbitP14TargetCocycle 391)
        (orbitP14TargetCocycle_consistent 391) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 1, 0, 1, 2] (orbitP14RepresentativeCoeff 391)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_391))

theorem orbitP14_path_endpoint_392 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 392) = orbitP14TargetCoeff 392 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv392 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 392))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 392)) ≃*
      CocycleGroup (orbitP14TargetCocycle 392)
        (orbitP14TargetCocycle_consistent 392) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 0, 1, 2] (orbitP14RepresentativeCoeff 392)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_392))

theorem orbitP14_path_endpoint_393 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 0, 2]
      (orbitP14RepresentativeCoeff 393) = orbitP14TargetCoeff 393 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv393 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 393))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 393)) ≃*
      CocycleGroup (orbitP14TargetCocycle 393)
        (orbitP14TargetCocycle_consistent 393) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 0, 2] (orbitP14RepresentativeCoeff 393)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_393))

theorem orbitP14_path_endpoint_394 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 394) = orbitP14TargetCoeff 394 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv394 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 394))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 394)) ≃*
      CocycleGroup (orbitP14TargetCocycle 394)
        (orbitP14TargetCocycle_consistent 394) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 394)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_394))

theorem orbitP14_path_endpoint_395 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 0, 2]
      (orbitP14RepresentativeCoeff 395) = orbitP14TargetCoeff 395 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv395 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 395))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 395)) ≃*
      CocycleGroup (orbitP14TargetCocycle 395)
        (orbitP14TargetCocycle_consistent 395) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 0, 2] (orbitP14RepresentativeCoeff 395)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_395))

theorem orbitP14_path_endpoint_396 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0]
      (orbitP14RepresentativeCoeff 396) = orbitP14TargetCoeff 396 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv396 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 396))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 396)) ≃*
      CocycleGroup (orbitP14TargetCocycle 396)
        (orbitP14TargetCocycle_consistent 396) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0] (orbitP14RepresentativeCoeff 396)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_396))

theorem orbitP14_path_endpoint_397 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 0]
      (orbitP14RepresentativeCoeff 397) = orbitP14TargetCoeff 397 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv397 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 397))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 397)) ≃*
      CocycleGroup (orbitP14TargetCocycle 397)
        (orbitP14TargetCocycle_consistent 397) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 0] (orbitP14RepresentativeCoeff 397)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_397))

theorem orbitP14_path_endpoint_398 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2]
      (orbitP14RepresentativeCoeff 398) = orbitP14TargetCoeff 398 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv398 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 398))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 398)) ≃*
      CocycleGroup (orbitP14TargetCocycle 398)
        (orbitP14TargetCocycle_consistent 398) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2] (orbitP14RepresentativeCoeff 398)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_398))

theorem orbitP14_path_endpoint_399 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 0, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 399) = orbitP14TargetCoeff 399 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv399 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 399))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 399)) ≃*
      CocycleGroup (orbitP14TargetCocycle 399)
        (orbitP14TargetCocycle_consistent 399) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 0, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 399)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_399))

end Smallgroups.UsefulTheorems.Order32Certificate
