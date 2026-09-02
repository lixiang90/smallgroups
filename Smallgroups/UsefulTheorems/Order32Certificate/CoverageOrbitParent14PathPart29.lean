/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart28

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 29. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_448 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 448) = orbitP14TargetCoeff 448 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv448 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 448))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 448)) ≃*
      CocycleGroup (orbitP14TargetCocycle 448)
        (orbitP14TargetCocycle_consistent 448) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 448)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_448))

theorem orbitP14_path_endpoint_449 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 0, 1, 1, 2, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 449) = orbitP14TargetCoeff 449 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv449 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 449))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 449)) ≃*
      CocycleGroup (orbitP14TargetCocycle 449)
        (orbitP14TargetCocycle_consistent 449) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 0, 1, 1, 2, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 449)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_449))

theorem orbitP14_path_endpoint_450 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 0, 1, 1, 0]
      (orbitP14RepresentativeCoeff 450) = orbitP14TargetCoeff 450 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv450 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 450))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 450)) ≃*
      CocycleGroup (orbitP14TargetCocycle 450)
        (orbitP14TargetCocycle_consistent 450) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 0, 1, 1, 0] (orbitP14RepresentativeCoeff 450)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_450))

theorem orbitP14_path_endpoint_451 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2]
      (orbitP14RepresentativeCoeff 451) = orbitP14TargetCoeff 451 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv451 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 451))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 451)) ≃*
      CocycleGroup (orbitP14TargetCocycle 451)
        (orbitP14TargetCocycle_consistent 451) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2] (orbitP14RepresentativeCoeff 451)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_451))

theorem orbitP14_path_endpoint_452 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 0]
      (orbitP14RepresentativeCoeff 452) = orbitP14TargetCoeff 452 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv452 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 452))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 452)) ≃*
      CocycleGroup (orbitP14TargetCocycle 452)
        (orbitP14TargetCocycle_consistent 452) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 0] (orbitP14RepresentativeCoeff 452)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_452))

theorem orbitP14_path_endpoint_453 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 1, 0, 2]
      (orbitP14RepresentativeCoeff 453) = orbitP14TargetCoeff 453 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv453 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 453))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 453)) ≃*
      CocycleGroup (orbitP14TargetCocycle 453)
        (orbitP14TargetCocycle_consistent 453) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 1, 0, 2] (orbitP14RepresentativeCoeff 453)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_453))

theorem orbitP14_path_endpoint_454 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 2, 0, 1, 2, 1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 454) = orbitP14TargetCoeff 454 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv454 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 454))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 454)) ≃*
      CocycleGroup (orbitP14TargetCocycle 454)
        (orbitP14TargetCocycle_consistent 454) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 2, 0, 1, 2, 1, 1, 2, 0] (orbitP14RepresentativeCoeff 454)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_454))

theorem orbitP14_path_endpoint_455 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 0, 1, 0]
      (orbitP14RepresentativeCoeff 455) = orbitP14TargetCoeff 455 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv455 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 455))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 455)) ≃*
      CocycleGroup (orbitP14TargetCocycle 455)
        (orbitP14TargetCocycle_consistent 455) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 0, 1, 0] (orbitP14RepresentativeCoeff 455)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_455))

theorem orbitP14_path_endpoint_456 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 2, 1, 2, 0]
      (orbitP14RepresentativeCoeff 456) = orbitP14TargetCoeff 456 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv456 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 456))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 456)) ≃*
      CocycleGroup (orbitP14TargetCocycle 456)
        (orbitP14TargetCocycle_consistent 456) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 2, 1, 2, 0] (orbitP14RepresentativeCoeff 456)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_456))

theorem orbitP14_path_endpoint_457 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 0, 1, 0, 2]
      (orbitP14RepresentativeCoeff 457) = orbitP14TargetCoeff 457 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv457 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 457))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 457)) ≃*
      CocycleGroup (orbitP14TargetCocycle 457)
        (orbitP14TargetCocycle_consistent 457) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 0, 1, 0, 2] (orbitP14RepresentativeCoeff 457)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_457))

theorem orbitP14_path_endpoint_458 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 1, 0, 2]
      (orbitP14RepresentativeCoeff 458) = orbitP14TargetCoeff 458 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv458 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 458))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 458)) ≃*
      CocycleGroup (orbitP14TargetCocycle 458)
        (orbitP14TargetCocycle_consistent 458) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 1, 0, 2] (orbitP14RepresentativeCoeff 458)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_458))

theorem orbitP14_path_endpoint_459 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 0, 1, 2]
      (orbitP14RepresentativeCoeff 459) = orbitP14TargetCoeff 459 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv459 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 459))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 459)) ≃*
      CocycleGroup (orbitP14TargetCocycle 459)
        (orbitP14TargetCocycle_consistent 459) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 0, 1, 2] (orbitP14RepresentativeCoeff 459)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_459))

theorem orbitP14_path_endpoint_460 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 0, 2]
      (orbitP14RepresentativeCoeff 460) = orbitP14TargetCoeff 460 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv460 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 460))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 460)) ≃*
      CocycleGroup (orbitP14TargetCocycle 460)
        (orbitP14TargetCocycle_consistent 460) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 0, 2] (orbitP14RepresentativeCoeff 460)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_460))

theorem orbitP14_path_endpoint_461 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 1, 1, 2]
      (orbitP14RepresentativeCoeff 461) = orbitP14TargetCoeff 461 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv461 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 461))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 461)) ≃*
      CocycleGroup (orbitP14TargetCocycle 461)
        (orbitP14TargetCocycle_consistent 461) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 1, 1, 2] (orbitP14RepresentativeCoeff 461)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_461))

theorem orbitP14_path_endpoint_462 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 2, 1, 2, 1]
      (orbitP14RepresentativeCoeff 462) = orbitP14TargetCoeff 462 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv462 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 462))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 462)) ≃*
      CocycleGroup (orbitP14TargetCocycle 462)
        (orbitP14TargetCocycle_consistent 462) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 2, 1, 2, 1] (orbitP14RepresentativeCoeff 462)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_462))

theorem orbitP14_path_endpoint_463 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 1, 1, 2]
      (orbitP14RepresentativeCoeff 463) = orbitP14TargetCoeff 463 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv463 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 463))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 463)) ≃*
      CocycleGroup (orbitP14TargetCocycle 463)
        (orbitP14TargetCocycle_consistent 463) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 1, 1, 2] (orbitP14RepresentativeCoeff 463)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_463))

end Smallgroups.UsefulTheorems.Order32Certificate
