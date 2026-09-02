/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart32

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 33. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_512 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2]
      (orbitP14RepresentativeCoeff 512) = orbitP14TargetCoeff 512 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv512 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 512))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 512)) ≃*
      CocycleGroup (orbitP14TargetCocycle 512)
        (orbitP14TargetCocycle_consistent 512) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2] (orbitP14RepresentativeCoeff 512)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_512))

theorem orbitP14_path_endpoint_513 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1]
      (orbitP14RepresentativeCoeff 513) = orbitP14TargetCoeff 513 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv513 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 513))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 513)) ≃*
      CocycleGroup (orbitP14TargetCocycle 513)
        (orbitP14TargetCocycle_consistent 513) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1] (orbitP14RepresentativeCoeff 513)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_513))

theorem orbitP14_path_endpoint_514 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 1, 0, 2, 0]
      (orbitP14RepresentativeCoeff 514) = orbitP14TargetCoeff 514 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv514 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 514))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 514)) ≃*
      CocycleGroup (orbitP14TargetCocycle 514)
        (orbitP14TargetCocycle_consistent 514) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 1, 0, 2, 0] (orbitP14RepresentativeCoeff 514)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_514))

theorem orbitP14_path_endpoint_515 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0]
      (orbitP14RepresentativeCoeff 515) = orbitP14TargetCoeff 515 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv515 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 515))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 515)) ≃*
      CocycleGroup (orbitP14TargetCocycle 515)
        (orbitP14TargetCocycle_consistent 515) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0] (orbitP14RepresentativeCoeff 515)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_515))

theorem orbitP14_path_endpoint_516 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 1, 0, 2]
      (orbitP14RepresentativeCoeff 516) = orbitP14TargetCoeff 516 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv516 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 516))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 516)) ≃*
      CocycleGroup (orbitP14TargetCocycle 516)
        (orbitP14TargetCocycle_consistent 516) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 1, 0, 2] (orbitP14RepresentativeCoeff 516)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_516))

theorem orbitP14_path_endpoint_517 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2]
      (orbitP14RepresentativeCoeff 517) = orbitP14TargetCoeff 517 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv517 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 517))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 517)) ≃*
      CocycleGroup (orbitP14TargetCocycle 517)
        (orbitP14TargetCocycle_consistent 517) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2] (orbitP14RepresentativeCoeff 517)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_517))

theorem orbitP14_path_endpoint_518 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 2, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 518) = orbitP14TargetCoeff 518 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv518 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 518))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 518)) ≃*
      CocycleGroup (orbitP14TargetCocycle 518)
        (orbitP14TargetCocycle_consistent 518) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 2, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 518)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_518))

theorem orbitP14_path_endpoint_519 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 2, 1, 2, 1, 1, 0, 1]
      (orbitP14RepresentativeCoeff 519) = orbitP14TargetCoeff 519 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv519 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 519))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 519)) ≃*
      CocycleGroup (orbitP14TargetCocycle 519)
        (orbitP14TargetCocycle_consistent 519) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 2, 1, 2, 1, 1, 0, 1] (orbitP14RepresentativeCoeff 519)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_519))

theorem orbitP14_path_endpoint_520 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 0, 1, 2]
      (orbitP14RepresentativeCoeff 520) = orbitP14TargetCoeff 520 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv520 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 520))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 520)) ≃*
      CocycleGroup (orbitP14TargetCocycle 520)
        (orbitP14TargetCocycle_consistent 520) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 0, 1, 2] (orbitP14RepresentativeCoeff 520)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_520))

theorem orbitP14_path_endpoint_521 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2]
      (orbitP14RepresentativeCoeff 521) = orbitP14TargetCoeff 521 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv521 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 521))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 521)) ≃*
      CocycleGroup (orbitP14TargetCocycle 521)
        (orbitP14TargetCocycle_consistent 521) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2] (orbitP14RepresentativeCoeff 521)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_521))

theorem orbitP14_path_endpoint_522 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 2]
      (orbitP14RepresentativeCoeff 522) = orbitP14TargetCoeff 522 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv522 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 522))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 522)) ≃*
      CocycleGroup (orbitP14TargetCocycle 522)
        (orbitP14TargetCocycle_consistent 522) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 2] (orbitP14RepresentativeCoeff 522)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_522))

theorem orbitP14_path_endpoint_523 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 0, 1, 2]
      (orbitP14RepresentativeCoeff 523) = orbitP14TargetCoeff 523 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv523 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 523))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 523)) ≃*
      CocycleGroup (orbitP14TargetCocycle 523)
        (orbitP14TargetCocycle_consistent 523) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 0, 1, 2] (orbitP14RepresentativeCoeff 523)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_523))

theorem orbitP14_path_endpoint_524 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 2, 0]
      (orbitP14RepresentativeCoeff 524) = orbitP14TargetCoeff 524 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv524 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 524))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 524)) ≃*
      CocycleGroup (orbitP14TargetCocycle 524)
        (orbitP14TargetCocycle_consistent 524) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 2, 0] (orbitP14RepresentativeCoeff 524)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_524))

theorem orbitP14_path_endpoint_525 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 525) = orbitP14TargetCoeff 525 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv525 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 525))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 525)) ≃*
      CocycleGroup (orbitP14TargetCocycle 525)
        (orbitP14TargetCocycle_consistent 525) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 525)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_525))

theorem orbitP14_path_endpoint_526 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 0, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 526) = orbitP14TargetCoeff 526 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv526 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 526))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 526)) ≃*
      CocycleGroup (orbitP14TargetCocycle 526)
        (orbitP14TargetCocycle_consistent 526) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 0, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 526)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_526))

theorem orbitP14_path_endpoint_527 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 0, 1, 2, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 527) = orbitP14TargetCoeff 527 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv527 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 527))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 527)) ≃*
      CocycleGroup (orbitP14TargetCocycle 527)
        (orbitP14TargetCocycle_consistent 527) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 0, 1, 2, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 527)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_527))

end Smallgroups.UsefulTheorems.Order32Certificate
