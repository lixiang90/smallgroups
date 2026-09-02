/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart27

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 28. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_432 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 0, 1, 1]
      (orbitP14RepresentativeCoeff 432) = orbitP14TargetCoeff 432 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv432 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 432))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 432)) ≃*
      CocycleGroup (orbitP14TargetCocycle 432)
        (orbitP14TargetCocycle_consistent 432) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 0, 1, 1] (orbitP14RepresentativeCoeff 432)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_432))

theorem orbitP14_path_endpoint_433 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 0, 2, 0, 1, 1]
      (orbitP14RepresentativeCoeff 433) = orbitP14TargetCoeff 433 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv433 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 433))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 433)) ≃*
      CocycleGroup (orbitP14TargetCocycle 433)
        (orbitP14TargetCocycle_consistent 433) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 0, 2, 0, 1, 1] (orbitP14RepresentativeCoeff 433)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_433))

theorem orbitP14_path_endpoint_434 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 1, 2, 0, 1, 1]
      (orbitP14RepresentativeCoeff 434) = orbitP14TargetCoeff 434 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv434 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 434))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 434)) ≃*
      CocycleGroup (orbitP14TargetCocycle 434)
        (orbitP14TargetCocycle_consistent 434) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 1, 2, 0, 1, 1] (orbitP14RepresentativeCoeff 434)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_434))

theorem orbitP14_path_endpoint_435 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 435) = orbitP14TargetCoeff 435 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv435 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 435))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 435)) ≃*
      CocycleGroup (orbitP14TargetCocycle 435)
        (orbitP14TargetCocycle_consistent 435) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2] (orbitP14RepresentativeCoeff 435)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_435))

theorem orbitP14_path_endpoint_436 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 0, 1, 2, 1, 1, 0]
      (orbitP14RepresentativeCoeff 436) = orbitP14TargetCoeff 436 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv436 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 436))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 436)) ≃*
      CocycleGroup (orbitP14TargetCocycle 436)
        (orbitP14TargetCocycle_consistent 436) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 0, 1, 2, 1, 1, 0] (orbitP14RepresentativeCoeff 436)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_436))

theorem orbitP14_path_endpoint_437 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 1, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 437) = orbitP14TargetCoeff 437 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv437 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 437))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 437)) ≃*
      CocycleGroup (orbitP14TargetCocycle 437)
        (orbitP14TargetCocycle_consistent 437) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 1, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 437)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_437))

theorem orbitP14_path_endpoint_438 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 1, 0]
      (orbitP14RepresentativeCoeff 438) = orbitP14TargetCoeff 438 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv438 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 438))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 438)) ≃*
      CocycleGroup (orbitP14TargetCocycle 438)
        (orbitP14TargetCocycle_consistent 438) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 1, 0] (orbitP14RepresentativeCoeff 438)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_438))

theorem orbitP14_path_endpoint_439 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 2, 1, 2]
      (orbitP14RepresentativeCoeff 439) = orbitP14TargetCoeff 439 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv439 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 439))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 439)) ≃*
      CocycleGroup (orbitP14TargetCocycle 439)
        (orbitP14TargetCocycle_consistent 439) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 2, 1, 2] (orbitP14RepresentativeCoeff 439)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_439))

theorem orbitP14_path_endpoint_440 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 1, 2]
      (orbitP14RepresentativeCoeff 440) = orbitP14TargetCoeff 440 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv440 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 440))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 440)) ≃*
      CocycleGroup (orbitP14TargetCocycle 440)
        (orbitP14TargetCocycle_consistent 440) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 1, 2] (orbitP14RepresentativeCoeff 440)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_440))

theorem orbitP14_path_endpoint_441 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 441) = orbitP14TargetCoeff 441 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv441 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 441))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 441)) ≃*
      CocycleGroup (orbitP14TargetCocycle 441)
        (orbitP14TargetCocycle_consistent 441) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 441)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_441))

theorem orbitP14_path_endpoint_442 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 442) = orbitP14TargetCoeff 442 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv442 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 442))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 442)) ≃*
      CocycleGroup (orbitP14TargetCocycle 442)
        (orbitP14TargetCocycle_consistent 442) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 442)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_442))

theorem orbitP14_path_endpoint_443 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 0, 2, 1, 1]
      (orbitP14RepresentativeCoeff 443) = orbitP14TargetCoeff 443 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv443 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 443))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 443)) ≃*
      CocycleGroup (orbitP14TargetCocycle 443)
        (orbitP14TargetCocycle_consistent 443) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 0, 2, 1, 1] (orbitP14RepresentativeCoeff 443)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_443))

theorem orbitP14_path_endpoint_444 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 1, 0]
      (orbitP14RepresentativeCoeff 444) = orbitP14TargetCoeff 444 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv444 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 444))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 444)) ≃*
      CocycleGroup (orbitP14TargetCocycle 444)
        (orbitP14TargetCocycle_consistent 444) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 1, 0] (orbitP14RepresentativeCoeff 444)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_444))

theorem orbitP14_path_endpoint_445 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 1, 2, 1, 0, 2]
      (orbitP14RepresentativeCoeff 445) = orbitP14TargetCoeff 445 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv445 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 445))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 445)) ≃*
      CocycleGroup (orbitP14TargetCocycle 445)
        (orbitP14TargetCocycle_consistent 445) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 1, 2, 1, 0, 2] (orbitP14RepresentativeCoeff 445)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_445))

theorem orbitP14_path_endpoint_446 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 0, 1, 0, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 446) = orbitP14TargetCoeff 446 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv446 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 446))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 446)) ≃*
      CocycleGroup (orbitP14TargetCocycle 446)
        (orbitP14TargetCocycle_consistent 446) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 0, 1, 0, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 446)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_446))

theorem orbitP14_path_endpoint_447 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 447) = orbitP14TargetCoeff 447 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv447 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 447))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 447)) ≃*
      CocycleGroup (orbitP14TargetCocycle 447)
        (orbitP14TargetCocycle_consistent 447) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 447)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_447))

end Smallgroups.UsefulTheorems.Order32Certificate
