/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart36

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 37. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_576 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2]
      (orbitP14RepresentativeCoeff 576) = orbitP14TargetCoeff 576 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv576 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 576))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 576)) ≃*
      CocycleGroup (orbitP14TargetCocycle 576)
        (orbitP14TargetCocycle_consistent 576) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2] (orbitP14RepresentativeCoeff 576)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_576))

theorem orbitP14_path_endpoint_577 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 2]
      (orbitP14RepresentativeCoeff 577) = orbitP14TargetCoeff 577 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv577 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 577))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 577)) ≃*
      CocycleGroup (orbitP14TargetCocycle 577)
        (orbitP14TargetCocycle_consistent 577) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 2] (orbitP14RepresentativeCoeff 577)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_577))

theorem orbitP14_path_endpoint_578 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 2]
      (orbitP14RepresentativeCoeff 578) = orbitP14TargetCoeff 578 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv578 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 578))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 578)) ≃*
      CocycleGroup (orbitP14TargetCocycle 578)
        (orbitP14TargetCocycle_consistent 578) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 2] (orbitP14RepresentativeCoeff 578)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_578))

theorem orbitP14_path_endpoint_579 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 579) = orbitP14TargetCoeff 579 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv579 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 579))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 579)) ≃*
      CocycleGroup (orbitP14TargetCocycle 579)
        (orbitP14TargetCocycle_consistent 579) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 2, 0] (orbitP14RepresentativeCoeff 579)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_579))

theorem orbitP14_path_endpoint_580 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 0]
      (orbitP14RepresentativeCoeff 580) = orbitP14TargetCoeff 580 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv580 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 580))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 580)) ≃*
      CocycleGroup (orbitP14TargetCocycle 580)
        (orbitP14TargetCocycle_consistent 580) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 0] (orbitP14RepresentativeCoeff 580)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_580))

theorem orbitP14_path_endpoint_581 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 0, 1, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 581) = orbitP14TargetCoeff 581 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv581 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 581))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 581)) ≃*
      CocycleGroup (orbitP14TargetCocycle 581)
        (orbitP14TargetCocycle_consistent 581) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 0, 1, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 581)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_581))

theorem orbitP14_path_endpoint_582 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 2, 1, 0, 1]
      (orbitP14RepresentativeCoeff 582) = orbitP14TargetCoeff 582 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv582 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 582))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 582)) ≃*
      CocycleGroup (orbitP14TargetCocycle 582)
        (orbitP14TargetCocycle_consistent 582) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 2, 1, 0, 1] (orbitP14RepresentativeCoeff 582)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_582))

theorem orbitP14_path_endpoint_583 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 0, 1, 2]
      (orbitP14RepresentativeCoeff 583) = orbitP14TargetCoeff 583 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv583 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 583))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 583)) ≃*
      CocycleGroup (orbitP14TargetCocycle 583)
        (orbitP14TargetCocycle_consistent 583) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 0, 1, 2] (orbitP14RepresentativeCoeff 583)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_583))

theorem orbitP14_path_endpoint_584 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 584) = orbitP14TargetCoeff 584 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv584 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 584))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 584)) ≃*
      CocycleGroup (orbitP14TargetCocycle 584)
        (orbitP14TargetCocycle_consistent 584) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 0] (orbitP14RepresentativeCoeff 584)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_584))

theorem orbitP14_path_endpoint_585 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 0, 1, 2]
      (orbitP14RepresentativeCoeff 585) = orbitP14TargetCoeff 585 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv585 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 585))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 585)) ≃*
      CocycleGroup (orbitP14TargetCocycle 585)
        (orbitP14TargetCocycle_consistent 585) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 0, 1, 2] (orbitP14RepresentativeCoeff 585)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_585))

theorem orbitP14_path_endpoint_586 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 586) = orbitP14TargetCoeff 586 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv586 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 586))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 586)) ≃*
      CocycleGroup (orbitP14TargetCocycle 586)
        (orbitP14TargetCocycle_consistent 586) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 586)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_586))

theorem orbitP14_path_endpoint_587 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 587) = orbitP14TargetCoeff 587 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv587 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 587))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 587)) ≃*
      CocycleGroup (orbitP14TargetCocycle 587)
        (orbitP14TargetCocycle_consistent 587) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 587)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_587))

theorem orbitP14_path_endpoint_588 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 588) = orbitP14TargetCoeff 588 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv588 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 588))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 588)) ≃*
      CocycleGroup (orbitP14TargetCocycle 588)
        (orbitP14TargetCocycle_consistent 588) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 588)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_588))

theorem orbitP14_path_endpoint_589 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 1, 2, 1, 2]
      (orbitP14RepresentativeCoeff 589) = orbitP14TargetCoeff 589 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv589 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 589))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 589)) ≃*
      CocycleGroup (orbitP14TargetCocycle 589)
        (orbitP14TargetCocycle_consistent 589) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 1, 2, 1, 2] (orbitP14RepresentativeCoeff 589)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_589))

theorem orbitP14_path_endpoint_590 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 0, 1, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 590) = orbitP14TargetCoeff 590 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv590 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 590))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 590)) ≃*
      CocycleGroup (orbitP14TargetCocycle 590)
        (orbitP14TargetCocycle_consistent 590) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 0, 1, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 590)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_590))

theorem orbitP14_path_endpoint_591 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 1, 2]
      (orbitP14RepresentativeCoeff 591) = orbitP14TargetCoeff 591 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv591 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 591))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 591)) ≃*
      CocycleGroup (orbitP14TargetCocycle 591)
        (orbitP14TargetCocycle_consistent 591) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 1, 2] (orbitP14RepresentativeCoeff 591)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_591))

end Smallgroups.UsefulTheorems.Order32Certificate
