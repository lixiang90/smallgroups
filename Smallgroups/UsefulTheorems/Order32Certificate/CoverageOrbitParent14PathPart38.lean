/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart37

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 38. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_592 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2]
      (orbitP14RepresentativeCoeff 592) = orbitP14TargetCoeff 592 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv592 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 592))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 592)) ≃*
      CocycleGroup (orbitP14TargetCocycle 592)
        (orbitP14TargetCocycle_consistent 592) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2] (orbitP14RepresentativeCoeff 592)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_592))

theorem orbitP14_path_endpoint_593 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 0, 1, 0, 1]
      (orbitP14RepresentativeCoeff 593) = orbitP14TargetCoeff 593 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv593 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 593))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 593)) ≃*
      CocycleGroup (orbitP14TargetCocycle 593)
        (orbitP14TargetCocycle_consistent 593) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 0, 1, 0, 1] (orbitP14RepresentativeCoeff 593)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_593))

theorem orbitP14_path_endpoint_594 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 594) = orbitP14TargetCoeff 594 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv594 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 594))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 594)) ≃*
      CocycleGroup (orbitP14TargetCocycle 594)
        (orbitP14TargetCocycle_consistent 594) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 594)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_594))

theorem orbitP14_path_endpoint_595 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1]
      (orbitP14RepresentativeCoeff 595) = orbitP14TargetCoeff 595 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv595 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 595))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 595)) ≃*
      CocycleGroup (orbitP14TargetCocycle 595)
        (orbitP14TargetCocycle_consistent 595) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1] (orbitP14RepresentativeCoeff 595)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_595))

theorem orbitP14_path_endpoint_596 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 596) = orbitP14TargetCoeff 596 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv596 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 596))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 596)) ≃*
      CocycleGroup (orbitP14TargetCocycle 596)
        (orbitP14TargetCocycle_consistent 596) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 596)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_596))

theorem orbitP14_path_endpoint_597 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 1, 2, 1, 1, 2]
      (orbitP14RepresentativeCoeff 597) = orbitP14TargetCoeff 597 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv597 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 597))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 597)) ≃*
      CocycleGroup (orbitP14TargetCocycle 597)
        (orbitP14TargetCocycle_consistent 597) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 1, 2, 1, 1, 2] (orbitP14RepresentativeCoeff 597)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_597))

theorem orbitP14_path_endpoint_598 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0]
      (orbitP14RepresentativeCoeff 598) = orbitP14TargetCoeff 598 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv598 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 598))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 598)) ≃*
      CocycleGroup (orbitP14TargetCocycle 598)
        (orbitP14TargetCocycle_consistent 598) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0] (orbitP14RepresentativeCoeff 598)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_598))

theorem orbitP14_path_endpoint_599 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 1, 2, 1]
      (orbitP14RepresentativeCoeff 599) = orbitP14TargetCoeff 599 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv599 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 599))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 599)) ≃*
      CocycleGroup (orbitP14TargetCocycle 599)
        (orbitP14TargetCocycle_consistent 599) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 1, 2, 1] (orbitP14RepresentativeCoeff 599)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_599))

theorem orbitP14_path_endpoint_600 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 0, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 600) = orbitP14TargetCoeff 600 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv600 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 600))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 600)) ≃*
      CocycleGroup (orbitP14TargetCocycle 600)
        (orbitP14TargetCocycle_consistent 600) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 0, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 600)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_600))

theorem orbitP14_path_endpoint_601 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0]
      (orbitP14RepresentativeCoeff 601) = orbitP14TargetCoeff 601 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv601 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 601))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 601)) ≃*
      CocycleGroup (orbitP14TargetCocycle 601)
        (orbitP14TargetCocycle_consistent 601) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0] (orbitP14RepresentativeCoeff 601)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_601))

theorem orbitP14_path_endpoint_602 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 602) = orbitP14TargetCoeff 602 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv602 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 602))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 602)) ≃*
      CocycleGroup (orbitP14TargetCocycle 602)
        (orbitP14TargetCocycle_consistent 602) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 602)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_602))

theorem orbitP14_path_endpoint_603 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1]
      (orbitP14RepresentativeCoeff 603) = orbitP14TargetCoeff 603 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv603 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 603))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 603)) ≃*
      CocycleGroup (orbitP14TargetCocycle 603)
        (orbitP14TargetCocycle_consistent 603) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1] (orbitP14RepresentativeCoeff 603)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_603))

theorem orbitP14_path_endpoint_604 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 1, 0, 2, 1, 0]
      (orbitP14RepresentativeCoeff 604) = orbitP14TargetCoeff 604 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv604 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 604))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 604)) ≃*
      CocycleGroup (orbitP14TargetCocycle 604)
        (orbitP14TargetCocycle_consistent 604) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 1, 0, 2, 1, 0] (orbitP14RepresentativeCoeff 604)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_604))

theorem orbitP14_path_endpoint_605 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1]
      (orbitP14RepresentativeCoeff 605) = orbitP14TargetCoeff 605 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv605 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 605))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 605)) ≃*
      CocycleGroup (orbitP14TargetCocycle 605)
        (orbitP14TargetCocycle_consistent 605) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1] (orbitP14RepresentativeCoeff 605)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_605))

theorem orbitP14_path_endpoint_606 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 606) = orbitP14TargetCoeff 606 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv606 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 606))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 606)) ≃*
      CocycleGroup (orbitP14TargetCocycle 606)
        (orbitP14TargetCocycle_consistent 606) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 606)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_606))

theorem orbitP14_path_endpoint_607 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 1, 2]
      (orbitP14RepresentativeCoeff 607) = orbitP14TargetCoeff 607 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv607 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 607))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 607)) ≃*
      CocycleGroup (orbitP14TargetCocycle 607)
        (orbitP14TargetCocycle_consistent 607) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 1, 2] (orbitP14RepresentativeCoeff 607)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_607))

end Smallgroups.UsefulTheorems.Order32Certificate
