/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart38

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 39. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_608 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 0, 2, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 608) = orbitP14TargetCoeff 608 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv608 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 608))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 608)) ≃*
      CocycleGroup (orbitP14TargetCocycle 608)
        (orbitP14TargetCocycle_consistent 608) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 0, 2, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 608)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_608))

theorem orbitP14_path_endpoint_609 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 609) = orbitP14TargetCoeff 609 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv609 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 609))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 609)) ≃*
      CocycleGroup (orbitP14TargetCocycle 609)
        (orbitP14TargetCocycle_consistent 609) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 609)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_609))

theorem orbitP14_path_endpoint_610 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 610) = orbitP14TargetCoeff 610 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv610 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 610))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 610)) ≃*
      CocycleGroup (orbitP14TargetCocycle 610)
        (orbitP14TargetCocycle_consistent 610) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 0, 1, 2] (orbitP14RepresentativeCoeff 610)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_610))

theorem orbitP14_path_endpoint_611 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 2, 0, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 611) = orbitP14TargetCoeff 611 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv611 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 611))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 611)) ≃*
      CocycleGroup (orbitP14TargetCocycle 611)
        (orbitP14TargetCocycle_consistent 611) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 2, 0, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 611)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_611))

theorem orbitP14_path_endpoint_612 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 612) = orbitP14TargetCoeff 612 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv612 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 612))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 612)) ≃*
      CocycleGroup (orbitP14TargetCocycle 612)
        (orbitP14TargetCocycle_consistent 612) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 612)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_612))

theorem orbitP14_path_endpoint_613 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 1, 1, 0, 2, 0]
      (orbitP14RepresentativeCoeff 613) = orbitP14TargetCoeff 613 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv613 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 613))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 613)) ≃*
      CocycleGroup (orbitP14TargetCocycle 613)
        (orbitP14TargetCocycle_consistent 613) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 1, 1, 0, 2, 0] (orbitP14RepresentativeCoeff 613)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_613))

theorem orbitP14_path_endpoint_614 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 614) = orbitP14TargetCoeff 614 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv614 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 614))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 614)) ≃*
      CocycleGroup (orbitP14TargetCocycle 614)
        (orbitP14TargetCocycle_consistent 614) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 1, 2, 0] (orbitP14RepresentativeCoeff 614)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_614))

theorem orbitP14_path_endpoint_615 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 2]
      (orbitP14RepresentativeCoeff 615) = orbitP14TargetCoeff 615 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv615 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 615))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 615)) ≃*
      CocycleGroup (orbitP14TargetCocycle 615)
        (orbitP14TargetCocycle_consistent 615) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 2] (orbitP14RepresentativeCoeff 615)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_615))

theorem orbitP14_path_endpoint_616 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 2, 1]
      (orbitP14RepresentativeCoeff 616) = orbitP14TargetCoeff 616 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv616 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 616))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 616)) ≃*
      CocycleGroup (orbitP14TargetCocycle 616)
        (orbitP14TargetCocycle_consistent 616) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 2, 1] (orbitP14RepresentativeCoeff 616)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_616))

theorem orbitP14_path_endpoint_617 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 1, 2, 0]
      (orbitP14RepresentativeCoeff 617) = orbitP14TargetCoeff 617 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv617 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 617))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 617)) ≃*
      CocycleGroup (orbitP14TargetCocycle 617)
        (orbitP14TargetCocycle_consistent 617) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 1, 2, 0] (orbitP14RepresentativeCoeff 617)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_617))

theorem orbitP14_path_endpoint_618 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 0, 1, 1, 2]
      (orbitP14RepresentativeCoeff 618) = orbitP14TargetCoeff 618 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv618 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 618))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 618)) ≃*
      CocycleGroup (orbitP14TargetCocycle 618)
        (orbitP14TargetCocycle_consistent 618) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 0, 1, 1, 2] (orbitP14RepresentativeCoeff 618)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_618))

theorem orbitP14_path_endpoint_619 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 619) = orbitP14TargetCoeff 619 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv619 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 619))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 619)) ≃*
      CocycleGroup (orbitP14TargetCocycle 619)
        (orbitP14TargetCocycle_consistent 619) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 0] (orbitP14RepresentativeCoeff 619)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_619))

theorem orbitP14_path_endpoint_620 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 1, 1, 0]
      (orbitP14RepresentativeCoeff 620) = orbitP14TargetCoeff 620 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv620 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 620))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 620)) ≃*
      CocycleGroup (orbitP14TargetCocycle 620)
        (orbitP14TargetCocycle_consistent 620) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 1, 1, 0] (orbitP14RepresentativeCoeff 620)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_620))

theorem orbitP14_path_endpoint_621 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 2, 1]
      (orbitP14RepresentativeCoeff 621) = orbitP14TargetCoeff 621 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv621 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 621))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 621)) ≃*
      CocycleGroup (orbitP14TargetCocycle 621)
        (orbitP14TargetCocycle_consistent 621) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 2, 1] (orbitP14RepresentativeCoeff 621)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_621))

theorem orbitP14_path_endpoint_622 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 0, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 622) = orbitP14TargetCoeff 622 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv622 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 622))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 622)) ≃*
      CocycleGroup (orbitP14TargetCocycle 622)
        (orbitP14TargetCocycle_consistent 622) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 0, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 622)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_622))

theorem orbitP14_path_endpoint_623 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 0, 2, 0, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 623) = orbitP14TargetCoeff 623 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv623 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 623))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 623)) ≃*
      CocycleGroup (orbitP14TargetCocycle 623)
        (orbitP14TargetCocycle_consistent 623) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 0, 2, 0, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 623)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_623))

end Smallgroups.UsefulTheorems.Order32Certificate
