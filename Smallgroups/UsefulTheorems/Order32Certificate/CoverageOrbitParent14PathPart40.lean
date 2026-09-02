/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart39

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 40. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_624 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 624) = orbitP14TargetCoeff 624 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv624 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 624))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 624)) ≃*
      CocycleGroup (orbitP14TargetCocycle 624)
        (orbitP14TargetCocycle_consistent 624) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 624)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_624))

theorem orbitP14_path_endpoint_625 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 625) = orbitP14TargetCoeff 625 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv625 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 625))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 625)) ≃*
      CocycleGroup (orbitP14TargetCocycle 625)
        (orbitP14TargetCocycle_consistent 625) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 625)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_625))

theorem orbitP14_path_endpoint_626 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 0, 1, 2, 1, 2]
      (orbitP14RepresentativeCoeff 626) = orbitP14TargetCoeff 626 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv626 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 626))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 626)) ≃*
      CocycleGroup (orbitP14TargetCocycle 626)
        (orbitP14TargetCocycle_consistent 626) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 0, 1, 2, 1, 2] (orbitP14RepresentativeCoeff 626)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_626))

theorem orbitP14_path_endpoint_627 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 0, 2, 0, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 627) = orbitP14TargetCoeff 627 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv627 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 627))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 627)) ≃*
      CocycleGroup (orbitP14TargetCocycle 627)
        (orbitP14TargetCocycle_consistent 627) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 0, 2, 0, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 627)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_627))

theorem orbitP14_path_endpoint_628 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 0, 1]
      (orbitP14RepresentativeCoeff 628) = orbitP14TargetCoeff 628 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv628 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 628))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 628)) ≃*
      CocycleGroup (orbitP14TargetCocycle 628)
        (orbitP14TargetCocycle_consistent 628) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 0, 1] (orbitP14RepresentativeCoeff 628)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_628))

theorem orbitP14_path_endpoint_629 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 1, 2, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 629) = orbitP14TargetCoeff 629 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv629 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 629))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 629)) ≃*
      CocycleGroup (orbitP14TargetCocycle 629)
        (orbitP14TargetCocycle_consistent 629) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 1, 2, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 629)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_629))

theorem orbitP14_path_endpoint_630 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 0, 1, 1]
      (orbitP14RepresentativeCoeff 630) = orbitP14TargetCoeff 630 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv630 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 630))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 630)) ≃*
      CocycleGroup (orbitP14TargetCocycle 630)
        (orbitP14TargetCocycle_consistent 630) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 0, 1, 1] (orbitP14RepresentativeCoeff 630)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_630))

theorem orbitP14_path_endpoint_631 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 1, 2, 1]
      (orbitP14RepresentativeCoeff 631) = orbitP14TargetCoeff 631 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv631 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 631))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 631)) ≃*
      CocycleGroup (orbitP14TargetCocycle 631)
        (orbitP14TargetCocycle_consistent 631) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 1, 2, 1] (orbitP14RepresentativeCoeff 631)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_631))

theorem orbitP14_path_endpoint_632 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 632) = orbitP14TargetCoeff 632 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv632 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 632))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 632)) ≃*
      CocycleGroup (orbitP14TargetCocycle 632)
        (orbitP14TargetCocycle_consistent 632) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 632)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_632))

theorem orbitP14_path_endpoint_633 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1]
      (orbitP14RepresentativeCoeff 633) = orbitP14TargetCoeff 633 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv633 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 633))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 633)) ≃*
      CocycleGroup (orbitP14TargetCocycle 633)
        (orbitP14TargetCocycle_consistent 633) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1] (orbitP14RepresentativeCoeff 633)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_633))

theorem orbitP14_path_endpoint_634 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 634) = orbitP14TargetCoeff 634 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv634 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 634))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 634)) ≃*
      CocycleGroup (orbitP14TargetCocycle 634)
        (orbitP14TargetCocycle_consistent 634) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 634)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_634))

theorem orbitP14_path_endpoint_635 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 635) = orbitP14TargetCoeff 635 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv635 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 635))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 635)) ≃*
      CocycleGroup (orbitP14TargetCocycle 635)
        (orbitP14TargetCocycle_consistent 635) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 635)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_635))

theorem orbitP14_path_endpoint_636 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 636) = orbitP14TargetCoeff 636 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv636 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 636))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 636)) ≃*
      CocycleGroup (orbitP14TargetCocycle 636)
        (orbitP14TargetCocycle_consistent 636) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 636)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_636))

theorem orbitP14_path_endpoint_637 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 637) = orbitP14TargetCoeff 637 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv637 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 637))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 637)) ≃*
      CocycleGroup (orbitP14TargetCocycle 637)
        (orbitP14TargetCocycle_consistent 637) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 1, 2, 0] (orbitP14RepresentativeCoeff 637)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_637))

theorem orbitP14_path_endpoint_638 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 2, 0, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 638) = orbitP14TargetCoeff 638 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv638 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 638))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 638)) ≃*
      CocycleGroup (orbitP14TargetCocycle 638)
        (orbitP14TargetCocycle_consistent 638) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 2, 0, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 638)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_638))

theorem orbitP14_path_endpoint_639 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 2, 1, 1, 2]
      (orbitP14RepresentativeCoeff 639) = orbitP14TargetCoeff 639 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv639 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 639))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 639)) ≃*
      CocycleGroup (orbitP14TargetCocycle 639)
        (orbitP14TargetCocycle_consistent 639) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 2, 1, 1, 2] (orbitP14RepresentativeCoeff 639)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_639))

end Smallgroups.UsefulTheorems.Order32Certificate
