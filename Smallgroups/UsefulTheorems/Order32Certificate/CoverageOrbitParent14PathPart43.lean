/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart42

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 43. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_672 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 672) = orbitP14TargetCoeff 672 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv672 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 672))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 672)) ≃*
      CocycleGroup (orbitP14TargetCocycle 672)
        (orbitP14TargetCocycle_consistent 672) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 1] (orbitP14RepresentativeCoeff 672)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_672))

theorem orbitP14_path_endpoint_673 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 2, 0, 1, 2, 1, 1, 0]
      (orbitP14RepresentativeCoeff 673) = orbitP14TargetCoeff 673 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv673 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 673))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 673)) ≃*
      CocycleGroup (orbitP14TargetCocycle 673)
        (orbitP14TargetCocycle_consistent 673) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 2, 0, 1, 2, 1, 1, 0] (orbitP14RepresentativeCoeff 673)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_673))

theorem orbitP14_path_endpoint_674 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 2, 1, 2, 1]
      (orbitP14RepresentativeCoeff 674) = orbitP14TargetCoeff 674 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv674 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 674))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 674)) ≃*
      CocycleGroup (orbitP14TargetCocycle 674)
        (orbitP14TargetCocycle_consistent 674) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 2, 1, 2, 1] (orbitP14RepresentativeCoeff 674)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_674))

theorem orbitP14_path_endpoint_675 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 0, 2]
      (orbitP14RepresentativeCoeff 675) = orbitP14TargetCoeff 675 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv675 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 675))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 675)) ≃*
      CocycleGroup (orbitP14TargetCocycle 675)
        (orbitP14TargetCocycle_consistent 675) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 0, 2] (orbitP14RepresentativeCoeff 675)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_675))

theorem orbitP14_path_endpoint_676 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 2, 1, 2, 0]
      (orbitP14RepresentativeCoeff 676) = orbitP14TargetCoeff 676 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv676 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 676))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 676)) ≃*
      CocycleGroup (orbitP14TargetCocycle 676)
        (orbitP14TargetCocycle_consistent 676) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 2, 1, 2, 0] (orbitP14RepresentativeCoeff 676)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_676))

theorem orbitP14_path_endpoint_677 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 1, 1, 2]
      (orbitP14RepresentativeCoeff 677) = orbitP14TargetCoeff 677 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv677 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 677))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 677)) ≃*
      CocycleGroup (orbitP14TargetCocycle 677)
        (orbitP14TargetCocycle_consistent 677) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 1, 1, 2] (orbitP14RepresentativeCoeff 677)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_677))

theorem orbitP14_path_endpoint_678 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 1, 2, 1, 2, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 678) = orbitP14TargetCoeff 678 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv678 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 678))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 678)) ≃*
      CocycleGroup (orbitP14TargetCocycle 678)
        (orbitP14TargetCocycle_consistent 678) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 1, 2, 1, 2, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 678)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_678))

theorem orbitP14_path_endpoint_679 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 0]
      (orbitP14RepresentativeCoeff 679) = orbitP14TargetCoeff 679 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv679 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 679))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 679)) ≃*
      CocycleGroup (orbitP14TargetCocycle 679)
        (orbitP14TargetCocycle_consistent 679) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 0] (orbitP14RepresentativeCoeff 679)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_679))

theorem orbitP14_path_endpoint_680 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 0, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 680) = orbitP14TargetCoeff 680 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv680 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 680))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 680)) ≃*
      CocycleGroup (orbitP14TargetCocycle 680)
        (orbitP14TargetCocycle_consistent 680) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 0, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 680)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_680))

theorem orbitP14_path_endpoint_681 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 681) = orbitP14TargetCoeff 681 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv681 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 681))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 681)) ≃*
      CocycleGroup (orbitP14TargetCocycle 681)
        (orbitP14TargetCocycle_consistent 681) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 0, 1, 2] (orbitP14RepresentativeCoeff 681)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_681))

theorem orbitP14_path_endpoint_682 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 1, 2, 0, 1, 1, 1]
      (orbitP14RepresentativeCoeff 682) = orbitP14TargetCoeff 682 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv682 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 682))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 682)) ≃*
      CocycleGroup (orbitP14TargetCocycle 682)
        (orbitP14TargetCocycle_consistent 682) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 1, 2, 0, 1, 1, 1] (orbitP14RepresentativeCoeff 682)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_682))

theorem orbitP14_path_endpoint_683 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 1, 1, 2]
      (orbitP14RepresentativeCoeff 683) = orbitP14TargetCoeff 683 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv683 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 683))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 683)) ≃*
      CocycleGroup (orbitP14TargetCocycle 683)
        (orbitP14TargetCocycle_consistent 683) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 1, 1, 2] (orbitP14RepresentativeCoeff 683)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_683))

theorem orbitP14_path_endpoint_684 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 0, 1, 1, 2]
      (orbitP14RepresentativeCoeff 684) = orbitP14TargetCoeff 684 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv684 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 684))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 684)) ≃*
      CocycleGroup (orbitP14TargetCocycle 684)
        (orbitP14TargetCocycle_consistent 684) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 0, 1, 1, 2] (orbitP14RepresentativeCoeff 684)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_684))

theorem orbitP14_path_endpoint_685 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 0, 1, 0, 2, 0, 1]
      (orbitP14RepresentativeCoeff 685) = orbitP14TargetCoeff 685 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv685 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 685))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 685)) ≃*
      CocycleGroup (orbitP14TargetCocycle 685)
        (orbitP14TargetCocycle_consistent 685) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 0, 1, 0, 2, 0, 1] (orbitP14RepresentativeCoeff 685)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_685))

theorem orbitP14_path_endpoint_686 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 2, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 686) = orbitP14TargetCoeff 686 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv686 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 686))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 686)) ≃*
      CocycleGroup (orbitP14TargetCocycle 686)
        (orbitP14TargetCocycle_consistent 686) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 2, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 686)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_686))

theorem orbitP14_path_endpoint_687 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 687) = orbitP14TargetCoeff 687 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv687 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 687))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 687)) ≃*
      CocycleGroup (orbitP14TargetCocycle 687)
        (orbitP14TargetCocycle_consistent 687) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 0, 1, 2] (orbitP14RepresentativeCoeff 687)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_687))

end Smallgroups.UsefulTheorems.Order32Certificate
