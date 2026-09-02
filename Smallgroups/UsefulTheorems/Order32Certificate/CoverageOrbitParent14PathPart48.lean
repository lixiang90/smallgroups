/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart47

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 48. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_752 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 752) = orbitP14TargetCoeff 752 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv752 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 752))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 752)) ≃*
      CocycleGroup (orbitP14TargetCocycle 752)
        (orbitP14TargetCocycle_consistent 752) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 752)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_752))

theorem orbitP14_path_endpoint_753 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 1, 2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 753) = orbitP14TargetCoeff 753 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv753 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 753))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 753)) ≃*
      CocycleGroup (orbitP14TargetCocycle 753)
        (orbitP14TargetCocycle_consistent 753) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 1, 2, 0, 1, 2] (orbitP14RepresentativeCoeff 753)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_753))

theorem orbitP14_path_endpoint_754 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 754) = orbitP14TargetCoeff 754 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv754 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 754))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 754)) ≃*
      CocycleGroup (orbitP14TargetCocycle 754)
        (orbitP14TargetCocycle_consistent 754) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 2, 0, 1, 2] (orbitP14RepresentativeCoeff 754)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_754))

theorem orbitP14_path_endpoint_755 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 755) = orbitP14TargetCoeff 755 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv755 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 755))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 755)) ≃*
      CocycleGroup (orbitP14TargetCocycle 755)
        (orbitP14TargetCocycle_consistent 755) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 2] (orbitP14RepresentativeCoeff 755)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_755))

theorem orbitP14_path_endpoint_756 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 1, 0, 2]
      (orbitP14RepresentativeCoeff 756) = orbitP14TargetCoeff 756 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv756 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 756))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 756)) ≃*
      CocycleGroup (orbitP14TargetCocycle 756)
        (orbitP14TargetCocycle_consistent 756) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 1, 0, 2] (orbitP14RepresentativeCoeff 756)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_756))

theorem orbitP14_path_endpoint_757 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 1, 1, 0, 2]
      (orbitP14RepresentativeCoeff 757) = orbitP14TargetCoeff 757 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv757 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 757))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 757)) ≃*
      CocycleGroup (orbitP14TargetCocycle 757)
        (orbitP14TargetCocycle_consistent 757) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 1, 1, 0, 2] (orbitP14RepresentativeCoeff 757)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_757))

theorem orbitP14_path_endpoint_758 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 2]
      (orbitP14RepresentativeCoeff 758) = orbitP14TargetCoeff 758 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv758 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 758))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 758)) ≃*
      CocycleGroup (orbitP14TargetCocycle 758)
        (orbitP14TargetCocycle_consistent 758) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 2] (orbitP14RepresentativeCoeff 758)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_758))

theorem orbitP14_path_endpoint_759 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 1, 2, 1, 2]
      (orbitP14RepresentativeCoeff 759) = orbitP14TargetCoeff 759 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv759 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 759))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 759)) ≃*
      CocycleGroup (orbitP14TargetCocycle 759)
        (orbitP14TargetCocycle_consistent 759) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 1, 2, 1, 2] (orbitP14RepresentativeCoeff 759)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_759))

theorem orbitP14_path_endpoint_760 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 1, 1, 2]
      (orbitP14RepresentativeCoeff 760) = orbitP14TargetCoeff 760 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv760 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 760))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 760)) ≃*
      CocycleGroup (orbitP14TargetCocycle 760)
        (orbitP14TargetCocycle_consistent 760) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 1, 1, 2] (orbitP14RepresentativeCoeff 760)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_760))

theorem orbitP14_path_endpoint_761 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 1, 2]
      (orbitP14RepresentativeCoeff 761) = orbitP14TargetCoeff 761 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv761 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 761))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 761)) ≃*
      CocycleGroup (orbitP14TargetCocycle 761)
        (orbitP14TargetCocycle_consistent 761) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 1, 2] (orbitP14RepresentativeCoeff 761)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_761))

theorem orbitP14_path_endpoint_762 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 1, 2, 1, 0, 2]
      (orbitP14RepresentativeCoeff 762) = orbitP14TargetCoeff 762 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv762 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 762))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 762)) ≃*
      CocycleGroup (orbitP14TargetCocycle 762)
        (orbitP14TargetCocycle_consistent 762) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 1, 2, 1, 0, 2] (orbitP14RepresentativeCoeff 762)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_762))

theorem orbitP14_path_endpoint_763 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 1, 2]
      (orbitP14RepresentativeCoeff 763) = orbitP14TargetCoeff 763 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv763 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 763))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 763)) ≃*
      CocycleGroup (orbitP14TargetCocycle 763)
        (orbitP14TargetCocycle_consistent 763) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 1, 2] (orbitP14RepresentativeCoeff 763)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_763))

theorem orbitP14_path_endpoint_764 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 1, 2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 764) = orbitP14TargetCoeff 764 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv764 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 764))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 764)) ≃*
      CocycleGroup (orbitP14TargetCocycle 764)
        (orbitP14TargetCocycle_consistent 764) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 1, 2, 0, 1, 2] (orbitP14RepresentativeCoeff 764)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_764))

theorem orbitP14_path_endpoint_765 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 765) = orbitP14TargetCoeff 765 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv765 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 765))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 765)) ≃*
      CocycleGroup (orbitP14TargetCocycle 765)
        (orbitP14TargetCocycle_consistent 765) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 765)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_765))

theorem orbitP14_path_endpoint_766 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 1, 2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 766) = orbitP14TargetCoeff 766 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv766 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 766))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 766)) ≃*
      CocycleGroup (orbitP14TargetCocycle 766)
        (orbitP14TargetCocycle_consistent 766) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 1, 2, 0, 1, 2] (orbitP14RepresentativeCoeff 766)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_766))

theorem orbitP14_path_endpoint_767 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 2, 1, 1, 1, 2]
      (orbitP14RepresentativeCoeff 767) = orbitP14TargetCoeff 767 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv767 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 767))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 767)) ≃*
      CocycleGroup (orbitP14TargetCocycle 767)
        (orbitP14TargetCocycle_consistent 767) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 2, 1, 1, 1, 2] (orbitP14RepresentativeCoeff 767)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_767))

end Smallgroups.UsefulTheorems.Order32Certificate
