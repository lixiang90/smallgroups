/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart52

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 53. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_832 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 832) = orbitP14TargetCoeff 832 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv832 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 832))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 832)) ≃*
      CocycleGroup (orbitP14TargetCocycle 832)
        (orbitP14TargetCocycle_consistent 832) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 832)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_832))

theorem orbitP14_path_endpoint_833 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 1, 1, 0, 1]
      (orbitP14RepresentativeCoeff 833) = orbitP14TargetCoeff 833 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv833 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 833))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 833)) ≃*
      CocycleGroup (orbitP14TargetCocycle 833)
        (orbitP14TargetCocycle_consistent 833) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 1, 1, 0, 1] (orbitP14RepresentativeCoeff 833)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_833))

theorem orbitP14_path_endpoint_834 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 834) = orbitP14TargetCoeff 834 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv834 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 834))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 834)) ≃*
      CocycleGroup (orbitP14TargetCocycle 834)
        (orbitP14TargetCocycle_consistent 834) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 834)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_834))

theorem orbitP14_path_endpoint_835 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 0, 1, 0, 2, 1, 2, 0]
      (orbitP14RepresentativeCoeff 835) = orbitP14TargetCoeff 835 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv835 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 835))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 835)) ≃*
      CocycleGroup (orbitP14TargetCocycle 835)
        (orbitP14TargetCocycle_consistent 835) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 0, 1, 0, 2, 1, 2, 0] (orbitP14RepresentativeCoeff 835)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_835))

theorem orbitP14_path_endpoint_836 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 0, 1, 2]
      (orbitP14RepresentativeCoeff 836) = orbitP14TargetCoeff 836 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv836 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 836))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 836)) ≃*
      CocycleGroup (orbitP14TargetCocycle 836)
        (orbitP14TargetCocycle_consistent 836) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 0, 1, 2] (orbitP14RepresentativeCoeff 836)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_836))

theorem orbitP14_path_endpoint_837 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 0, 1, 0, 2, 1, 2]
      (orbitP14RepresentativeCoeff 837) = orbitP14TargetCoeff 837 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv837 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 837))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 837)) ≃*
      CocycleGroup (orbitP14TargetCocycle 837)
        (orbitP14TargetCocycle_consistent 837) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 0, 1, 0, 2, 1, 2] (orbitP14RepresentativeCoeff 837)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_837))

theorem orbitP14_path_endpoint_838 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 838) = orbitP14TargetCoeff 838 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv838 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 838))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 838)) ≃*
      CocycleGroup (orbitP14TargetCocycle 838)
        (orbitP14TargetCocycle_consistent 838) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 838)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_838))

theorem orbitP14_path_endpoint_839 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 839) = orbitP14TargetCoeff 839 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv839 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 839))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 839)) ≃*
      CocycleGroup (orbitP14TargetCocycle 839)
        (orbitP14TargetCocycle_consistent 839) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 839)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_839))

theorem orbitP14_path_endpoint_840 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 2, 1, 1, 2]
      (orbitP14RepresentativeCoeff 840) = orbitP14TargetCoeff 840 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv840 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 840))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 840)) ≃*
      CocycleGroup (orbitP14TargetCocycle 840)
        (orbitP14TargetCocycle_consistent 840) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 2, 1, 1, 2] (orbitP14RepresentativeCoeff 840)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_840))

theorem orbitP14_path_endpoint_841 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 0, 1, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 841) = orbitP14TargetCoeff 841 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv841 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 841))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 841)) ≃*
      CocycleGroup (orbitP14TargetCocycle 841)
        (orbitP14TargetCocycle_consistent 841) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 0, 1, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 841)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_841))

theorem orbitP14_path_endpoint_842 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 0, 1, 0, 1, 2]
      (orbitP14RepresentativeCoeff 842) = orbitP14TargetCoeff 842 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv842 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 842))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 842)) ≃*
      CocycleGroup (orbitP14TargetCocycle 842)
        (orbitP14TargetCocycle_consistent 842) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 0, 1, 0, 1, 2] (orbitP14RepresentativeCoeff 842)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_842))

theorem orbitP14_path_endpoint_843 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 0, 2, 1, 2]
      (orbitP14RepresentativeCoeff 843) = orbitP14TargetCoeff 843 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv843 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 843))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 843)) ≃*
      CocycleGroup (orbitP14TargetCocycle 843)
        (orbitP14TargetCocycle_consistent 843) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 0, 2, 1, 2] (orbitP14RepresentativeCoeff 843)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_843))

theorem orbitP14_path_endpoint_844 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 0, 1, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 844) = orbitP14TargetCoeff 844 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv844 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 844))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 844)) ≃*
      CocycleGroup (orbitP14TargetCocycle 844)
        (orbitP14TargetCocycle_consistent 844) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 0, 1, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 844)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_844))

theorem orbitP14_path_endpoint_845 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 1, 2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 845) = orbitP14TargetCoeff 845 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv845 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 845))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 845)) ≃*
      CocycleGroup (orbitP14TargetCocycle 845)
        (orbitP14TargetCocycle_consistent 845) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 1, 2, 0, 1, 2] (orbitP14RepresentativeCoeff 845)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_845))

theorem orbitP14_path_endpoint_846 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 2, 0, 1, 1, 2]
      (orbitP14RepresentativeCoeff 846) = orbitP14TargetCoeff 846 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv846 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 846))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 846)) ≃*
      CocycleGroup (orbitP14TargetCocycle 846)
        (orbitP14TargetCocycle_consistent 846) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 2, 0, 1, 1, 2] (orbitP14RepresentativeCoeff 846)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_846))

theorem orbitP14_path_endpoint_847 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 1, 2, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 847) = orbitP14TargetCoeff 847 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv847 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 847))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 847)) ≃*
      CocycleGroup (orbitP14TargetCocycle 847)
        (orbitP14TargetCocycle_consistent 847) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 1, 2, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 847)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_847))

end Smallgroups.UsefulTheorems.Order32Certificate
