/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart53

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 54. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_848 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 848) = orbitP14TargetCoeff 848 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv848 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 848))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 848)) ≃*
      CocycleGroup (orbitP14TargetCocycle 848)
        (orbitP14TargetCocycle_consistent 848) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 848)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_848))

theorem orbitP14_path_endpoint_849 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 1, 2, 0, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 849) = orbitP14TargetCoeff 849 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv849 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 849))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 849)) ≃*
      CocycleGroup (orbitP14TargetCocycle 849)
        (orbitP14TargetCocycle_consistent 849) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 1, 2, 0, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 849)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_849))

theorem orbitP14_path_endpoint_850 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 850) = orbitP14TargetCoeff 850 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv850 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 850))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 850)) ≃*
      CocycleGroup (orbitP14TargetCocycle 850)
        (orbitP14TargetCocycle_consistent 850) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 1, 2, 0] (orbitP14RepresentativeCoeff 850)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_850))

theorem orbitP14_path_endpoint_851 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 851) = orbitP14TargetCoeff 851 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv851 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 851))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 851)) ≃*
      CocycleGroup (orbitP14TargetCocycle 851)
        (orbitP14TargetCocycle_consistent 851) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 851)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_851))

theorem orbitP14_path_endpoint_852 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 2, 1, 0, 2]
      (orbitP14RepresentativeCoeff 852) = orbitP14TargetCoeff 852 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv852 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 852))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 852)) ≃*
      CocycleGroup (orbitP14TargetCocycle 852)
        (orbitP14TargetCocycle_consistent 852) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 2, 1, 0, 2] (orbitP14RepresentativeCoeff 852)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_852))

theorem orbitP14_path_endpoint_853 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 853) = orbitP14TargetCoeff 853 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv853 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 853))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 853)) ≃*
      CocycleGroup (orbitP14TargetCocycle 853)
        (orbitP14TargetCocycle_consistent 853) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 1, 2, 0] (orbitP14RepresentativeCoeff 853)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_853))

theorem orbitP14_path_endpoint_854 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 854) = orbitP14TargetCoeff 854 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv854 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 854))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 854)) ≃*
      CocycleGroup (orbitP14TargetCocycle 854)
        (orbitP14TargetCocycle_consistent 854) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 854)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_854))

theorem orbitP14_path_endpoint_855 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 0, 2, 0, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 855) = orbitP14TargetCoeff 855 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv855 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 855))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 855)) ≃*
      CocycleGroup (orbitP14TargetCocycle 855)
        (orbitP14TargetCocycle_consistent 855) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 0, 2, 0, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 855)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_855))

theorem orbitP14_path_endpoint_856 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 856) = orbitP14TargetCoeff 856 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv856 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 856))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 856)) ≃*
      CocycleGroup (orbitP14TargetCocycle 856)
        (orbitP14TargetCocycle_consistent 856) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 856)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_856))

theorem orbitP14_path_endpoint_857 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 857) = orbitP14TargetCoeff 857 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv857 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 857))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 857)) ≃*
      CocycleGroup (orbitP14TargetCocycle 857)
        (orbitP14TargetCocycle_consistent 857) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 1, 2, 0] (orbitP14RepresentativeCoeff 857)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_857))

theorem orbitP14_path_endpoint_858 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 0, 1, 2, 1, 2, 1]
      (orbitP14RepresentativeCoeff 858) = orbitP14TargetCoeff 858 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv858 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 858))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 858)) ≃*
      CocycleGroup (orbitP14TargetCocycle 858)
        (orbitP14TargetCocycle_consistent 858) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 0, 1, 2, 1, 2, 1] (orbitP14RepresentativeCoeff 858)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_858))

theorem orbitP14_path_endpoint_859 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 0, 1, 2]
      (orbitP14RepresentativeCoeff 859) = orbitP14TargetCoeff 859 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv859 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 859))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 859)) ≃*
      CocycleGroup (orbitP14TargetCocycle 859)
        (orbitP14TargetCocycle_consistent 859) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 0, 1, 2] (orbitP14RepresentativeCoeff 859)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_859))

theorem orbitP14_path_endpoint_860 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 1, 2, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 860) = orbitP14TargetCoeff 860 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv860 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 860))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 860)) ≃*
      CocycleGroup (orbitP14TargetCocycle 860)
        (orbitP14TargetCocycle_consistent 860) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 1, 2, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 860)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_860))

theorem orbitP14_path_endpoint_861 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2]
      (orbitP14RepresentativeCoeff 861) = orbitP14TargetCoeff 861 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv861 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 861))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 861)) ≃*
      CocycleGroup (orbitP14TargetCocycle 861)
        (orbitP14TargetCocycle_consistent 861) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2] (orbitP14RepresentativeCoeff 861)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_861))

theorem orbitP14_path_endpoint_862 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 862) = orbitP14TargetCoeff 862 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv862 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 862))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 862)) ≃*
      CocycleGroup (orbitP14TargetCocycle 862)
        (orbitP14TargetCocycle_consistent 862) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 862)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_862))

theorem orbitP14_path_endpoint_863 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 2, 1, 1, 2]
      (orbitP14RepresentativeCoeff 863) = orbitP14TargetCoeff 863 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv863 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 863))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 863)) ≃*
      CocycleGroup (orbitP14TargetCocycle 863)
        (orbitP14TargetCocycle_consistent 863) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 2, 1, 1, 2] (orbitP14RepresentativeCoeff 863)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_863))

end Smallgroups.UsefulTheorems.Order32Certificate
