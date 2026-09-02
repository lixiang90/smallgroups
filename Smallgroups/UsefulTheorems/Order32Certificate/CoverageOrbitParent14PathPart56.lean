/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart55

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 56. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_880 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 880) = orbitP14TargetCoeff 880 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv880 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 880))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 880)) ≃*
      CocycleGroup (orbitP14TargetCocycle 880)
        (orbitP14TargetCocycle_consistent 880) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 880)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_880))

theorem orbitP14_path_endpoint_881 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 0, 1, 1]
      (orbitP14RepresentativeCoeff 881) = orbitP14TargetCoeff 881 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv881 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 881))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 881)) ≃*
      CocycleGroup (orbitP14TargetCocycle 881)
        (orbitP14TargetCocycle_consistent 881) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 0, 1, 1] (orbitP14RepresentativeCoeff 881)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_881))

theorem orbitP14_path_endpoint_882 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 1, 2, 1]
      (orbitP14RepresentativeCoeff 882) = orbitP14TargetCoeff 882 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv882 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 882))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 882)) ≃*
      CocycleGroup (orbitP14TargetCocycle 882)
        (orbitP14TargetCocycle_consistent 882) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 1, 2, 1] (orbitP14RepresentativeCoeff 882)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_882))

theorem orbitP14_path_endpoint_883 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 1, 2, 1, 0, 2, 1, 0]
      (orbitP14RepresentativeCoeff 883) = orbitP14TargetCoeff 883 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv883 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 883))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 883)) ≃*
      CocycleGroup (orbitP14TargetCocycle 883)
        (orbitP14TargetCocycle_consistent 883) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 1, 2, 1, 0, 2, 1, 0] (orbitP14RepresentativeCoeff 883)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_883))

theorem orbitP14_path_endpoint_884 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 884) = orbitP14TargetCoeff 884 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv884 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 884))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 884)) ≃*
      CocycleGroup (orbitP14TargetCocycle 884)
        (orbitP14TargetCocycle_consistent 884) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 884)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_884))

theorem orbitP14_path_endpoint_885 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 0, 1, 2, 1, 2]
      (orbitP14RepresentativeCoeff 885) = orbitP14TargetCoeff 885 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv885 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 885))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 885)) ≃*
      CocycleGroup (orbitP14TargetCocycle 885)
        (orbitP14TargetCocycle_consistent 885) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 0, 1, 2, 1, 2] (orbitP14RepresentativeCoeff 885)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_885))

theorem orbitP14_path_endpoint_886 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 1, 2, 1, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 886) = orbitP14TargetCoeff 886 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv886 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 886))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 886)) ≃*
      CocycleGroup (orbitP14TargetCocycle 886)
        (orbitP14TargetCocycle_consistent 886) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 1, 2, 1, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 886)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_886))

theorem orbitP14_path_endpoint_887 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 0, 2, 0, 1, 2, 1, 0, 1]
      (orbitP14RepresentativeCoeff 887) = orbitP14TargetCoeff 887 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv887 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 887))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 887)) ≃*
      CocycleGroup (orbitP14TargetCocycle 887)
        (orbitP14TargetCocycle_consistent 887) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 0, 2, 0, 1, 2, 1, 0, 1] (orbitP14RepresentativeCoeff 887)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_887))

theorem orbitP14_path_endpoint_888 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 0, 2, 1, 2, 1]
      (orbitP14RepresentativeCoeff 888) = orbitP14TargetCoeff 888 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv888 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 888))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 888)) ≃*
      CocycleGroup (orbitP14TargetCocycle 888)
        (orbitP14TargetCocycle_consistent 888) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 0, 2, 1, 2, 1] (orbitP14RepresentativeCoeff 888)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_888))

theorem orbitP14_path_endpoint_889 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 889) = orbitP14TargetCoeff 889 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv889 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 889))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 889)) ≃*
      CocycleGroup (orbitP14TargetCocycle 889)
        (orbitP14TargetCocycle_consistent 889) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 889)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_889))

theorem orbitP14_path_endpoint_890 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 0, 1, 1, 2]
      (orbitP14RepresentativeCoeff 890) = orbitP14TargetCoeff 890 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv890 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 890))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 890)) ≃*
      CocycleGroup (orbitP14TargetCocycle 890)
        (orbitP14TargetCocycle_consistent 890) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 0, 1, 1, 2] (orbitP14RepresentativeCoeff 890)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_890))

theorem orbitP14_path_endpoint_891 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 1, 2]
      (orbitP14RepresentativeCoeff 891) = orbitP14TargetCoeff 891 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv891 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 891))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 891)) ≃*
      CocycleGroup (orbitP14TargetCocycle 891)
        (orbitP14TargetCocycle_consistent 891) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 1, 2] (orbitP14RepresentativeCoeff 891)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_891))

theorem orbitP14_path_endpoint_892 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 892) = orbitP14TargetCoeff 892 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv892 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 892))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 892)) ≃*
      CocycleGroup (orbitP14TargetCocycle 892)
        (orbitP14TargetCocycle_consistent 892) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 892)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_892))

theorem orbitP14_path_endpoint_893 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 893) = orbitP14TargetCoeff 893 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv893 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 893))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 893)) ≃*
      CocycleGroup (orbitP14TargetCocycle 893)
        (orbitP14TargetCocycle_consistent 893) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 1, 2, 0] (orbitP14RepresentativeCoeff 893)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_893))

theorem orbitP14_path_endpoint_894 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 894) = orbitP14TargetCoeff 894 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv894 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 894))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 894)) ≃*
      CocycleGroup (orbitP14TargetCocycle 894)
        (orbitP14TargetCocycle_consistent 894) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 894)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_894))

theorem orbitP14_path_endpoint_895 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 895) = orbitP14TargetCoeff 895 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv895 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 895))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 895)) ≃*
      CocycleGroup (orbitP14TargetCocycle 895)
        (orbitP14TargetCocycle_consistent 895) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 0, 1, 2] (orbitP14RepresentativeCoeff 895)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_895))

end Smallgroups.UsefulTheorems.Order32Certificate
