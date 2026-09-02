/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart58

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 59. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_928 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 2, 1, 1, 0]
      (orbitP14RepresentativeCoeff 928) = orbitP14TargetCoeff 928 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv928 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 928))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 928)) ≃*
      CocycleGroup (orbitP14TargetCocycle 928)
        (orbitP14TargetCocycle_consistent 928) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 2, 1, 1, 0] (orbitP14RepresentativeCoeff 928)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_928))

theorem orbitP14_path_endpoint_929 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 0, 1, 1, 2]
      (orbitP14RepresentativeCoeff 929) = orbitP14TargetCoeff 929 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv929 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 929))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 929)) ≃*
      CocycleGroup (orbitP14TargetCocycle 929)
        (orbitP14TargetCocycle_consistent 929) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 0, 1, 1, 2] (orbitP14RepresentativeCoeff 929)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_929))

theorem orbitP14_path_endpoint_930 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 930) = orbitP14TargetCoeff 930 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv930 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 930))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 930)) ≃*
      CocycleGroup (orbitP14TargetCocycle 930)
        (orbitP14TargetCocycle_consistent 930) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 930)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_930))

theorem orbitP14_path_endpoint_931 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 931) = orbitP14TargetCoeff 931 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv931 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 931))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 931)) ≃*
      CocycleGroup (orbitP14TargetCocycle 931)
        (orbitP14TargetCocycle_consistent 931) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 931)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_931))

theorem orbitP14_path_endpoint_932 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 0, 1, 2, 1, 2, 0]
      (orbitP14RepresentativeCoeff 932) = orbitP14TargetCoeff 932 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv932 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 932))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 932)) ≃*
      CocycleGroup (orbitP14TargetCocycle 932)
        (orbitP14TargetCocycle_consistent 932) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 0, 1, 2, 1, 2, 0] (orbitP14RepresentativeCoeff 932)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_932))

theorem orbitP14_path_endpoint_933 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 0, 2, 0, 1, 2, 1, 1, 0]
      (orbitP14RepresentativeCoeff 933) = orbitP14TargetCoeff 933 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv933 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 933))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 933)) ≃*
      CocycleGroup (orbitP14TargetCocycle 933)
        (orbitP14TargetCocycle_consistent 933) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 0, 2, 0, 1, 2, 1, 1, 0] (orbitP14RepresentativeCoeff 933)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_933))

theorem orbitP14_path_endpoint_934 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 1, 0, 2]
      (orbitP14RepresentativeCoeff 934) = orbitP14TargetCoeff 934 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv934 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 934))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 934)) ≃*
      CocycleGroup (orbitP14TargetCocycle 934)
        (orbitP14TargetCocycle_consistent 934) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 1, 0, 2] (orbitP14RepresentativeCoeff 934)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_934))

theorem orbitP14_path_endpoint_935 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 935) = orbitP14TargetCoeff 935 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv935 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 935))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 935)) ≃*
      CocycleGroup (orbitP14TargetCocycle 935)
        (orbitP14TargetCocycle_consistent 935) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 935)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_935))

theorem orbitP14_path_endpoint_936 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 1, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 936) = orbitP14TargetCoeff 936 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv936 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 936))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 936)) ≃*
      CocycleGroup (orbitP14TargetCocycle 936)
        (orbitP14TargetCocycle_consistent 936) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 1, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 936)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_936))

theorem orbitP14_path_endpoint_937 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1]
      (orbitP14RepresentativeCoeff 937) = orbitP14TargetCoeff 937 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv937 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 937))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 937)) ≃*
      CocycleGroup (orbitP14TargetCocycle 937)
        (orbitP14TargetCocycle_consistent 937) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1] (orbitP14RepresentativeCoeff 937)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_937))

theorem orbitP14_path_endpoint_938 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 0, 2, 1, 1, 2]
      (orbitP14RepresentativeCoeff 938) = orbitP14TargetCoeff 938 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv938 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 938))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 938)) ≃*
      CocycleGroup (orbitP14TargetCocycle 938)
        (orbitP14TargetCocycle_consistent 938) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 0, 2, 1, 1, 2] (orbitP14RepresentativeCoeff 938)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_938))

theorem orbitP14_path_endpoint_939 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 1, 2]
      (orbitP14RepresentativeCoeff 939) = orbitP14TargetCoeff 939 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv939 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 939))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 939)) ≃*
      CocycleGroup (orbitP14TargetCocycle 939)
        (orbitP14TargetCocycle_consistent 939) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 1, 2] (orbitP14RepresentativeCoeff 939)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_939))

theorem orbitP14_path_endpoint_940 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 1, 0, 2]
      (orbitP14RepresentativeCoeff 940) = orbitP14TargetCoeff 940 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv940 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 940))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 940)) ≃*
      CocycleGroup (orbitP14TargetCocycle 940)
        (orbitP14TargetCocycle_consistent 940) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 1, 0, 2] (orbitP14RepresentativeCoeff 940)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_940))

theorem orbitP14_path_endpoint_941 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 941) = orbitP14TargetCoeff 941 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv941 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 941))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 941)) ≃*
      CocycleGroup (orbitP14TargetCocycle 941)
        (orbitP14TargetCocycle_consistent 941) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 941)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_941))

theorem orbitP14_path_endpoint_942 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 2, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 942) = orbitP14TargetCoeff 942 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv942 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 942))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 942)) ≃*
      CocycleGroup (orbitP14TargetCocycle 942)
        (orbitP14TargetCocycle_consistent 942) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 2, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 942)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_942))

theorem orbitP14_path_endpoint_943 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 2, 1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 943) = orbitP14TargetCoeff 943 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv943 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 943))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 943)) ≃*
      CocycleGroup (orbitP14TargetCocycle 943)
        (orbitP14TargetCocycle_consistent 943) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 2, 1, 1, 2, 0] (orbitP14RepresentativeCoeff 943)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_943))

end Smallgroups.UsefulTheorems.Order32Certificate
