/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart62

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 63. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_992 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 1, 0]
      (orbitP14RepresentativeCoeff 992) = orbitP14TargetCoeff 992 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv992 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 992))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 992)) ≃*
      CocycleGroup (orbitP14TargetCocycle 992)
        (orbitP14TargetCocycle_consistent 992) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 1, 0] (orbitP14RepresentativeCoeff 992)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_992))

theorem orbitP14_path_endpoint_993 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 0, 1, 1, 0]
      (orbitP14RepresentativeCoeff 993) = orbitP14TargetCoeff 993 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv993 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 993))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 993)) ≃*
      CocycleGroup (orbitP14TargetCocycle 993)
        (orbitP14TargetCocycle_consistent 993) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 0, 1, 1, 0] (orbitP14RepresentativeCoeff 993)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_993))

theorem orbitP14_path_endpoint_994 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 0, 1, 0]
      (orbitP14RepresentativeCoeff 994) = orbitP14TargetCoeff 994 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv994 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 994))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 994)) ≃*
      CocycleGroup (orbitP14TargetCocycle 994)
        (orbitP14TargetCocycle_consistent 994) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 0, 1, 0] (orbitP14RepresentativeCoeff 994)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_994))

theorem orbitP14_path_endpoint_995 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 0, 1, 2, 1, 2, 0]
      (orbitP14RepresentativeCoeff 995) = orbitP14TargetCoeff 995 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv995 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 995))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 995)) ≃*
      CocycleGroup (orbitP14TargetCocycle 995)
        (orbitP14TargetCocycle_consistent 995) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 0, 1, 2, 1, 2, 0] (orbitP14RepresentativeCoeff 995)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_995))

theorem orbitP14_path_endpoint_996 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 996) = orbitP14TargetCoeff 996 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv996 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 996))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 996)) ≃*
      CocycleGroup (orbitP14TargetCocycle 996)
        (orbitP14TargetCocycle_consistent 996) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 996)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_996))

theorem orbitP14_path_endpoint_997 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 1, 2, 1, 0, 2, 1]
      (orbitP14RepresentativeCoeff 997) = orbitP14TargetCoeff 997 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv997 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 997))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 997)) ≃*
      CocycleGroup (orbitP14TargetCocycle 997)
        (orbitP14TargetCocycle_consistent 997) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 1, 2, 1, 0, 2, 1] (orbitP14RepresentativeCoeff 997)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_997))

theorem orbitP14_path_endpoint_998 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 1, 2, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 998) = orbitP14TargetCoeff 998 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv998 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 998))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 998)) ≃*
      CocycleGroup (orbitP14TargetCocycle 998)
        (orbitP14TargetCocycle_consistent 998) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 1, 2, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 998)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_998))

theorem orbitP14_path_endpoint_999 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 2, 0, 1, 2, 1, 0, 1]
      (orbitP14RepresentativeCoeff 999) = orbitP14TargetCoeff 999 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv999 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 999))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 999)) ≃*
      CocycleGroup (orbitP14TargetCocycle 999)
        (orbitP14TargetCocycle_consistent 999) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 2, 0, 1, 2, 1, 0, 1] (orbitP14RepresentativeCoeff 999)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_999))

theorem orbitP14_path_endpoint_1000 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 0, 2, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 1000) = orbitP14TargetCoeff 1000 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv1000 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 1000))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 1000)) ≃*
      CocycleGroup (orbitP14TargetCocycle 1000)
        (orbitP14TargetCocycle_consistent 1000) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 0, 2, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 1000)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_1000))

theorem orbitP14_path_endpoint_1001 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 0, 1, 0]
      (orbitP14RepresentativeCoeff 1001) = orbitP14TargetCoeff 1001 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv1001 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 1001))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 1001)) ≃*
      CocycleGroup (orbitP14TargetCocycle 1001)
        (orbitP14TargetCocycle_consistent 1001) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 0, 1, 0] (orbitP14RepresentativeCoeff 1001)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_1001))

theorem orbitP14_path_endpoint_1002 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 1, 2]
      (orbitP14RepresentativeCoeff 1002) = orbitP14TargetCoeff 1002 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv1002 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 1002))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 1002)) ≃*
      CocycleGroup (orbitP14TargetCocycle 1002)
        (orbitP14TargetCocycle_consistent 1002) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 1, 2] (orbitP14RepresentativeCoeff 1002)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_1002))

theorem orbitP14_path_endpoint_1003 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 1, 2]
      (orbitP14RepresentativeCoeff 1003) = orbitP14TargetCoeff 1003 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv1003 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 1003))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 1003)) ≃*
      CocycleGroup (orbitP14TargetCocycle 1003)
        (orbitP14TargetCocycle_consistent 1003) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 1, 2] (orbitP14RepresentativeCoeff 1003)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_1003))

theorem orbitP14_path_endpoint_1004 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 0, 1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 1004) = orbitP14TargetCoeff 1004 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv1004 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 1004))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 1004)) ≃*
      CocycleGroup (orbitP14TargetCocycle 1004)
        (orbitP14TargetCocycle_consistent 1004) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 0, 1, 1, 2, 0] (orbitP14RepresentativeCoeff 1004)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_1004))

theorem orbitP14_path_endpoint_1005 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 1005) = orbitP14TargetCoeff 1005 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv1005 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 1005))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 1005)) ≃*
      CocycleGroup (orbitP14TargetCocycle 1005)
        (orbitP14TargetCocycle_consistent 1005) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 1, 2, 0] (orbitP14RepresentativeCoeff 1005)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_1005))

theorem orbitP14_path_endpoint_1006 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 0, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 1006) = orbitP14TargetCoeff 1006 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv1006 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 1006))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 1006)) ≃*
      CocycleGroup (orbitP14TargetCocycle 1006)
        (orbitP14TargetCocycle_consistent 1006) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 0, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 1006)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_1006))

theorem orbitP14_path_endpoint_1007 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 1007) = orbitP14TargetCoeff 1007 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv1007 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 1007))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 1007)) ≃*
      CocycleGroup (orbitP14TargetCocycle 1007)
        (orbitP14TargetCocycle_consistent 1007) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 1007)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_1007))

end Smallgroups.UsefulTheorems.Order32Certificate
