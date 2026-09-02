/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart61

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 62. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_976 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 976) = orbitP14TargetCoeff 976 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv976 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 976))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 976)) ≃*
      CocycleGroup (orbitP14TargetCocycle 976)
        (orbitP14TargetCocycle_consistent 976) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 976)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_976))

theorem orbitP14_path_endpoint_977 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 977) = orbitP14TargetCoeff 977 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv977 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 977))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 977)) ≃*
      CocycleGroup (orbitP14TargetCocycle 977)
        (orbitP14TargetCocycle_consistent 977) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 977)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_977))

theorem orbitP14_path_endpoint_978 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1]
      (orbitP14RepresentativeCoeff 978) = orbitP14TargetCoeff 978 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv978 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 978))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 978)) ≃*
      CocycleGroup (orbitP14TargetCocycle 978)
        (orbitP14TargetCocycle_consistent 978) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1] (orbitP14RepresentativeCoeff 978)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_978))

theorem orbitP14_path_endpoint_979 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 1, 2, 1]
      (orbitP14RepresentativeCoeff 979) = orbitP14TargetCoeff 979 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv979 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 979))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 979)) ≃*
      CocycleGroup (orbitP14TargetCocycle 979)
        (orbitP14TargetCocycle_consistent 979) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 1, 2, 1] (orbitP14RepresentativeCoeff 979)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_979))

theorem orbitP14_path_endpoint_980 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 980) = orbitP14TargetCoeff 980 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv980 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 980))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 980)) ≃*
      CocycleGroup (orbitP14TargetCocycle 980)
        (orbitP14TargetCocycle_consistent 980) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 1] (orbitP14RepresentativeCoeff 980)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_980))

theorem orbitP14_path_endpoint_981 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 981) = orbitP14TargetCoeff 981 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv981 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 981))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 981)) ≃*
      CocycleGroup (orbitP14TargetCocycle 981)
        (orbitP14TargetCocycle_consistent 981) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 981)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_981))

theorem orbitP14_path_endpoint_982 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 982) = orbitP14TargetCoeff 982 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv982 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 982))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 982)) ≃*
      CocycleGroup (orbitP14TargetCocycle 982)
        (orbitP14TargetCocycle_consistent 982) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 982)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_982))

theorem orbitP14_path_endpoint_983 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 983) = orbitP14TargetCoeff 983 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv983 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 983))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 983)) ≃*
      CocycleGroup (orbitP14TargetCocycle 983)
        (orbitP14TargetCocycle_consistent 983) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1] (orbitP14RepresentativeCoeff 983)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_983))

theorem orbitP14_path_endpoint_984 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 984) = orbitP14TargetCoeff 984 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv984 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 984))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 984)) ≃*
      CocycleGroup (orbitP14TargetCocycle 984)
        (orbitP14TargetCocycle_consistent 984) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 984)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_984))

theorem orbitP14_path_endpoint_985 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 2, 1, 1, 2]
      (orbitP14RepresentativeCoeff 985) = orbitP14TargetCoeff 985 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv985 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 985))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 985)) ≃*
      CocycleGroup (orbitP14TargetCocycle 985)
        (orbitP14TargetCocycle_consistent 985) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 2, 1, 1, 2] (orbitP14RepresentativeCoeff 985)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_985))

theorem orbitP14_path_endpoint_986 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 1, 1, 0]
      (orbitP14RepresentativeCoeff 986) = orbitP14TargetCoeff 986 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv986 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 986))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 986)) ≃*
      CocycleGroup (orbitP14TargetCocycle 986)
        (orbitP14TargetCocycle_consistent 986) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 1, 1, 0] (orbitP14RepresentativeCoeff 986)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_986))

theorem orbitP14_path_endpoint_987 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 987) = orbitP14TargetCoeff 987 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv987 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 987))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 987)) ≃*
      CocycleGroup (orbitP14TargetCocycle 987)
        (orbitP14TargetCocycle_consistent 987) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 987)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_987))

theorem orbitP14_path_endpoint_988 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 988) = orbitP14TargetCoeff 988 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv988 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 988))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 988)) ≃*
      CocycleGroup (orbitP14TargetCocycle 988)
        (orbitP14TargetCocycle_consistent 988) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 988)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_988))

theorem orbitP14_path_endpoint_989 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 1]
      (orbitP14RepresentativeCoeff 989) = orbitP14TargetCoeff 989 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv989 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 989))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 989)) ≃*
      CocycleGroup (orbitP14TargetCocycle 989)
        (orbitP14TargetCocycle_consistent 989) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 1] (orbitP14RepresentativeCoeff 989)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_989))

theorem orbitP14_path_endpoint_990 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 990) = orbitP14TargetCoeff 990 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv990 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 990))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 990)) ≃*
      CocycleGroup (orbitP14TargetCocycle 990)
        (orbitP14TargetCocycle_consistent 990) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 990)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_990))

theorem orbitP14_path_endpoint_991 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 1, 1, 2]
      (orbitP14RepresentativeCoeff 991) = orbitP14TargetCoeff 991 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv991 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 991))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 991)) ≃*
      CocycleGroup (orbitP14TargetCocycle 991)
        (orbitP14TargetCocycle_consistent 991) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 1, 1, 2] (orbitP14RepresentativeCoeff 991)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_991))

end Smallgroups.UsefulTheorems.Order32Certificate
