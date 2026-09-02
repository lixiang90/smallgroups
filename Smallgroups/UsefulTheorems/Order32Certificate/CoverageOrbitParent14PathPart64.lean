/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart63

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 64. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_1008 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1]
      (orbitP14RepresentativeCoeff 1008) = orbitP14TargetCoeff 1008 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv1008 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 1008))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 1008)) ≃*
      CocycleGroup (orbitP14TargetCocycle 1008)
        (orbitP14TargetCocycle_consistent 1008) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1] (orbitP14RepresentativeCoeff 1008)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_1008))

theorem orbitP14_path_endpoint_1009 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 2, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 1009) = orbitP14TargetCoeff 1009 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv1009 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 1009))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 1009)) ≃*
      CocycleGroup (orbitP14TargetCocycle 1009)
        (orbitP14TargetCocycle_consistent 1009) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 2, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 1009)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_1009))

theorem orbitP14_path_endpoint_1010 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 1010) = orbitP14TargetCoeff 1010 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv1010 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 1010))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 1010)) ≃*
      CocycleGroup (orbitP14TargetCocycle 1010)
        (orbitP14TargetCocycle_consistent 1010) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 1010)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_1010))

theorem orbitP14_path_endpoint_1011 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 1, 2, 1]
      (orbitP14RepresentativeCoeff 1011) = orbitP14TargetCoeff 1011 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv1011 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 1011))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 1011)) ≃*
      CocycleGroup (orbitP14TargetCocycle 1011)
        (orbitP14TargetCocycle_consistent 1011) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 1, 2, 1] (orbitP14RepresentativeCoeff 1011)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_1011))

theorem orbitP14_path_endpoint_1012 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 1012) = orbitP14TargetCoeff 1012 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv1012 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 1012))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 1012)) ≃*
      CocycleGroup (orbitP14TargetCocycle 1012)
        (orbitP14TargetCocycle_consistent 1012) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 1012)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_1012))

theorem orbitP14_path_endpoint_1013 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 1013) = orbitP14TargetCoeff 1013 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv1013 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 1013))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 1013)) ≃*
      CocycleGroup (orbitP14TargetCocycle 1013)
        (orbitP14TargetCocycle_consistent 1013) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 1013)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_1013))

theorem orbitP14_path_endpoint_1014 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 2, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 1014) = orbitP14TargetCoeff 1014 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv1014 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 1014))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 1014)) ≃*
      CocycleGroup (orbitP14TargetCocycle 1014)
        (orbitP14TargetCocycle_consistent 1014) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 2, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 1014)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_1014))

theorem orbitP14_path_endpoint_1015 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 2, 1, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 1015) = orbitP14TargetCoeff 1015 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv1015 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 1015))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 1015)) ≃*
      CocycleGroup (orbitP14TargetCocycle 1015)
        (orbitP14TargetCocycle_consistent 1015) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 2, 1, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 1015)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_1015))

theorem orbitP14_path_endpoint_1016 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 1, 0, 1]
      (orbitP14RepresentativeCoeff 1016) = orbitP14TargetCoeff 1016 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv1016 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 1016))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 1016)) ≃*
      CocycleGroup (orbitP14TargetCocycle 1016)
        (orbitP14TargetCocycle_consistent 1016) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 1, 0, 1] (orbitP14RepresentativeCoeff 1016)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_1016))

theorem orbitP14_path_endpoint_1017 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 1017) = orbitP14TargetCoeff 1017 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv1017 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 1017))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 1017)) ≃*
      CocycleGroup (orbitP14TargetCocycle 1017)
        (orbitP14TargetCocycle_consistent 1017) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 1017)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_1017))

theorem orbitP14_path_endpoint_1018 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 1018) = orbitP14TargetCoeff 1018 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv1018 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 1018))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 1018)) ≃*
      CocycleGroup (orbitP14TargetCocycle 1018)
        (orbitP14TargetCocycle_consistent 1018) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 1018)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_1018))

theorem orbitP14_path_endpoint_1019 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 2]
      (orbitP14RepresentativeCoeff 1019) = orbitP14TargetCoeff 1019 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv1019 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 1019))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 1019)) ≃*
      CocycleGroup (orbitP14TargetCocycle 1019)
        (orbitP14TargetCocycle_consistent 1019) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 2] (orbitP14RepresentativeCoeff 1019)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_1019))

theorem orbitP14_path_endpoint_1020 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 1020) = orbitP14TargetCoeff 1020 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv1020 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 1020))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 1020)) ≃*
      CocycleGroup (orbitP14TargetCocycle 1020)
        (orbitP14TargetCocycle_consistent 1020) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 1020)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_1020))

theorem orbitP14_path_endpoint_1021 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 1021) = orbitP14TargetCoeff 1021 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv1021 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 1021))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 1021)) ≃*
      CocycleGroup (orbitP14TargetCocycle 1021)
        (orbitP14TargetCocycle_consistent 1021) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 2, 0] (orbitP14RepresentativeCoeff 1021)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_1021))

theorem orbitP14_path_endpoint_1022 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 1, 2, 1, 2, 1]
      (orbitP14RepresentativeCoeff 1022) = orbitP14TargetCoeff 1022 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv1022 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 1022))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 1022)) ≃*
      CocycleGroup (orbitP14TargetCocycle 1022)
        (orbitP14TargetCocycle_consistent 1022) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 1, 2, 1, 2, 1] (orbitP14RepresentativeCoeff 1022)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_1022))

theorem orbitP14_path_endpoint_1023 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 1, 2, 1, 2]
      (orbitP14RepresentativeCoeff 1023) = orbitP14TargetCoeff 1023 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv1023 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 1023))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 1023)) ≃*
      CocycleGroup (orbitP14TargetCocycle 1023)
        (orbitP14TargetCocycle_consistent 1023) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 1, 2, 1, 2] (orbitP14RepresentativeCoeff 1023)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_1023))

end Smallgroups.UsefulTheorems.Order32Certificate
