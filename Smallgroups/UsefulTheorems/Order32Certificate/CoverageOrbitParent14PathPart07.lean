/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart06

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 7. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_96 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 96) = orbitP14TargetCoeff 96 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv96 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 96))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 96)) ≃*
      CocycleGroup (orbitP14TargetCocycle 96)
        (orbitP14TargetCocycle_consistent 96) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 96)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_96))

theorem orbitP14_path_endpoint_97 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 2, 1, 2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 97) = orbitP14TargetCoeff 97 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv97 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 97))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 97)) ≃*
      CocycleGroup (orbitP14TargetCocycle 97)
        (orbitP14TargetCocycle_consistent 97) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 2, 1, 2, 0, 1, 2] (orbitP14RepresentativeCoeff 97)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_97))

theorem orbitP14_path_endpoint_98 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 98) = orbitP14TargetCoeff 98 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv98 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 98))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 98)) ≃*
      CocycleGroup (orbitP14TargetCocycle 98)
        (orbitP14TargetCocycle_consistent 98) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 2] (orbitP14RepresentativeCoeff 98)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_98))

theorem orbitP14_path_endpoint_99 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 1, 2, 1, 2, 0, 1, 1, 2]
      (orbitP14RepresentativeCoeff 99) = orbitP14TargetCoeff 99 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv99 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 99))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 99)) ≃*
      CocycleGroup (orbitP14TargetCocycle 99)
        (orbitP14TargetCocycle_consistent 99) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 1, 2, 1, 2, 0, 1, 1, 2] (orbitP14RepresentativeCoeff 99)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_99))

theorem orbitP14_path_endpoint_100 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 0, 2, 0]
      (orbitP14RepresentativeCoeff 100) = orbitP14TargetCoeff 100 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv100 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 100))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 100)) ≃*
      CocycleGroup (orbitP14TargetCocycle 100)
        (orbitP14TargetCocycle_consistent 100) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 0, 2, 0] (orbitP14RepresentativeCoeff 100)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_100))

theorem orbitP14_path_endpoint_101 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 101) = orbitP14TargetCoeff 101 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv101 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 101))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 101)) ≃*
      CocycleGroup (orbitP14TargetCocycle 101)
        (orbitP14TargetCocycle_consistent 101) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 101)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_101))

theorem orbitP14_path_endpoint_102 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1]
      (orbitP14RepresentativeCoeff 102) = orbitP14TargetCoeff 102 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv102 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 102))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 102)) ≃*
      CocycleGroup (orbitP14TargetCocycle 102)
        (orbitP14TargetCocycle_consistent 102) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1] (orbitP14RepresentativeCoeff 102)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_102))

theorem orbitP14_path_endpoint_103 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 1]
      (orbitP14RepresentativeCoeff 103) = orbitP14TargetCoeff 103 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv103 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 103))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 103)) ≃*
      CocycleGroup (orbitP14TargetCocycle 103)
        (orbitP14TargetCocycle_consistent 103) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 1] (orbitP14RepresentativeCoeff 103)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_103))

theorem orbitP14_path_endpoint_104 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 1]
      (orbitP14RepresentativeCoeff 104) = orbitP14TargetCoeff 104 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv104 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 104))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 104)) ≃*
      CocycleGroup (orbitP14TargetCocycle 104)
        (orbitP14TargetCocycle_consistent 104) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 1] (orbitP14RepresentativeCoeff 104)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_104))

theorem orbitP14_path_endpoint_105 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1]
      (orbitP14RepresentativeCoeff 105) = orbitP14TargetCoeff 105 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv105 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 105))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 105)) ≃*
      CocycleGroup (orbitP14TargetCocycle 105)
        (orbitP14TargetCocycle_consistent 105) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1] (orbitP14RepresentativeCoeff 105)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_105))

theorem orbitP14_path_endpoint_106 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 1, 0]
      (orbitP14RepresentativeCoeff 106) = orbitP14TargetCoeff 106 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv106 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 106))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 106)) ≃*
      CocycleGroup (orbitP14TargetCocycle 106)
        (orbitP14TargetCocycle_consistent 106) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 1, 0] (orbitP14RepresentativeCoeff 106)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_106))

theorem orbitP14_path_endpoint_107 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 107) = orbitP14TargetCoeff 107 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv107 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 107))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 107)) ≃*
      CocycleGroup (orbitP14TargetCocycle 107)
        (orbitP14TargetCocycle_consistent 107) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 0] (orbitP14RepresentativeCoeff 107)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_107))

theorem orbitP14_path_endpoint_108 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 1, 0]
      (orbitP14RepresentativeCoeff 108) = orbitP14TargetCoeff 108 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv108 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 108))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 108)) ≃*
      CocycleGroup (orbitP14TargetCocycle 108)
        (orbitP14TargetCocycle_consistent 108) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 1, 0] (orbitP14RepresentativeCoeff 108)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_108))

theorem orbitP14_path_endpoint_109 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 2, 1, 2, 0, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 109) = orbitP14TargetCoeff 109 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv109 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 109))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 109)) ≃*
      CocycleGroup (orbitP14TargetCocycle 109)
        (orbitP14TargetCocycle_consistent 109) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 2, 1, 2, 0, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 109)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_109))

theorem orbitP14_path_endpoint_110 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 2, 1, 2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 110) = orbitP14TargetCoeff 110 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv110 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 110))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 110)) ≃*
      CocycleGroup (orbitP14TargetCocycle 110)
        (orbitP14TargetCocycle_consistent 110) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 2, 1, 2, 0, 1, 2] (orbitP14RepresentativeCoeff 110)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_110))

theorem orbitP14_path_endpoint_111 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 111) = orbitP14TargetCoeff 111 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv111 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 111))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 111)) ≃*
      CocycleGroup (orbitP14TargetCocycle 111)
        (orbitP14TargetCocycle_consistent 111) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 111)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_111))

end Smallgroups.UsefulTheorems.Order32Certificate
