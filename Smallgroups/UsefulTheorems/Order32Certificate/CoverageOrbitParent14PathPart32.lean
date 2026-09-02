/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart31

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 32. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_496 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 1]
      (orbitP14RepresentativeCoeff 496) = orbitP14TargetCoeff 496 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv496 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 496))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 496)) ≃*
      CocycleGroup (orbitP14TargetCocycle 496)
        (orbitP14TargetCocycle_consistent 496) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 1] (orbitP14RepresentativeCoeff 496)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_496))

theorem orbitP14_path_endpoint_497 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 1]
      (orbitP14RepresentativeCoeff 497) = orbitP14TargetCoeff 497 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv497 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 497))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 497)) ≃*
      CocycleGroup (orbitP14TargetCocycle 497)
        (orbitP14TargetCocycle_consistent 497) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 1] (orbitP14RepresentativeCoeff 497)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_497))

theorem orbitP14_path_endpoint_498 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 0, 1, 0, 2, 1, 1, 0]
      (orbitP14RepresentativeCoeff 498) = orbitP14TargetCoeff 498 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv498 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 498))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 498)) ≃*
      CocycleGroup (orbitP14TargetCocycle 498)
        (orbitP14TargetCocycle_consistent 498) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 0, 1, 0, 2, 1, 1, 0] (orbitP14RepresentativeCoeff 498)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_498))

theorem orbitP14_path_endpoint_499 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 0, 1, 0, 2]
      (orbitP14RepresentativeCoeff 499) = orbitP14TargetCoeff 499 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv499 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 499))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 499)) ≃*
      CocycleGroup (orbitP14TargetCocycle 499)
        (orbitP14TargetCocycle_consistent 499) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 0, 1, 0, 2] (orbitP14RepresentativeCoeff 499)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_499))

theorem orbitP14_path_endpoint_500 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 0, 1, 0, 2, 1, 1]
      (orbitP14RepresentativeCoeff 500) = orbitP14TargetCoeff 500 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv500 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 500))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 500)) ≃*
      CocycleGroup (orbitP14TargetCocycle 500)
        (orbitP14TargetCocycle_consistent 500) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 0, 1, 0, 2, 1, 1] (orbitP14RepresentativeCoeff 500)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_500))

theorem orbitP14_path_endpoint_501 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 0, 1, 0, 2, 0]
      (orbitP14RepresentativeCoeff 501) = orbitP14TargetCoeff 501 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv501 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 501))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 501)) ≃*
      CocycleGroup (orbitP14TargetCocycle 501)
        (orbitP14TargetCocycle_consistent 501) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 0, 1, 0, 2, 0] (orbitP14RepresentativeCoeff 501)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_501))

theorem orbitP14_path_endpoint_502 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 0, 1, 2, 1, 0, 1]
      (orbitP14RepresentativeCoeff 502) = orbitP14TargetCoeff 502 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv502 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 502))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 502)) ≃*
      CocycleGroup (orbitP14TargetCocycle 502)
        (orbitP14TargetCocycle_consistent 502) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 0, 1, 2, 1, 0, 1] (orbitP14RepresentativeCoeff 502)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_502))

theorem orbitP14_path_endpoint_503 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 1, 1, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 503) = orbitP14TargetCoeff 503 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv503 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 503))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 503)) ≃*
      CocycleGroup (orbitP14TargetCocycle 503)
        (orbitP14TargetCocycle_consistent 503) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 1, 1, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 503)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_503))

theorem orbitP14_path_endpoint_504 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 0, 1, 0, 2]
      (orbitP14RepresentativeCoeff 504) = orbitP14TargetCoeff 504 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv504 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 504))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 504)) ≃*
      CocycleGroup (orbitP14TargetCocycle 504)
        (orbitP14TargetCocycle_consistent 504) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 0, 1, 0, 2] (orbitP14RepresentativeCoeff 504)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_504))

theorem orbitP14_path_endpoint_505 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 0, 2, 1, 2, 1, 0, 2]
      (orbitP14RepresentativeCoeff 505) = orbitP14TargetCoeff 505 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv505 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 505))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 505)) ≃*
      CocycleGroup (orbitP14TargetCocycle 505)
        (orbitP14TargetCocycle_consistent 505) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 0, 2, 1, 2, 1, 0, 2] (orbitP14RepresentativeCoeff 505)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_505))

theorem orbitP14_path_endpoint_506 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 1, 0, 2]
      (orbitP14RepresentativeCoeff 506) = orbitP14TargetCoeff 506 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv506 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 506))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 506)) ≃*
      CocycleGroup (orbitP14TargetCocycle 506)
        (orbitP14TargetCocycle_consistent 506) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 1, 0, 2] (orbitP14RepresentativeCoeff 506)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_506))

theorem orbitP14_path_endpoint_507 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 0, 1, 1, 0, 2]
      (orbitP14RepresentativeCoeff 507) = orbitP14TargetCoeff 507 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv507 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 507))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 507)) ≃*
      CocycleGroup (orbitP14TargetCocycle 507)
        (orbitP14TargetCocycle_consistent 507) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 0, 1, 1, 0, 2] (orbitP14RepresentativeCoeff 507)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_507))

theorem orbitP14_path_endpoint_508 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 1, 0, 2, 0]
      (orbitP14RepresentativeCoeff 508) = orbitP14TargetCoeff 508 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv508 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 508))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 508)) ≃*
      CocycleGroup (orbitP14TargetCocycle 508)
        (orbitP14TargetCocycle_consistent 508) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 1, 0, 2, 0] (orbitP14RepresentativeCoeff 508)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_508))

theorem orbitP14_path_endpoint_509 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 1, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 509) = orbitP14TargetCoeff 509 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv509 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 509))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 509)) ≃*
      CocycleGroup (orbitP14TargetCocycle 509)
        (orbitP14TargetCocycle_consistent 509) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 1, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 509)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_509))

theorem orbitP14_path_endpoint_510 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 2, 1, 1]
      (orbitP14RepresentativeCoeff 510) = orbitP14TargetCoeff 510 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv510 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 510))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 510)) ≃*
      CocycleGroup (orbitP14TargetCocycle 510)
        (orbitP14TargetCocycle_consistent 510) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 2, 1, 1] (orbitP14RepresentativeCoeff 510)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_510))

theorem orbitP14_path_endpoint_511 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 1, 2, 1, 0, 2, 1, 2]
      (orbitP14RepresentativeCoeff 511) = orbitP14TargetCoeff 511 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv511 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 511))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 511)) ≃*
      CocycleGroup (orbitP14TargetCocycle 511)
        (orbitP14TargetCocycle_consistent 511) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 1, 2, 1, 0, 2, 1, 2] (orbitP14RepresentativeCoeff 511)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_511))

end Smallgroups.UsefulTheorems.Order32Certificate
