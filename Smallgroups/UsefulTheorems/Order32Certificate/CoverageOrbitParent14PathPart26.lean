/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart25

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 26. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_400 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 400) = orbitP14TargetCoeff 400 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv400 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 400))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 400)) ≃*
      CocycleGroup (orbitP14TargetCocycle 400)
        (orbitP14TargetCocycle_consistent 400) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 400)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_400))

theorem orbitP14_path_endpoint_401 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 2, 0]
      (orbitP14RepresentativeCoeff 401) = orbitP14TargetCoeff 401 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv401 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 401))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 401)) ≃*
      CocycleGroup (orbitP14TargetCocycle 401)
        (orbitP14TargetCocycle_consistent 401) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 2, 0] (orbitP14RepresentativeCoeff 401)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_401))

theorem orbitP14_path_endpoint_402 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 0, 1, 1]
      (orbitP14RepresentativeCoeff 402) = orbitP14TargetCoeff 402 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv402 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 402))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 402)) ≃*
      CocycleGroup (orbitP14TargetCocycle 402)
        (orbitP14TargetCocycle_consistent 402) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 0, 1, 1] (orbitP14RepresentativeCoeff 402)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_402))

theorem orbitP14_path_endpoint_403 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 0, 1, 0, 2, 0, 1]
      (orbitP14RepresentativeCoeff 403) = orbitP14TargetCoeff 403 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv403 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 403))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 403)) ≃*
      CocycleGroup (orbitP14TargetCocycle 403)
        (orbitP14TargetCocycle_consistent 403) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 0, 1, 0, 2, 0, 1] (orbitP14RepresentativeCoeff 403)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_403))

theorem orbitP14_path_endpoint_404 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 0, 2, 0, 1, 2, 1, 0, 2, 1]
      (orbitP14RepresentativeCoeff 404) = orbitP14TargetCoeff 404 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv404 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 404))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 404)) ≃*
      CocycleGroup (orbitP14TargetCocycle 404)
        (orbitP14TargetCocycle_consistent 404) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 0, 2, 0, 1, 2, 1, 0, 2, 1] (orbitP14RepresentativeCoeff 404)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_404))

theorem orbitP14_path_endpoint_405 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 1, 2]
      (orbitP14RepresentativeCoeff 405) = orbitP14TargetCoeff 405 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv405 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 405))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 405)) ≃*
      CocycleGroup (orbitP14TargetCocycle 405)
        (orbitP14TargetCocycle_consistent 405) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 1, 2] (orbitP14RepresentativeCoeff 405)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_405))

theorem orbitP14_path_endpoint_406 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 0, 2, 0, 1, 1]
      (orbitP14RepresentativeCoeff 406) = orbitP14TargetCoeff 406 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv406 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 406))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 406)) ≃*
      CocycleGroup (orbitP14TargetCocycle 406)
        (orbitP14TargetCocycle_consistent 406) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 0, 2, 0, 1, 1] (orbitP14RepresentativeCoeff 406)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_406))

theorem orbitP14_path_endpoint_407 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 407) = orbitP14TargetCoeff 407 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv407 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 407))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 407)) ≃*
      CocycleGroup (orbitP14TargetCocycle 407)
        (orbitP14TargetCocycle_consistent 407) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 407)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_407))

theorem orbitP14_path_endpoint_408 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1]
      (orbitP14RepresentativeCoeff 408) = orbitP14TargetCoeff 408 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv408 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 408))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 408)) ≃*
      CocycleGroup (orbitP14TargetCocycle 408)
        (orbitP14TargetCocycle_consistent 408) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1] (orbitP14RepresentativeCoeff 408)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_408))

theorem orbitP14_path_endpoint_409 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 0, 2]
      (orbitP14RepresentativeCoeff 409) = orbitP14TargetCoeff 409 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv409 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 409))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 409)) ≃*
      CocycleGroup (orbitP14TargetCocycle 409)
        (orbitP14TargetCocycle_consistent 409) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 0, 2] (orbitP14RepresentativeCoeff 409)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_409))

theorem orbitP14_path_endpoint_410 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 410) = orbitP14TargetCoeff 410 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv410 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 410))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 410)) ≃*
      CocycleGroup (orbitP14TargetCocycle 410)
        (orbitP14TargetCocycle_consistent 410) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 410)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_410))

theorem orbitP14_path_endpoint_411 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 0, 2, 1, 1]
      (orbitP14RepresentativeCoeff 411) = orbitP14TargetCoeff 411 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv411 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 411))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 411)) ≃*
      CocycleGroup (orbitP14TargetCocycle 411)
        (orbitP14TargetCocycle_consistent 411) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 0, 2, 1, 1] (orbitP14RepresentativeCoeff 411)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_411))

theorem orbitP14_path_endpoint_412 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 2, 1]
      (orbitP14RepresentativeCoeff 412) = orbitP14TargetCoeff 412 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv412 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 412))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 412)) ≃*
      CocycleGroup (orbitP14TargetCocycle 412)
        (orbitP14TargetCocycle_consistent 412) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 2, 1] (orbitP14RepresentativeCoeff 412)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_412))

theorem orbitP14_path_endpoint_413 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 0]
      (orbitP14RepresentativeCoeff 413) = orbitP14TargetCoeff 413 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv413 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 413))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 413)) ≃*
      CocycleGroup (orbitP14TargetCocycle 413)
        (orbitP14TargetCocycle_consistent 413) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 0] (orbitP14RepresentativeCoeff 413)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_413))

theorem orbitP14_path_endpoint_414 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 414) = orbitP14TargetCoeff 414 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv414 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 414))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 414)) ≃*
      CocycleGroup (orbitP14TargetCocycle 414)
        (orbitP14TargetCocycle_consistent 414) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 414)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_414))

theorem orbitP14_path_endpoint_415 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 1, 2, 0, 1, 1, 1, 2]
      (orbitP14RepresentativeCoeff 415) = orbitP14TargetCoeff 415 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv415 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 415))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 415)) ≃*
      CocycleGroup (orbitP14TargetCocycle 415)
        (orbitP14TargetCocycle_consistent 415) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 1, 2, 0, 1, 1, 1, 2] (orbitP14RepresentativeCoeff 415)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_415))

end Smallgroups.UsefulTheorems.Order32Certificate
