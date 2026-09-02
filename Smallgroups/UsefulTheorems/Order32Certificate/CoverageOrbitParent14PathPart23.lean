/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart22

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 23. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_352 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 1, 2, 0, 1, 1]
      (orbitP14RepresentativeCoeff 352) = orbitP14TargetCoeff 352 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv352 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 352))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 352)) ≃*
      CocycleGroup (orbitP14TargetCocycle 352)
        (orbitP14TargetCocycle_consistent 352) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 1, 2, 0, 1, 1] (orbitP14RepresentativeCoeff 352)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_352))

theorem orbitP14_path_endpoint_353 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 353) = orbitP14TargetCoeff 353 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv353 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 353))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 353)) ≃*
      CocycleGroup (orbitP14TargetCocycle 353)
        (orbitP14TargetCocycle_consistent 353) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 353)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_353))

theorem orbitP14_path_endpoint_354 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1]
      (orbitP14RepresentativeCoeff 354) = orbitP14TargetCoeff 354 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv354 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 354))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 354)) ≃*
      CocycleGroup (orbitP14TargetCocycle 354)
        (orbitP14TargetCocycle_consistent 354) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1] (orbitP14RepresentativeCoeff 354)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_354))

theorem orbitP14_path_endpoint_355 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1]
      (orbitP14RepresentativeCoeff 355) = orbitP14TargetCoeff 355 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv355 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 355))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 355)) ≃*
      CocycleGroup (orbitP14TargetCocycle 355)
        (orbitP14TargetCocycle_consistent 355) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1] (orbitP14RepresentativeCoeff 355)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_355))

theorem orbitP14_path_endpoint_356 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0]
      (orbitP14RepresentativeCoeff 356) = orbitP14TargetCoeff 356 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv356 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 356))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 356)) ≃*
      CocycleGroup (orbitP14TargetCocycle 356)
        (orbitP14TargetCocycle_consistent 356) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0] (orbitP14RepresentativeCoeff 356)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_356))

theorem orbitP14_path_endpoint_357 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0]
      (orbitP14RepresentativeCoeff 357) = orbitP14TargetCoeff 357 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv357 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 357))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 357)) ≃*
      CocycleGroup (orbitP14TargetCocycle 357)
        (orbitP14TargetCocycle_consistent 357) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0] (orbitP14RepresentativeCoeff 357)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_357))

theorem orbitP14_path_endpoint_358 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 0, 2, 0, 1, 2, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 358) = orbitP14TargetCoeff 358 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv358 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 358))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 358)) ≃*
      CocycleGroup (orbitP14TargetCocycle 358)
        (orbitP14TargetCocycle_consistent 358) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 0, 2, 0, 1, 2, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 358)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_358))

theorem orbitP14_path_endpoint_359 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 2, 1, 2, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 359) = orbitP14TargetCoeff 359 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv359 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 359))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 359)) ≃*
      CocycleGroup (orbitP14TargetCocycle 359)
        (orbitP14TargetCocycle_consistent 359) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 2, 1, 2, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 359)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_359))

theorem orbitP14_path_endpoint_360 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 360) = orbitP14TargetCoeff 360 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv360 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 360))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 360)) ≃*
      CocycleGroup (orbitP14TargetCocycle 360)
        (orbitP14TargetCocycle_consistent 360) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 360)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_360))

theorem orbitP14_path_endpoint_361 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 1, 0, 2, 1]
      (orbitP14RepresentativeCoeff 361) = orbitP14TargetCoeff 361 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv361 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 361))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 361)) ≃*
      CocycleGroup (orbitP14TargetCocycle 361)
        (orbitP14TargetCocycle_consistent 361) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 1, 0, 2, 1] (orbitP14RepresentativeCoeff 361)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_361))

theorem orbitP14_path_endpoint_362 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 1, 2, 1, 1, 2]
      (orbitP14RepresentativeCoeff 362) = orbitP14TargetCoeff 362 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv362 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 362))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 362)) ≃*
      CocycleGroup (orbitP14TargetCocycle 362)
        (orbitP14TargetCocycle_consistent 362) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 1, 2, 1, 1, 2] (orbitP14RepresentativeCoeff 362)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_362))

theorem orbitP14_path_endpoint_363 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 1, 2, 0, 1, 1, 2]
      (orbitP14RepresentativeCoeff 363) = orbitP14TargetCoeff 363 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv363 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 363))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 363)) ≃*
      CocycleGroup (orbitP14TargetCocycle 363)
        (orbitP14TargetCocycle_consistent 363) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 1, 2, 0, 1, 1, 2] (orbitP14RepresentativeCoeff 363)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_363))

theorem orbitP14_path_endpoint_364 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 1, 2, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 364) = orbitP14TargetCoeff 364 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv364 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 364))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 364)) ≃*
      CocycleGroup (orbitP14TargetCocycle 364)
        (orbitP14TargetCocycle_consistent 364) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 1, 2, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 364)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_364))

theorem orbitP14_path_endpoint_365 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 1, 2, 1, 1, 2, 1]
      (orbitP14RepresentativeCoeff 365) = orbitP14TargetCoeff 365 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv365 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 365))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 365)) ≃*
      CocycleGroup (orbitP14TargetCocycle 365)
        (orbitP14TargetCocycle_consistent 365) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 1, 2, 1, 1, 2, 1] (orbitP14RepresentativeCoeff 365)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_365))

theorem orbitP14_path_endpoint_366 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 2]
      (orbitP14RepresentativeCoeff 366) = orbitP14TargetCoeff 366 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv366 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 366))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 366)) ≃*
      CocycleGroup (orbitP14TargetCocycle 366)
        (orbitP14TargetCocycle_consistent 366) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 2] (orbitP14RepresentativeCoeff 366)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_366))

theorem orbitP14_path_endpoint_367 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 0, 2]
      (orbitP14RepresentativeCoeff 367) = orbitP14TargetCoeff 367 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv367 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 367))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 367)) ≃*
      CocycleGroup (orbitP14TargetCocycle 367)
        (orbitP14TargetCocycle_consistent 367) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 0, 2] (orbitP14RepresentativeCoeff 367)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_367))

end Smallgroups.UsefulTheorems.Order32Certificate
