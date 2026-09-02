/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart19

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 20. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_304 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 0, 1, 0, 1]
      (orbitP14RepresentativeCoeff 304) = orbitP14TargetCoeff 304 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv304 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 304))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 304)) ≃*
      CocycleGroup (orbitP14TargetCocycle 304)
        (orbitP14TargetCocycle_consistent 304) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 0, 1, 0, 1] (orbitP14RepresentativeCoeff 304)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_304))

theorem orbitP14_path_endpoint_305 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 2, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 305) = orbitP14TargetCoeff 305 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv305 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 305))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 305)) ≃*
      CocycleGroup (orbitP14TargetCocycle 305)
        (orbitP14TargetCocycle_consistent 305) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 2, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 305)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_305))

theorem orbitP14_path_endpoint_306 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 1, 1, 1]
      (orbitP14RepresentativeCoeff 306) = orbitP14TargetCoeff 306 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv306 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 306))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 306)) ≃*
      CocycleGroup (orbitP14TargetCocycle 306)
        (orbitP14TargetCocycle_consistent 306) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 1, 1, 1] (orbitP14RepresentativeCoeff 306)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_306))

theorem orbitP14_path_endpoint_307 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 307) = orbitP14TargetCoeff 307 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv307 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 307))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 307)) ≃*
      CocycleGroup (orbitP14TargetCocycle 307)
        (orbitP14TargetCocycle_consistent 307) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 307)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_307))

theorem orbitP14_path_endpoint_308 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 2, 0, 1, 2, 1, 1, 0, 2]
      (orbitP14RepresentativeCoeff 308) = orbitP14TargetCoeff 308 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv308 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 308))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 308)) ≃*
      CocycleGroup (orbitP14TargetCocycle 308)
        (orbitP14TargetCocycle_consistent 308) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 2, 0, 1, 2, 1, 1, 0, 2] (orbitP14RepresentativeCoeff 308)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_308))

theorem orbitP14_path_endpoint_309 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 0, 1, 0, 2, 0]
      (orbitP14RepresentativeCoeff 309) = orbitP14TargetCoeff 309 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv309 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 309))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 309)) ≃*
      CocycleGroup (orbitP14TargetCocycle 309)
        (orbitP14TargetCocycle_consistent 309) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 0, 1, 0, 2, 0] (orbitP14RepresentativeCoeff 309)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_309))

theorem orbitP14_path_endpoint_310 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 0, 1, 1]
      (orbitP14RepresentativeCoeff 310) = orbitP14TargetCoeff 310 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv310 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 310))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 310)) ≃*
      CocycleGroup (orbitP14TargetCocycle 310)
        (orbitP14TargetCocycle_consistent 310) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 0, 1, 1] (orbitP14RepresentativeCoeff 310)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_310))

theorem orbitP14_path_endpoint_311 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1]
      (orbitP14RepresentativeCoeff 311) = orbitP14TargetCoeff 311 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv311 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 311))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 311)) ≃*
      CocycleGroup (orbitP14TargetCocycle 311)
        (orbitP14TargetCocycle_consistent 311) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1] (orbitP14RepresentativeCoeff 311)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_311))

theorem orbitP14_path_endpoint_312 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1]
      (orbitP14RepresentativeCoeff 312) = orbitP14TargetCoeff 312 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv312 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 312))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 312)) ≃*
      CocycleGroup (orbitP14TargetCocycle 312)
        (orbitP14TargetCocycle_consistent 312) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1] (orbitP14RepresentativeCoeff 312)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_312))

theorem orbitP14_path_endpoint_313 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 1, 1, 0]
      (orbitP14RepresentativeCoeff 313) = orbitP14TargetCoeff 313 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv313 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 313))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 313)) ≃*
      CocycleGroup (orbitP14TargetCocycle 313)
        (orbitP14TargetCocycle_consistent 313) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 1, 1, 0] (orbitP14RepresentativeCoeff 313)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_313))

theorem orbitP14_path_endpoint_314 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 2, 1, 2]
      (orbitP14RepresentativeCoeff 314) = orbitP14TargetCoeff 314 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv314 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 314))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 314)) ≃*
      CocycleGroup (orbitP14TargetCocycle 314)
        (orbitP14TargetCocycle_consistent 314) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 2, 1, 2] (orbitP14RepresentativeCoeff 314)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_314))

theorem orbitP14_path_endpoint_315 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 315) = orbitP14TargetCoeff 315 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv315 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 315))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 315)) ≃*
      CocycleGroup (orbitP14TargetCocycle 315)
        (orbitP14TargetCocycle_consistent 315) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 315)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_315))

theorem orbitP14_path_endpoint_316 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 1]
      (orbitP14RepresentativeCoeff 316) = orbitP14TargetCoeff 316 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv316 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 316))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 316)) ≃*
      CocycleGroup (orbitP14TargetCocycle 316)
        (orbitP14TargetCocycle_consistent 316) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 1] (orbitP14RepresentativeCoeff 316)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_316))

theorem orbitP14_path_endpoint_317 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 1, 1]
      (orbitP14RepresentativeCoeff 317) = orbitP14TargetCoeff 317 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv317 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 317))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 317)) ≃*
      CocycleGroup (orbitP14TargetCocycle 317)
        (orbitP14TargetCocycle_consistent 317) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 1, 1] (orbitP14RepresentativeCoeff 317)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_317))

theorem orbitP14_path_endpoint_318 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 0, 2, 0, 1, 2, 1, 2]
      (orbitP14RepresentativeCoeff 318) = orbitP14TargetCoeff 318 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv318 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 318))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 318)) ≃*
      CocycleGroup (orbitP14TargetCocycle 318)
        (orbitP14TargetCocycle_consistent 318) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 0, 2, 0, 1, 2, 1, 2] (orbitP14RepresentativeCoeff 318)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_318))

theorem orbitP14_path_endpoint_319 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 0, 1, 0, 2, 1]
      (orbitP14RepresentativeCoeff 319) = orbitP14TargetCoeff 319 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv319 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 319))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 319)) ≃*
      CocycleGroup (orbitP14TargetCocycle 319)
        (orbitP14TargetCocycle_consistent 319) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 0, 1, 0, 2, 1] (orbitP14RepresentativeCoeff 319)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_319))

end Smallgroups.UsefulTheorems.Order32Certificate
