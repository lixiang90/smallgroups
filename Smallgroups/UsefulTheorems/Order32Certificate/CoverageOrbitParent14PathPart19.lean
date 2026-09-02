/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart18

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 19. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_288 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 1]
      (orbitP14RepresentativeCoeff 288) = orbitP14TargetCoeff 288 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv288 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 288))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 288)) ≃*
      CocycleGroup (orbitP14TargetCocycle 288)
        (orbitP14TargetCocycle_consistent 288) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 1] (orbitP14RepresentativeCoeff 288)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_288))

theorem orbitP14_path_endpoint_289 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 2, 1, 2, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 289) = orbitP14TargetCoeff 289 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv289 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 289))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 289)) ≃*
      CocycleGroup (orbitP14TargetCocycle 289)
        (orbitP14TargetCocycle_consistent 289) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 2, 1, 2, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 289)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_289))

theorem orbitP14_path_endpoint_290 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 0, 2]
      (orbitP14RepresentativeCoeff 290) = orbitP14TargetCoeff 290 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv290 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 290))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 290)) ≃*
      CocycleGroup (orbitP14TargetCocycle 290)
        (orbitP14TargetCocycle_consistent 290) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 0, 2] (orbitP14RepresentativeCoeff 290)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_290))

theorem orbitP14_path_endpoint_291 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 291) = orbitP14TargetCoeff 291 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv291 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 291))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 291)) ≃*
      CocycleGroup (orbitP14TargetCocycle 291)
        (orbitP14TargetCocycle_consistent 291) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 291)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_291))

theorem orbitP14_path_endpoint_292 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 292) = orbitP14TargetCoeff 292 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv292 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 292))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 292)) ≃*
      CocycleGroup (orbitP14TargetCocycle 292)
        (orbitP14TargetCocycle_consistent 292) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 292)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_292))

theorem orbitP14_path_endpoint_293 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 1, 2, 1, 2, 0, 1, 1, 2, 0]
      (orbitP14RepresentativeCoeff 293) = orbitP14TargetCoeff 293 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv293 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 293))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 293)) ≃*
      CocycleGroup (orbitP14TargetCocycle 293)
        (orbitP14TargetCocycle_consistent 293) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 1, 2, 1, 2, 0, 1, 1, 2, 0] (orbitP14RepresentativeCoeff 293)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_293))

theorem orbitP14_path_endpoint_294 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1]
      (orbitP14RepresentativeCoeff 294) = orbitP14TargetCoeff 294 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv294 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 294))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 294)) ≃*
      CocycleGroup (orbitP14TargetCocycle 294)
        (orbitP14TargetCocycle_consistent 294) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1] (orbitP14RepresentativeCoeff 294)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_294))

theorem orbitP14_path_endpoint_295 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 1, 2]
      (orbitP14RepresentativeCoeff 295) = orbitP14TargetCoeff 295 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv295 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 295))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 295)) ≃*
      CocycleGroup (orbitP14TargetCocycle 295)
        (orbitP14TargetCocycle_consistent 295) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 1, 2] (orbitP14RepresentativeCoeff 295)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_295))

theorem orbitP14_path_endpoint_296 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 1, 1]
      (orbitP14RepresentativeCoeff 296) = orbitP14TargetCoeff 296 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv296 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 296))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 296)) ≃*
      CocycleGroup (orbitP14TargetCocycle 296)
        (orbitP14TargetCocycle_consistent 296) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 1, 1] (orbitP14RepresentativeCoeff 296)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_296))

theorem orbitP14_path_endpoint_297 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 0]
      (orbitP14RepresentativeCoeff 297) = orbitP14TargetCoeff 297 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv297 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 297))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 297)) ≃*
      CocycleGroup (orbitP14TargetCocycle 297)
        (orbitP14TargetCocycle_consistent 297) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 0] (orbitP14RepresentativeCoeff 297)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_297))

theorem orbitP14_path_endpoint_298 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 298) = orbitP14TargetCoeff 298 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv298 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 298))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 298)) ≃*
      CocycleGroup (orbitP14TargetCocycle 298)
        (orbitP14TargetCocycle_consistent 298) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 1] (orbitP14RepresentativeCoeff 298)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_298))

theorem orbitP14_path_endpoint_299 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 2, 1, 2, 0, 1, 2, 0, 1, 0]
      (orbitP14RepresentativeCoeff 299) = orbitP14TargetCoeff 299 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv299 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 299))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 299)) ≃*
      CocycleGroup (orbitP14TargetCocycle 299)
        (orbitP14TargetCocycle_consistent 299) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 2, 1, 2, 0, 1, 2, 0, 1, 0] (orbitP14RepresentativeCoeff 299)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_299))

theorem orbitP14_path_endpoint_300 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 1]
      (orbitP14RepresentativeCoeff 300) = orbitP14TargetCoeff 300 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv300 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 300))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 300)) ≃*
      CocycleGroup (orbitP14TargetCocycle 300)
        (orbitP14TargetCocycle_consistent 300) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 1] (orbitP14RepresentativeCoeff 300)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_300))

theorem orbitP14_path_endpoint_301 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2]
      (orbitP14RepresentativeCoeff 301) = orbitP14TargetCoeff 301 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv301 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 301))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 301)) ≃*
      CocycleGroup (orbitP14TargetCocycle 301)
        (orbitP14TargetCocycle_consistent 301) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2] (orbitP14RepresentativeCoeff 301)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_301))

theorem orbitP14_path_endpoint_302 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 2, 1, 2, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 302) = orbitP14TargetCoeff 302 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv302 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 302))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 302)) ≃*
      CocycleGroup (orbitP14TargetCocycle 302)
        (orbitP14TargetCocycle_consistent 302) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 2, 1, 2, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 302)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_302))

theorem orbitP14_path_endpoint_303 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 303) = orbitP14TargetCoeff 303 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv303 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 303))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 303)) ≃*
      CocycleGroup (orbitP14TargetCocycle 303)
        (orbitP14TargetCocycle_consistent 303) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 303)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_303))

end Smallgroups.UsefulTheorems.Order32Certificate
