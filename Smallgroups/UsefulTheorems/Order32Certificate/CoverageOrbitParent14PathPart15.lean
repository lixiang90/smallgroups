/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart14

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 15. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_224 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 224) = orbitP14TargetCoeff 224 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv224 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 224))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 224)) ≃*
      CocycleGroup (orbitP14TargetCocycle 224)
        (orbitP14TargetCocycle_consistent 224) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 224)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_224))

theorem orbitP14_path_endpoint_225 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 2, 1, 2, 1]
      (orbitP14RepresentativeCoeff 225) = orbitP14TargetCoeff 225 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv225 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 225))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 225)) ≃*
      CocycleGroup (orbitP14TargetCocycle 225)
        (orbitP14TargetCocycle_consistent 225) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 2, 1, 2, 1] (orbitP14RepresentativeCoeff 225)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_225))

theorem orbitP14_path_endpoint_226 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 0, 2, 0, 1, 2, 1, 2, 1]
      (orbitP14RepresentativeCoeff 226) = orbitP14TargetCoeff 226 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv226 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 226))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 226)) ≃*
      CocycleGroup (orbitP14TargetCocycle 226)
        (orbitP14TargetCocycle_consistent 226) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 0, 2, 0, 1, 2, 1, 2, 1] (orbitP14RepresentativeCoeff 226)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_226))

theorem orbitP14_path_endpoint_227 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 0, 1, 0, 2]
      (orbitP14RepresentativeCoeff 227) = orbitP14TargetCoeff 227 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv227 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 227))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 227)) ≃*
      CocycleGroup (orbitP14TargetCocycle 227)
        (orbitP14TargetCocycle_consistent 227) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 0, 1, 0, 2] (orbitP14RepresentativeCoeff 227)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_227))

theorem orbitP14_path_endpoint_228 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 0, 1]
      (orbitP14RepresentativeCoeff 228) = orbitP14TargetCoeff 228 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv228 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 228))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 228)) ≃*
      CocycleGroup (orbitP14TargetCocycle 228)
        (orbitP14TargetCocycle_consistent 228) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 0, 1] (orbitP14RepresentativeCoeff 228)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_228))

theorem orbitP14_path_endpoint_229 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 229) = orbitP14TargetCoeff 229 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv229 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 229))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 229)) ≃*
      CocycleGroup (orbitP14TargetCocycle 229)
        (orbitP14TargetCocycle_consistent 229) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 229)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_229))

theorem orbitP14_path_endpoint_230 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1, 1, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 230) = orbitP14TargetCoeff 230 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv230 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 230))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 230)) ≃*
      CocycleGroup (orbitP14TargetCocycle 230)
        (orbitP14TargetCocycle_consistent 230) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1, 1, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 230)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_230))

theorem orbitP14_path_endpoint_231 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1]
      (orbitP14RepresentativeCoeff 231) = orbitP14TargetCoeff 231 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv231 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 231))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 231)) ≃*
      CocycleGroup (orbitP14TargetCocycle 231)
        (orbitP14TargetCocycle_consistent 231) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1] (orbitP14RepresentativeCoeff 231)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_231))

theorem orbitP14_path_endpoint_232 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 0]
      (orbitP14RepresentativeCoeff 232) = orbitP14TargetCoeff 232 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv232 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 232))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 232)) ≃*
      CocycleGroup (orbitP14TargetCocycle 232)
        (orbitP14TargetCocycle_consistent 232) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 0] (orbitP14RepresentativeCoeff 232)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_232))

theorem orbitP14_path_endpoint_233 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 233) = orbitP14TargetCoeff 233 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv233 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 233))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 233)) ≃*
      CocycleGroup (orbitP14TargetCocycle 233)
        (orbitP14TargetCocycle_consistent 233) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 233)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_233))

theorem orbitP14_path_endpoint_234 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 1, 0]
      (orbitP14RepresentativeCoeff 234) = orbitP14TargetCoeff 234 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv234 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 234))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 234)) ≃*
      CocycleGroup (orbitP14TargetCocycle 234)
        (orbitP14TargetCocycle_consistent 234) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 1, 0] (orbitP14RepresentativeCoeff 234)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_234))

theorem orbitP14_path_endpoint_235 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 0, 2]
      (orbitP14RepresentativeCoeff 235) = orbitP14TargetCoeff 235 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv235 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 235))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 235)) ≃*
      CocycleGroup (orbitP14TargetCocycle 235)
        (orbitP14TargetCocycle_consistent 235) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 0, 2] (orbitP14RepresentativeCoeff 235)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_235))

theorem orbitP14_path_endpoint_236 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 2, 1, 2, 0]
      (orbitP14RepresentativeCoeff 236) = orbitP14TargetCoeff 236 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv236 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 236))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 236)) ≃*
      CocycleGroup (orbitP14TargetCocycle 236)
        (orbitP14TargetCocycle_consistent 236) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 2, 1, 2, 0] (orbitP14RepresentativeCoeff 236)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_236))

theorem orbitP14_path_endpoint_237 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 0, 1, 0]
      (orbitP14RepresentativeCoeff 237) = orbitP14TargetCoeff 237 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv237 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 237))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 237)) ≃*
      CocycleGroup (orbitP14TargetCocycle 237)
        (orbitP14TargetCocycle_consistent 237) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 0, 1, 0] (orbitP14RepresentativeCoeff 237)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_237))

theorem orbitP14_path_endpoint_238 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 0, 2, 0, 1, 2, 1, 2, 0]
      (orbitP14RepresentativeCoeff 238) = orbitP14TargetCoeff 238 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv238 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 238))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 238)) ≃*
      CocycleGroup (orbitP14TargetCocycle 238)
        (orbitP14TargetCocycle_consistent 238) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 0, 2, 0, 1, 2, 1, 2, 0] (orbitP14RepresentativeCoeff 238)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_238))

theorem orbitP14_path_endpoint_239 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 1, 1, 2]
      (orbitP14RepresentativeCoeff 239) = orbitP14TargetCoeff 239 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv239 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 239))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 239)) ≃*
      CocycleGroup (orbitP14TargetCocycle 239)
        (orbitP14TargetCocycle_consistent 239) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 1, 1, 2] (orbitP14RepresentativeCoeff 239)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_239))

end Smallgroups.UsefulTheorems.Order32Certificate
