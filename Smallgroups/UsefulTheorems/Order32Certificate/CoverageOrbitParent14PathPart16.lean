/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart15

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 16. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_240 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 0, 1, 1]
      (orbitP14RepresentativeCoeff 240) = orbitP14TargetCoeff 240 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv240 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 240))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 240)) ≃*
      CocycleGroup (orbitP14TargetCocycle 240)
        (orbitP14TargetCocycle_consistent 240) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 0, 1, 1] (orbitP14RepresentativeCoeff 240)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_240))

theorem orbitP14_path_endpoint_241 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 0, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 241) = orbitP14TargetCoeff 241 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv241 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 241))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 241)) ≃*
      CocycleGroup (orbitP14TargetCocycle 241)
        (orbitP14TargetCocycle_consistent 241) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 0, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 241)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_241))

theorem orbitP14_path_endpoint_242 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 0, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 242) = orbitP14TargetCoeff 242 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv242 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 242))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 242)) ≃*
      CocycleGroup (orbitP14TargetCocycle 242)
        (orbitP14TargetCocycle_consistent 242) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 0, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 242)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_242))

theorem orbitP14_path_endpoint_243 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 0, 1, 0, 2, 1, 1]
      (orbitP14RepresentativeCoeff 243) = orbitP14TargetCoeff 243 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv243 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 243))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 243)) ≃*
      CocycleGroup (orbitP14TargetCocycle 243)
        (orbitP14TargetCocycle_consistent 243) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 0, 1, 0, 2, 1, 1] (orbitP14RepresentativeCoeff 243)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_243))

theorem orbitP14_path_endpoint_244 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 0, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 244) = orbitP14TargetCoeff 244 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv244 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 244))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 244)) ≃*
      CocycleGroup (orbitP14TargetCocycle 244)
        (orbitP14TargetCocycle_consistent 244) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 0, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 244)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_244))

theorem orbitP14_path_endpoint_245 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 245) = orbitP14TargetCoeff 245 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv245 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 245))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 245)) ≃*
      CocycleGroup (orbitP14TargetCocycle 245)
        (orbitP14TargetCocycle_consistent 245) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 245)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_245))

theorem orbitP14_path_endpoint_246 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 246) = orbitP14TargetCoeff 246 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv246 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 246))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 246)) ≃*
      CocycleGroup (orbitP14TargetCocycle 246)
        (orbitP14TargetCocycle_consistent 246) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 1] (orbitP14RepresentativeCoeff 246)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_246))

theorem orbitP14_path_endpoint_247 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 2, 1, 2, 0]
      (orbitP14RepresentativeCoeff 247) = orbitP14TargetCoeff 247 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv247 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 247))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 247)) ≃*
      CocycleGroup (orbitP14TargetCocycle 247)
        (orbitP14TargetCocycle_consistent 247) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 2, 1, 2, 0] (orbitP14RepresentativeCoeff 247)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_247))

theorem orbitP14_path_endpoint_248 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 248) = orbitP14TargetCoeff 248 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv248 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 248))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 248)) ≃*
      CocycleGroup (orbitP14TargetCocycle 248)
        (orbitP14TargetCocycle_consistent 248) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 248)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_248))

theorem orbitP14_path_endpoint_249 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 0, 1, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 249) = orbitP14TargetCoeff 249 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv249 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 249))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 249)) ≃*
      CocycleGroup (orbitP14TargetCocycle 249)
        (orbitP14TargetCocycle_consistent 249) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 0, 1, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 249)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_249))

theorem orbitP14_path_endpoint_250 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 1]
      (orbitP14RepresentativeCoeff 250) = orbitP14TargetCoeff 250 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv250 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 250))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 250)) ≃*
      CocycleGroup (orbitP14TargetCocycle 250)
        (orbitP14TargetCocycle_consistent 250) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 1] (orbitP14RepresentativeCoeff 250)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_250))

theorem orbitP14_path_endpoint_251 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 1, 2, 0, 1, 0, 2]
      (orbitP14RepresentativeCoeff 251) = orbitP14TargetCoeff 251 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv251 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 251))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 251)) ≃*
      CocycleGroup (orbitP14TargetCocycle 251)
        (orbitP14TargetCocycle_consistent 251) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 1, 2, 0, 1, 0, 2] (orbitP14RepresentativeCoeff 251)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_251))

theorem orbitP14_path_endpoint_252 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 252) = orbitP14TargetCoeff 252 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv252 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 252))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 252)) ≃*
      CocycleGroup (orbitP14TargetCocycle 252)
        (orbitP14TargetCocycle_consistent 252) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 252)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_252))

theorem orbitP14_path_endpoint_253 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 253) = orbitP14TargetCoeff 253 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv253 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 253))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 253)) ≃*
      CocycleGroup (orbitP14TargetCocycle 253)
        (orbitP14TargetCocycle_consistent 253) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 253)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_253))

theorem orbitP14_path_endpoint_254 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 1, 2, 1, 2, 1, 1, 0, 2]
      (orbitP14RepresentativeCoeff 254) = orbitP14TargetCoeff 254 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv254 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 254))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 254)) ≃*
      CocycleGroup (orbitP14TargetCocycle 254)
        (orbitP14TargetCocycle_consistent 254) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 1, 2, 1, 2, 1, 1, 0, 2] (orbitP14RepresentativeCoeff 254)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_254))

theorem orbitP14_path_endpoint_255 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 0, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 255) = orbitP14TargetCoeff 255 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv255 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 255))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 255)) ≃*
      CocycleGroup (orbitP14TargetCocycle 255)
        (orbitP14TargetCocycle_consistent 255) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 0, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 255)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_255))

end Smallgroups.UsefulTheorems.Order32Certificate
