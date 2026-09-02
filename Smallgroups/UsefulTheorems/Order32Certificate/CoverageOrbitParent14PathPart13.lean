/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart12

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 13. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_192 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 2, 0, 1, 1, 2]
      (orbitP14RepresentativeCoeff 192) = orbitP14TargetCoeff 192 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv192 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 192))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 192)) ≃*
      CocycleGroup (orbitP14TargetCocycle 192)
        (orbitP14TargetCocycle_consistent 192) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 2, 0, 1, 1, 2] (orbitP14RepresentativeCoeff 192)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_192))

theorem orbitP14_path_endpoint_193 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 193) = orbitP14TargetCoeff 193 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv193 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 193))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 193)) ≃*
      CocycleGroup (orbitP14TargetCocycle 193)
        (orbitP14TargetCocycle_consistent 193) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 193)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_193))

theorem orbitP14_path_endpoint_194 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 194) = orbitP14TargetCoeff 194 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv194 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 194))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 194)) ≃*
      CocycleGroup (orbitP14TargetCocycle 194)
        (orbitP14TargetCocycle_consistent 194) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 194)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_194))

theorem orbitP14_path_endpoint_195 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 1, 2, 1, 2, 1, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 195) = orbitP14TargetCoeff 195 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv195 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 195))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 195)) ≃*
      CocycleGroup (orbitP14TargetCocycle 195)
        (orbitP14TargetCocycle_consistent 195) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 1, 2, 1, 2, 1, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 195)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_195))

theorem orbitP14_path_endpoint_196 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 0, 2]
      (orbitP14RepresentativeCoeff 196) = orbitP14TargetCoeff 196 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv196 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 196))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 196)) ≃*
      CocycleGroup (orbitP14TargetCocycle 196)
        (orbitP14TargetCocycle_consistent 196) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 0, 2] (orbitP14RepresentativeCoeff 196)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_196))

theorem orbitP14_path_endpoint_197 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2]
      (orbitP14RepresentativeCoeff 197) = orbitP14TargetCoeff 197 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv197 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 197))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 197)) ≃*
      CocycleGroup (orbitP14TargetCocycle 197)
        (orbitP14TargetCocycle_consistent 197) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2] (orbitP14RepresentativeCoeff 197)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_197))

theorem orbitP14_path_endpoint_198 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 1]
      (orbitP14RepresentativeCoeff 198) = orbitP14TargetCoeff 198 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv198 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 198))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 198)) ≃*
      CocycleGroup (orbitP14TargetCocycle 198)
        (orbitP14TargetCocycle_consistent 198) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 1] (orbitP14RepresentativeCoeff 198)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_198))

theorem orbitP14_path_endpoint_199 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 1, 0, 2, 1, 0]
      (orbitP14RepresentativeCoeff 199) = orbitP14TargetCoeff 199 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv199 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 199))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 199)) ≃*
      CocycleGroup (orbitP14TargetCocycle 199)
        (orbitP14TargetCocycle_consistent 199) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 1, 0, 2, 1, 0] (orbitP14RepresentativeCoeff 199)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_199))

theorem orbitP14_path_endpoint_200 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 1, 2, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 200) = orbitP14TargetCoeff 200 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv200 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 200))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 200)) ≃*
      CocycleGroup (orbitP14TargetCocycle 200)
        (orbitP14TargetCocycle_consistent 200) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 1, 2, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 200)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_200))

theorem orbitP14_path_endpoint_201 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 2, 1, 2, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 201) = orbitP14TargetCoeff 201 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv201 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 201))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 201)) ≃*
      CocycleGroup (orbitP14TargetCocycle 201)
        (orbitP14TargetCocycle_consistent 201) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 2, 1, 2, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 201)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_201))

theorem orbitP14_path_endpoint_202 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 202) = orbitP14TargetCoeff 202 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv202 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 202))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 202)) ≃*
      CocycleGroup (orbitP14TargetCocycle 202)
        (orbitP14TargetCocycle_consistent 202) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 202)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_202))

theorem orbitP14_path_endpoint_203 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 2, 0, 1, 1]
      (orbitP14RepresentativeCoeff 203) = orbitP14TargetCoeff 203 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv203 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 203))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 203)) ≃*
      CocycleGroup (orbitP14TargetCocycle 203)
        (orbitP14TargetCocycle_consistent 203) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 2, 0, 1, 1] (orbitP14RepresentativeCoeff 203)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_203))

theorem orbitP14_path_endpoint_204 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 1]
      (orbitP14RepresentativeCoeff 204) = orbitP14TargetCoeff 204 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv204 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 204))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 204)) ≃*
      CocycleGroup (orbitP14TargetCocycle 204)
        (orbitP14TargetCocycle_consistent 204) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 1] (orbitP14RepresentativeCoeff 204)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_204))

theorem orbitP14_path_endpoint_205 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 1, 0, 1]
      (orbitP14RepresentativeCoeff 205) = orbitP14TargetCoeff 205 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv205 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 205))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 205)) ≃*
      CocycleGroup (orbitP14TargetCocycle 205)
        (orbitP14TargetCocycle_consistent 205) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 1, 0, 1] (orbitP14RepresentativeCoeff 205)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_205))

theorem orbitP14_path_endpoint_206 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1]
      (orbitP14RepresentativeCoeff 206) = orbitP14TargetCoeff 206 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv206 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 206))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 206)) ≃*
      CocycleGroup (orbitP14TargetCocycle 206)
        (orbitP14TargetCocycle_consistent 206) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1] (orbitP14RepresentativeCoeff 206)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_206))

theorem orbitP14_path_endpoint_207 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 207) = orbitP14TargetCoeff 207 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv207 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 207))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 207)) ≃*
      CocycleGroup (orbitP14TargetCocycle 207)
        (orbitP14TargetCocycle_consistent 207) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 1, 0] (orbitP14RepresentativeCoeff 207)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_207))

end Smallgroups.UsefulTheorems.Order32Certificate
