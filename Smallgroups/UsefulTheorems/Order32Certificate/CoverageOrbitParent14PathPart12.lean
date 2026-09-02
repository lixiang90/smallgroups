/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart11

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 12. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_176 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 1]
      (orbitP14RepresentativeCoeff 176) = orbitP14TargetCoeff 176 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv176 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 176))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 176)) ≃*
      CocycleGroup (orbitP14TargetCocycle 176)
        (orbitP14TargetCocycle_consistent 176) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 1] (orbitP14RepresentativeCoeff 176)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_176))

theorem orbitP14_path_endpoint_177 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 177) = orbitP14TargetCoeff 177 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv177 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 177))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 177)) ≃*
      CocycleGroup (orbitP14TargetCocycle 177)
        (orbitP14TargetCocycle_consistent 177) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 177)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_177))

theorem orbitP14_path_endpoint_178 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 1, 0, 2, 1, 1, 1]
      (orbitP14RepresentativeCoeff 178) = orbitP14TargetCoeff 178 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv178 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 178))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 178)) ≃*
      CocycleGroup (orbitP14TargetCocycle 178)
        (orbitP14TargetCocycle_consistent 178) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 1, 0, 2, 1, 1, 1] (orbitP14RepresentativeCoeff 178)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_178))

theorem orbitP14_path_endpoint_179 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2]
      (orbitP14RepresentativeCoeff 179) = orbitP14TargetCoeff 179 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv179 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 179))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 179)) ≃*
      CocycleGroup (orbitP14TargetCocycle 179)
        (orbitP14TargetCocycle_consistent 179) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2] (orbitP14RepresentativeCoeff 179)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_179))

theorem orbitP14_path_endpoint_180 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1, 1, 1, 2]
      (orbitP14RepresentativeCoeff 180) = orbitP14TargetCoeff 180 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv180 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 180))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 180)) ≃*
      CocycleGroup (orbitP14TargetCocycle 180)
        (orbitP14TargetCocycle_consistent 180) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1, 1, 1, 2] (orbitP14RepresentativeCoeff 180)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_180))

theorem orbitP14_path_endpoint_181 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 0]
      (orbitP14RepresentativeCoeff 181) = orbitP14TargetCoeff 181 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv181 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 181))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 181)) ≃*
      CocycleGroup (orbitP14TargetCocycle 181)
        (orbitP14TargetCocycle_consistent 181) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 0] (orbitP14RepresentativeCoeff 181)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_181))

theorem orbitP14_path_endpoint_182 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 1, 1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 182) = orbitP14TargetCoeff 182 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv182 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 182))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 182)) ≃*
      CocycleGroup (orbitP14TargetCocycle 182)
        (orbitP14TargetCocycle_consistent 182) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 1, 1, 2, 0, 1] (orbitP14RepresentativeCoeff 182)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_182))

theorem orbitP14_path_endpoint_183 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1]
      (orbitP14RepresentativeCoeff 183) = orbitP14TargetCoeff 183 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv183 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 183))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 183)) ≃*
      CocycleGroup (orbitP14TargetCocycle 183)
        (orbitP14TargetCocycle_consistent 183) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1] (orbitP14RepresentativeCoeff 183)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_183))

theorem orbitP14_path_endpoint_184 :
    Order16Table.applyOrbitPath orbitP14ActionColumns []
      (orbitP14RepresentativeCoeff 184) = orbitP14TargetCoeff 184 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv184 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 184))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 184)) ≃*
      CocycleGroup (orbitP14TargetCocycle 184)
        (orbitP14TargetCocycle_consistent 184) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [] (orbitP14RepresentativeCoeff 184)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_184))

theorem orbitP14_path_endpoint_185 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 1, 2, 1, 0, 2]
      (orbitP14RepresentativeCoeff 185) = orbitP14TargetCoeff 185 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv185 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 185))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 185)) ≃*
      CocycleGroup (orbitP14TargetCocycle 185)
        (orbitP14TargetCocycle_consistent 185) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 1, 2, 1, 0, 2] (orbitP14RepresentativeCoeff 185)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_185))

theorem orbitP14_path_endpoint_186 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 186) = orbitP14TargetCoeff 186 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv186 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 186))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 186)) ≃*
      CocycleGroup (orbitP14TargetCocycle 186)
        (orbitP14TargetCocycle_consistent 186) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 186)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_186))

theorem orbitP14_path_endpoint_187 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 1, 1]
      (orbitP14RepresentativeCoeff 187) = orbitP14TargetCoeff 187 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv187 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 187))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 187)) ≃*
      CocycleGroup (orbitP14TargetCocycle 187)
        (orbitP14TargetCocycle_consistent 187) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 1, 1] (orbitP14RepresentativeCoeff 187)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_187))

theorem orbitP14_path_endpoint_188 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 1, 0]
      (orbitP14RepresentativeCoeff 188) = orbitP14TargetCoeff 188 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv188 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 188))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 188)) ≃*
      CocycleGroup (orbitP14TargetCocycle 188)
        (orbitP14TargetCocycle_consistent 188) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 1, 0] (orbitP14RepresentativeCoeff 188)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_188))

theorem orbitP14_path_endpoint_189 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 1, 1, 0]
      (orbitP14RepresentativeCoeff 189) = orbitP14TargetCoeff 189 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv189 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 189))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 189)) ≃*
      CocycleGroup (orbitP14TargetCocycle 189)
        (orbitP14TargetCocycle_consistent 189) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 1, 1, 0] (orbitP14RepresentativeCoeff 189)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_189))

theorem orbitP14_path_endpoint_190 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1]
      (orbitP14RepresentativeCoeff 190) = orbitP14TargetCoeff 190 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv190 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 190))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 190)) ≃*
      CocycleGroup (orbitP14TargetCocycle 190)
        (orbitP14TargetCocycle_consistent 190) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1] (orbitP14RepresentativeCoeff 190)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_190))

theorem orbitP14_path_endpoint_191 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 2, 1, 0, 2, 1, 2]
      (orbitP14RepresentativeCoeff 191) = orbitP14TargetCoeff 191 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv191 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 191))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 191)) ≃*
      CocycleGroup (orbitP14TargetCocycle 191)
        (orbitP14TargetCocycle_consistent 191) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 2, 1, 0, 2, 1, 2] (orbitP14RepresentativeCoeff 191)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_191))

end Smallgroups.UsefulTheorems.Order32Certificate
