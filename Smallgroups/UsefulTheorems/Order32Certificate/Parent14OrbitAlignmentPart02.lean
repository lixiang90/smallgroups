/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageParent14OrbitCore
import Smallgroups.GAP.Polycyclic.Imported.Order32
import Smallgroups.UsefulTheorems.Order32Certificate.Parent14OrbitAlignmentPart01

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Direct parent-14 orbit 1 alignment to GAP id 45. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

abbrev parent14OrbitGroup1 :=
  CocycleGroup (parent14SelectedCocycle 1)
    (parent14SelectedCocycle_consistent 1)
def parent14GapExponents1 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [0, 1, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 0, 0], [0, 0, 1, 0, 1], [1, 0, 0, 0, 0], [1, 0, 0, 0, 1], [1, 0, 0, 1, 0], [1, 0, 0, 1, 1], [0, 1, 1, 0, 0], [0, 1, 1, 0, 1], [1, 1, 0, 0, 0], [1, 1, 0, 0, 1], [1, 1, 0, 1, 0], [1, 1, 0, 1, 1], [1, 0, 1, 0, 0], [1, 0, 1, 0, 1], [1, 0, 1, 1, 0], [1, 0, 1, 1, 1], [0, 0, 0, 1, 0], [0, 0, 0, 1, 1], [1, 1, 1, 0, 0], [1, 1, 1, 0, 1], [1, 1, 1, 1, 0], [1, 1, 1, 1, 1], [0, 1, 0, 1, 0], [0, 1, 0, 1, 1], [0, 0, 1, 1, 0], [0, 0, 1, 1, 1], [0, 1, 1, 1, 0], [0, 1, 1, 1, 1]]
def parent14OrbitToGap1 (x : parent14OrbitGroup1) :
    PCGroup smallGroup_32_45 :=
  evalVec (parent14GapExponents1 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_45.layers)

set_option maxHeartbeats 8000000 in
-- Finite verification of the generated 32-element PC isomorphism.
noncomputable def parent14OrbitGapEquiv1 :
    parent14OrbitGroup1 ≃* PCGroup smallGroup_32_45 :=
  mulEquivOfDecide parent14OrbitToGap1
    (by decide +kernel) (by decide +kernel)

end Smallgroups.UsefulTheorems.Order32Certificate
