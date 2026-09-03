/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent09Core
import Smallgroups.GAP.Polycyclic.Imported.Order32

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 9, orbit 1, alignment to GAP id 14. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP9OrbitGroup1 := CocycleGroup
  (orbitP9SelectedCocycle 1) (orbitP9SelectedCocycle_consistent 1)
def orbitP9GapExponents1 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 1, 1], [1, 0, 0, 0, 0], [1, 0, 0, 1, 1], [1, 1, 0, 1, 0], [1, 1, 0, 0, 1], [0, 0, 1, 0, 0], [0, 0, 1, 1, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [0, 1, 0, 1, 1], [0, 1, 0, 0, 0], [1, 0, 1, 0, 0], [1, 0, 1, 1, 1], [1, 0, 0, 0, 1], [1, 0, 0, 1, 0], [1, 1, 1, 1, 0], [1, 1, 1, 0, 1], [1, 1, 0, 1, 1], [1, 1, 0, 0, 0], [0, 0, 1, 0, 1], [0, 0, 1, 1, 0], [0, 1, 1, 1, 1], [0, 1, 1, 0, 0], [0, 1, 0, 1, 0], [0, 1, 0, 0, 1], [1, 0, 1, 0, 1], [1, 0, 1, 1, 0], [1, 1, 1, 1, 1], [1, 1, 1, 0, 0], [0, 1, 1, 1, 0], [0, 1, 1, 0, 1]]
def orbitP9ToGap1 (x : orbitP9OrbitGroup1) :
    PCGroup smallGroup_32_14 :=
  evalVec (orbitP9GapExponents1 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_14.layers)

set_option maxHeartbeats 8000000 in
-- Finite verification of the generated 32-element PC isomorphism.
noncomputable def orbitP9GapEquiv1 :
    orbitP9OrbitGroup1 ≃* PCGroup smallGroup_32_14 :=
  mulEquivOfDecide orbitP9ToGap1
    (by decide +kernel) (by decide +kernel)

end Smallgroups.UsefulTheorems.Order32Certificate
