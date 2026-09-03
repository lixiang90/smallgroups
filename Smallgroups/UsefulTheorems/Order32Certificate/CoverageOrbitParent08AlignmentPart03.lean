/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent08Core
import Smallgroups.GAP.Polycyclic.Imported.Order32

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 8, orbit 2, alignment to GAP id 9. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP8OrbitGroup2 := CocycleGroup
  (orbitP8SelectedCocycle 2) (orbitP8SelectedCocycle_consistent 2)
def orbitP8GapExponents2 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 1, 1], [1, 0, 0, 1, 1], [1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 1, 0, 1, 1], [0, 0, 1, 1, 1], [0, 0, 1, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [1, 1, 0, 1, 1], [1, 1, 0, 0, 0], [1, 0, 1, 0, 0], [1, 0, 1, 1, 1], [1, 0, 0, 1, 0], [1, 0, 0, 0, 1], [0, 1, 1, 1, 1], [0, 1, 1, 0, 0], [0, 1, 0, 0, 1], [0, 1, 0, 1, 0], [0, 0, 1, 1, 0], [0, 0, 1, 0, 1], [1, 1, 1, 0, 0], [1, 1, 1, 1, 1], [1, 1, 0, 1, 0], [1, 1, 0, 0, 1], [1, 0, 1, 0, 1], [1, 0, 1, 1, 0], [0, 1, 1, 1, 0], [0, 1, 1, 0, 1], [1, 1, 1, 0, 1], [1, 1, 1, 1, 0]]
def orbitP8ToGap2 (x : orbitP8OrbitGroup2) :
    PCGroup smallGroup_32_9 :=
  evalVec (orbitP8GapExponents2 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_9.layers)

set_option maxHeartbeats 8000000 in
-- Finite verification of the generated 32-element PC isomorphism.
noncomputable def orbitP8GapEquiv2 :
    orbitP8OrbitGroup2 ≃* PCGroup smallGroup_32_9 :=
  mulEquivOfDecide orbitP8ToGap2
    (by decide +kernel) (by decide +kernel)

end Smallgroups.UsefulTheorems.Order32Certificate
