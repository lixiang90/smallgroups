/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent09Core
import Smallgroups.GAP.Polycyclic.Imported.Order32

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 9, orbit 2, alignment to GAP id 10. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP9OrbitGroup2 := CocycleGroup
  (orbitP9SelectedCocycle 2) (orbitP9SelectedCocycle_consistent 2)
def orbitP9GapExponents2 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 1, 1], [1, 0, 0, 1, 0], [1, 0, 0, 0, 1], [0, 1, 1, 1, 1], [0, 1, 1, 0, 0], [0, 0, 1, 1, 0], [0, 0, 1, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [1, 1, 1, 0, 1], [1, 1, 1, 1, 0], [1, 0, 1, 0, 0], [1, 0, 1, 1, 1], [1, 0, 0, 1, 1], [1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 1, 0, 1, 1], [0, 1, 1, 1, 0], [0, 1, 1, 0, 1], [0, 0, 1, 1, 1], [0, 0, 1, 0, 0], [1, 1, 0, 1, 0], [1, 1, 0, 0, 1], [1, 1, 1, 0, 0], [1, 1, 1, 1, 1], [1, 0, 1, 0, 1], [1, 0, 1, 1, 0], [0, 1, 0, 0, 1], [0, 1, 0, 1, 0], [1, 1, 0, 1, 1], [1, 1, 0, 0, 0]]
def orbitP9ToGap2 (x : orbitP9OrbitGroup2) :
    PCGroup smallGroup_32_10 :=
  evalVec (orbitP9GapExponents2 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_10.layers)

set_option maxHeartbeats 8000000 in
-- Finite verification of the generated 32-element PC isomorphism.
noncomputable def orbitP9GapEquiv2 :
    orbitP9OrbitGroup2 ≃* PCGroup smallGroup_32_10 :=
  mulEquivOfDecide orbitP9ToGap2
    (by decide +kernel) (by decide +kernel)

end Smallgroups.UsefulTheorems.Order32Certificate
