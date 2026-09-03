/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent03Core
import Smallgroups.GAP.Polycyclic.Imported.Order32

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 3, orbit 4, alignment to GAP id 2. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP3OrbitGroup4 := CocycleGroup
  (orbitP3SelectedCocycle 4) (orbitP3SelectedCocycle_consistent 4)
def orbitP3GapExponents4 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 1, 1, 1], [0, 1, 1, 1, 1], [0, 1, 0, 0, 0], [1, 1, 0, 0, 0], [1, 1, 1, 1, 1], [0, 0, 0, 1, 1], [0, 0, 1, 0, 0], [0, 0, 0, 0, 1], [0, 0, 1, 1, 0], [1, 0, 1, 0, 1], [1, 0, 0, 1, 0], [0, 1, 0, 1, 1], [0, 1, 1, 0, 0], [0, 1, 0, 0, 1], [0, 1, 1, 1, 0], [1, 1, 1, 0, 0], [1, 1, 0, 1, 1], [1, 1, 1, 1, 0], [1, 1, 0, 0, 1], [0, 0, 0, 1, 0], [0, 0, 1, 0, 1], [1, 0, 1, 1, 0], [1, 0, 0, 0, 1], [1, 0, 1, 0, 0], [1, 0, 0, 1, 1], [0, 1, 1, 0, 1], [0, 1, 0, 1, 0], [1, 1, 0, 1, 0], [1, 1, 1, 0, 1], [1, 0, 1, 1, 1], [1, 0, 0, 0, 0]]
def orbitP3ToGap4 (x : orbitP3OrbitGroup4) :
    PCGroup smallGroup_32_2 :=
  evalVec (orbitP3GapExponents4 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_2.layers)

set_option maxHeartbeats 8000000 in
-- Finite verification of the generated 32-element PC isomorphism.
noncomputable def orbitP3GapEquiv4 :
    orbitP3OrbitGroup4 ≃* PCGroup smallGroup_32_2 :=
  mulEquivOfDecide orbitP3ToGap4
    (by decide +kernel) (by decide +kernel)

end Smallgroups.UsefulTheorems.Order32Certificate
