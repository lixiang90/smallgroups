/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent12Core
import Smallgroups.GAP.Polycyclic.Imported.Order32

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 12, orbit 2, alignment to GAP id 35. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP12OrbitGroup2 := CocycleGroup
  (orbitP12SelectedCocycle 2) (orbitP12SelectedCocycle_consistent 2)
def orbitP12GapExponents2 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 1, 0, 1], [1, 1, 1, 0, 0], [1, 0, 0, 1, 0], [1, 0, 0, 1, 1], [0, 0, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 1, 0], [0, 0, 0, 1, 1], [0, 1, 1, 1, 0], [0, 1, 1, 1, 1], [1, 1, 0, 0, 0], [1, 1, 0, 0, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 0], [1, 0, 1, 1, 1], [1, 0, 1, 1, 0], [1, 0, 0, 0, 0], [1, 0, 0, 0, 1], [0, 0, 1, 1, 0], [0, 0, 1, 1, 1], [0, 1, 0, 1, 0], [0, 1, 0, 1, 1], [0, 1, 1, 0, 0], [0, 1, 1, 0, 1], [1, 1, 0, 1, 0], [1, 1, 0, 1, 1], [1, 0, 1, 0, 1], [1, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 1, 0, 0, 1]]
def orbitP12ToGap2 (x : orbitP12OrbitGroup2) :
    PCGroup smallGroup_32_35 :=
  evalVec (orbitP12GapExponents2 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_35.layers)

set_option maxHeartbeats 8000000 in
-- Finite verification of the generated 32-element PC isomorphism.
noncomputable def orbitP12GapEquiv2 :
    orbitP12OrbitGroup2 ≃* PCGroup smallGroup_32_35 :=
  mulEquivOfDecide orbitP12ToGap2
    (by decide +kernel) (by decide +kernel)

end Smallgroups.UsefulTheorems.Order32Certificate
