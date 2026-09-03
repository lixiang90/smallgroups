/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11Core
import Smallgroups.GAP.Polycyclic.Imported.Order32

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 11, orbit 1, alignment to GAP id 25. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP11OrbitGroup1 := CocycleGroup
  (orbitP11SelectedCocycle 1) (orbitP11SelectedCocycle_consistent 1)
def orbitP11GapExponents1 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [0, 1, 0, 1, 1], [0, 1, 0, 1, 0], [1, 0, 0, 0, 1], [1, 0, 0, 0, 0], [0, 0, 1, 1, 1], [0, 0, 1, 1, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 1], [1, 1, 0, 0, 0], [1, 1, 0, 0, 1], [0, 1, 1, 0, 0], [0, 1, 1, 0, 1], [0, 1, 0, 0, 1], [0, 1, 0, 0, 0], [1, 0, 1, 1, 1], [1, 0, 1, 1, 0], [1, 0, 0, 1, 1], [1, 0, 0, 1, 0], [0, 0, 1, 0, 1], [0, 0, 1, 0, 0], [1, 1, 1, 1, 0], [1, 1, 1, 1, 1], [1, 1, 0, 1, 0], [1, 1, 0, 1, 1], [0, 1, 1, 1, 0], [0, 1, 1, 1, 1], [1, 0, 1, 0, 1], [1, 0, 1, 0, 0], [1, 1, 1, 0, 0], [1, 1, 1, 0, 1]]
def orbitP11ToGap1 (x : orbitP11OrbitGroup1) :
    PCGroup smallGroup_32_25 :=
  evalVec (orbitP11GapExponents1 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_25.layers)

set_option maxHeartbeats 8000000 in
-- Finite verification of the generated 32-element PC isomorphism.
noncomputable def orbitP11GapEquiv1 :
    orbitP11OrbitGroup1 ≃* PCGroup smallGroup_32_25 :=
  mulEquivOfDecide orbitP11ToGap1
    (by decide +kernel) (by decide +kernel)

end Smallgroups.UsefulTheorems.Order32Certificate
