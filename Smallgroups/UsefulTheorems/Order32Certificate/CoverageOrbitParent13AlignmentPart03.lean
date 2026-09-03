/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13Core
import Smallgroups.GAP.Polycyclic.Imported.Order32

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 13, orbit 2, alignment to GAP id 28. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP13OrbitGroup2 := CocycleGroup
  (orbitP13SelectedCocycle 2) (orbitP13SelectedCocycle_consistent 2)
def orbitP13GapExponents2 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 1, 1], [1, 0, 0, 1, 1], [1, 0, 0, 0, 0], [1, 1, 0, 0, 1], [1, 1, 0, 1, 0], [0, 1, 1, 0, 1], [0, 1, 1, 1, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [0, 1, 0, 1, 0], [0, 1, 0, 0, 1], [1, 1, 1, 1, 0], [1, 1, 1, 0, 1], [1, 0, 0, 1, 0], [1, 0, 0, 0, 1], [1, 0, 1, 0, 1], [1, 0, 1, 1, 0], [1, 1, 0, 0, 0], [1, 1, 0, 1, 1], [0, 1, 1, 0, 0], [0, 1, 1, 1, 1], [0, 0, 1, 1, 0], [0, 0, 1, 0, 1], [0, 1, 0, 1, 1], [0, 1, 0, 0, 0], [1, 1, 1, 1, 1], [1, 1, 1, 0, 0], [1, 0, 1, 0, 0], [1, 0, 1, 1, 1], [0, 0, 1, 1, 1], [0, 0, 1, 0, 0]]
def orbitP13ToGap2 (x : orbitP13OrbitGroup2) :
    PCGroup smallGroup_32_28 :=
  evalVec (orbitP13GapExponents2 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_28.layers)

set_option maxHeartbeats 8000000 in
-- Finite verification of the generated 32-element PC isomorphism.
noncomputable def orbitP13GapEquiv2 :
    orbitP13OrbitGroup2 ≃* PCGroup smallGroup_32_28 :=
  mulEquivOfDecide orbitP13ToGap2
    (by decide +kernel) (by decide +kernel)

end Smallgroups.UsefulTheorems.Order32Certificate
