/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10Core
import Smallgroups.GAP.Polycyclic.Imported.Order32

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 10, orbit 7, alignment to GAP id 36. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP10OrbitGroup7 := CocycleGroup
  (orbitP10SelectedCocycle 7) (orbitP10SelectedCocycle_consistent 7)
def orbitP10GapExponents7 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 1, 1, 0], [1, 1, 1, 1, 1], [0, 0, 1, 0, 0], [0, 0, 1, 0, 1], [0, 1, 1, 1, 0], [0, 1, 1, 1, 1], [0, 0, 0, 1, 1], [0, 0, 0, 1, 0], [1, 1, 0, 1, 1], [1, 1, 0, 1, 0], [1, 0, 0, 0, 1], [1, 0, 0, 0, 0], [1, 1, 1, 0, 1], [1, 1, 1, 0, 0], [0, 1, 0, 1, 0], [0, 1, 0, 1, 1], [0, 0, 1, 1, 0], [0, 0, 1, 1, 1], [0, 1, 1, 0, 1], [0, 1, 1, 0, 0], [1, 0, 1, 0, 1], [1, 0, 1, 0, 0], [1, 1, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 0, 1, 1], [1, 0, 0, 1, 0], [0, 1, 0, 0, 0], [0, 1, 0, 0, 1], [1, 0, 1, 1, 0], [1, 0, 1, 1, 1]]
def orbitP10ToGap7 (x : orbitP10OrbitGroup7) :
    PCGroup smallGroup_32_36 :=
  evalVec (orbitP10GapExponents7 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_36.layers)

set_option maxHeartbeats 8000000 in
-- Finite verification of the generated 32-element PC isomorphism.
noncomputable def orbitP10GapEquiv7 :
    orbitP10OrbitGroup7 ≃* PCGroup smallGroup_32_36 :=
  mulEquivOfDecide orbitP10ToGap7
    (by decide +kernel) (by decide +kernel)

end Smallgroups.UsefulTheorems.Order32Certificate
