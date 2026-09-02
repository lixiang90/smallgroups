/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10Core
import Smallgroups.GAP.Polycyclic.Imported.Order32
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10AlignmentPart03

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 10, orbit 3, alignment to GAP id 23. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP10OrbitGroup3 := CocycleGroup
  (orbitP10SelectedCocycle 3) (orbitP10SelectedCocycle_consistent 3)
def orbitP10GapExponents3 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 1, 0], [1, 0, 0, 1, 1], [1, 0, 0, 0, 1], [0, 1, 1, 1, 1], [0, 1, 1, 0, 1], [0, 1, 0, 0, 1], [0, 1, 0, 1, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1, 1], [1, 1, 1, 0, 0], [1, 1, 1, 1, 0], [1, 1, 0, 1, 0], [1, 1, 0, 0, 0], [1, 0, 0, 1, 0], [1, 0, 0, 0, 0], [0, 0, 1, 1, 0], [0, 0, 1, 0, 0], [0, 1, 1, 1, 0], [0, 1, 1, 0, 0], [0, 1, 0, 0, 0], [0, 1, 0, 1, 0], [1, 0, 1, 0, 1], [1, 0, 1, 1, 1], [1, 1, 1, 0, 1], [1, 1, 1, 1, 1], [1, 1, 0, 1, 1], [1, 1, 0, 0, 1], [0, 0, 1, 1, 1], [0, 0, 1, 0, 1], [1, 0, 1, 0, 0], [1, 0, 1, 1, 0]]
def orbitP10ToGap3 (x : orbitP10OrbitGroup3) :
    PCGroup smallGroup_32_23 :=
  evalVec (orbitP10GapExponents3 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_23.layers)

set_option maxHeartbeats 8000000 in
-- Finite verification of the generated 32-element PC isomorphism.
noncomputable def orbitP10GapEquiv3 :
    orbitP10OrbitGroup3 ≃* PCGroup smallGroup_32_23 :=
  mulEquivOfDecide orbitP10ToGap3
    (by decide +kernel) (by decide +kernel)

end Smallgroups.UsefulTheorems.Order32Certificate
