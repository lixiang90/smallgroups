/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent04Core
import Smallgroups.GAP.Polycyclic.Imported.Order32
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent04AlignmentPart03

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 4, orbit 3, alignment to GAP id 2. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP4OrbitGroup3 := CocycleGroup
  (orbitP4SelectedCocycle 3) (orbitP4SelectedCocycle_consistent 3)
def orbitP4GapExponents3 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 1, 1], [0, 1, 1, 0, 0], [0, 1, 1, 1, 1], [1, 1, 1, 1, 0], [1, 1, 1, 0, 1], [0, 0, 1, 1, 1], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1], [1, 0, 1, 1, 1], [1, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 1, 0, 1, 1], [0, 1, 1, 1, 0], [0, 1, 1, 0, 1], [1, 1, 0, 1, 0], [1, 1, 0, 0, 1], [1, 1, 1, 0, 0], [1, 1, 1, 1, 1], [0, 0, 1, 0, 1], [0, 0, 1, 1, 0], [1, 0, 0, 0, 0], [1, 0, 0, 1, 1], [1, 0, 1, 0, 1], [1, 0, 1, 1, 0], [0, 1, 0, 1, 0], [0, 1, 0, 0, 1], [1, 1, 0, 0, 0], [1, 1, 0, 1, 1], [1, 0, 0, 1, 0], [1, 0, 0, 0, 1]]
def orbitP4ToGap3 (x : orbitP4OrbitGroup3) :
    PCGroup smallGroup_32_2 :=
  evalVec (orbitP4GapExponents3 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_2.layers)

set_option maxHeartbeats 8000000 in
-- Finite verification of the generated 32-element PC isomorphism.
noncomputable def orbitP4GapEquiv3 :
    orbitP4OrbitGroup3 ≃* PCGroup smallGroup_32_2 :=
  mulEquivOfDecide orbitP4ToGap3
    (by decide +kernel) (by decide +kernel)

end Smallgroups.UsefulTheorems.Order32Certificate
