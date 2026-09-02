/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent05Core
import Smallgroups.GAP.Polycyclic.Imported.Order32
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent05AlignmentPart01

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 5, orbit 1, alignment to GAP id 3. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP5OrbitGroup1 := CocycleGroup
  (orbitP5SelectedCocycle 1) (orbitP5SelectedCocycle_consistent 1)
def orbitP5GapExponents1 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 1, 0], [1, 0, 1, 0, 0], [1, 0, 1, 1, 0], [0, 1, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 1, 1, 1], [0, 0, 1, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1, 1], [1, 1, 1, 1, 0], [1, 1, 1, 0, 0], [1, 0, 0, 1, 0], [1, 0, 0, 0, 0], [1, 0, 1, 0, 1], [1, 0, 1, 1, 1], [0, 1, 1, 1, 1], [0, 1, 1, 0, 1], [0, 1, 0, 0, 1], [0, 1, 0, 1, 1], [0, 0, 1, 1, 0], [0, 0, 1, 0, 0], [1, 1, 0, 0, 0], [1, 1, 0, 1, 0], [1, 1, 1, 1, 1], [1, 1, 1, 0, 1], [1, 0, 0, 1, 1], [1, 0, 0, 0, 1], [0, 1, 1, 1, 0], [0, 1, 1, 0, 0], [1, 1, 0, 0, 1], [1, 1, 0, 1, 1]]
def orbitP5ToGap1 (x : orbitP5OrbitGroup1) :
    PCGroup smallGroup_32_3 :=
  evalVec (orbitP5GapExponents1 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_3.layers)

set_option maxHeartbeats 8000000 in
-- Finite verification of the generated 32-element PC isomorphism.
noncomputable def orbitP5GapEquiv1 :
    orbitP5OrbitGroup1 ≃* PCGroup smallGroup_32_3 :=
  mulEquivOfDecide orbitP5ToGap1
    (by decide +kernel) (by decide +kernel)

end Smallgroups.UsefulTheorems.Order32Certificate
