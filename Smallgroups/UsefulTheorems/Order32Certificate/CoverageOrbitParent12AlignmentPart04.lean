/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent12Core
import Smallgroups.GAP.Polycyclic.Imported.Order32
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent12AlignmentPart03

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 12, orbit 3, alignment to GAP id 29. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP12OrbitGroup3 := CocycleGroup
  (orbitP12SelectedCocycle 3) (orbitP12SelectedCocycle_consistent 3)
def orbitP12GapExponents3 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 1], [1, 0, 1, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 1, 0], [0, 0, 0, 1, 1], [0, 1, 1, 1, 1], [0, 1, 1, 1, 0], [1, 1, 1, 0, 0], [1, 1, 1, 0, 1], [1, 1, 0, 1, 0], [1, 1, 0, 1, 1], [1, 0, 0, 1, 1], [1, 0, 0, 1, 0], [1, 0, 1, 0, 1], [1, 0, 1, 0, 0], [0, 0, 1, 1, 0], [0, 0, 1, 1, 1], [0, 1, 0, 1, 1], [0, 1, 0, 1, 0], [0, 1, 1, 0, 1], [0, 1, 1, 0, 0], [1, 1, 1, 1, 0], [1, 1, 1, 1, 1], [1, 0, 0, 0, 1], [1, 0, 0, 0, 0], [0, 1, 0, 0, 1], [0, 1, 0, 0, 0]]
def orbitP12ToGap3 (x : orbitP12OrbitGroup3) :
    PCGroup smallGroup_32_29 :=
  evalVec (orbitP12GapExponents3 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_29.layers)

set_option maxHeartbeats 8000000 in
-- Finite verification of the generated 32-element PC isomorphism.
noncomputable def orbitP12GapEquiv3 :
    orbitP12OrbitGroup3 ≃* PCGroup smallGroup_32_29 :=
  mulEquivOfDecide orbitP12ToGap3
    (by decide +kernel) (by decide +kernel)

end Smallgroups.UsefulTheorems.Order32Certificate
