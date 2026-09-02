/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent08Core
import Smallgroups.GAP.Polycyclic.Imported.Order32
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent08AlignmentPart03

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 8, orbit 3, alignment to GAP id 10. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP8OrbitGroup3 := CocycleGroup
  (orbitP8SelectedCocycle 3) (orbitP8SelectedCocycle_consistent 3)
def orbitP8GapExponents3 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 1, 0], [0, 1, 1, 0, 0], [0, 1, 1, 1, 0], [1, 0, 0, 0, 0], [1, 0, 0, 1, 0], [0, 0, 1, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 1], [1, 1, 0, 1, 0], [1, 1, 0, 0, 0], [0, 1, 0, 1, 1], [0, 1, 0, 0, 1], [0, 1, 1, 0, 1], [0, 1, 1, 1, 1], [1, 0, 1, 1, 0], [1, 0, 1, 0, 0], [1, 0, 0, 0, 1], [1, 0, 0, 1, 1], [0, 0, 1, 1, 1], [0, 0, 1, 0, 1], [1, 1, 1, 0, 0], [1, 1, 1, 1, 0], [1, 1, 0, 1, 1], [1, 1, 0, 0, 1], [0, 1, 0, 1, 0], [0, 1, 0, 0, 0], [1, 0, 1, 1, 1], [1, 0, 1, 0, 1], [1, 1, 1, 0, 1], [1, 1, 1, 1, 1]]
def orbitP8ToGap3 (x : orbitP8OrbitGroup3) :
    PCGroup smallGroup_32_10 :=
  evalVec (orbitP8GapExponents3 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_10.layers)

set_option maxHeartbeats 8000000 in
-- Finite verification of the generated 32-element PC isomorphism.
noncomputable def orbitP8GapEquiv3 :
    orbitP8OrbitGroup3 ≃* PCGroup smallGroup_32_10 :=
  mulEquivOfDecide orbitP8ToGap3
    (by decide +kernel) (by decide +kernel)

end Smallgroups.UsefulTheorems.Order32Certificate
