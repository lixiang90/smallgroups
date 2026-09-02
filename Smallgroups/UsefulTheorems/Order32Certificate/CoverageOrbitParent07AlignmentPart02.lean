/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent07Core
import Smallgroups.GAP.Polycyclic.Imported.Order32
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent07AlignmentPart01

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 7, orbit 1, alignment to GAP id 14. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP7OrbitGroup1 := CocycleGroup
  (orbitP7SelectedCocycle 1) (orbitP7SelectedCocycle_consistent 1)
def orbitP7GapExponents1 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 1, 0], [1, 0, 0, 0, 1], [1, 0, 0, 1, 1], [1, 1, 1, 0, 1], [1, 1, 1, 1, 1], [0, 0, 1, 0, 1], [0, 0, 1, 1, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1, 1], [0, 1, 1, 0, 0], [0, 1, 1, 1, 0], [1, 0, 1, 0, 0], [1, 0, 1, 1, 0], [1, 0, 0, 0, 0], [1, 0, 0, 1, 0], [1, 1, 0, 0, 1], [1, 1, 0, 1, 1], [1, 1, 1, 0, 0], [1, 1, 1, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 1, 0], [0, 1, 0, 0, 0], [0, 1, 0, 1, 0], [0, 1, 1, 0, 1], [0, 1, 1, 1, 1], [1, 0, 1, 0, 1], [1, 0, 1, 1, 1], [1, 1, 0, 0, 0], [1, 1, 0, 1, 0], [0, 1, 0, 0, 1], [0, 1, 0, 1, 1]]
def orbitP7ToGap1 (x : orbitP7OrbitGroup1) :
    PCGroup smallGroup_32_14 :=
  evalVec (orbitP7GapExponents1 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_14.layers)

set_option maxHeartbeats 8000000 in
-- Finite verification of the generated 32-element PC isomorphism.
noncomputable def orbitP7GapEquiv1 :
    orbitP7OrbitGroup1 ≃* PCGroup smallGroup_32_14 :=
  mulEquivOfDecide orbitP7ToGap1
    (by decide +kernel) (by decide +kernel)

end Smallgroups.UsefulTheorems.Order32Certificate
