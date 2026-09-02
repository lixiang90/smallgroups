/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent06Core
import Smallgroups.GAP.Polycyclic.Imported.Order32
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent06AlignmentPart01

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 6, orbit 1, alignment to GAP id 4. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP6OrbitGroup1 := CocycleGroup
  (orbitP6SelectedCocycle 1) (orbitP6SelectedCocycle_consistent 1)
def orbitP6GapExponents1 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 1, 1], [1, 1, 1, 0, 1], [1, 1, 1, 1, 0], [0, 1, 1, 0, 0], [0, 1, 1, 1, 1], [0, 0, 1, 0, 1], [0, 0, 1, 1, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [1, 0, 0, 0, 1], [1, 0, 0, 1, 0], [1, 1, 0, 0, 1], [1, 1, 0, 1, 0], [1, 1, 1, 0, 0], [1, 1, 1, 1, 1], [0, 1, 0, 0, 0], [0, 1, 0, 1, 1], [0, 1, 1, 0, 1], [0, 1, 1, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 1, 1], [1, 0, 1, 0, 0], [1, 0, 1, 1, 1], [1, 0, 0, 0, 0], [1, 0, 0, 1, 1], [1, 1, 0, 0, 0], [1, 1, 0, 1, 1], [0, 1, 0, 0, 1], [0, 1, 0, 1, 0], [1, 0, 1, 0, 1], [1, 0, 1, 1, 0]]
def orbitP6ToGap1 (x : orbitP6OrbitGroup1) :
    PCGroup smallGroup_32_4 :=
  evalVec (orbitP6GapExponents1 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_4.layers)

set_option maxHeartbeats 8000000 in
-- Finite verification of the generated 32-element PC isomorphism.
noncomputable def orbitP6GapEquiv1 :
    orbitP6OrbitGroup1 ≃* PCGroup smallGroup_32_4 :=
  mulEquivOfDecide orbitP6ToGap1
    (by decide +kernel) (by decide +kernel)

end Smallgroups.UsefulTheorems.Order32Certificate
