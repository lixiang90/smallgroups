/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent06Core
import Smallgroups.GAP.Polycyclic.Imported.Order32

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 6, orbit 3, alignment to GAP id 12. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP6OrbitGroup3 := CocycleGroup
  (orbitP6SelectedCocycle 3) (orbitP6SelectedCocycle_consistent 3)
def orbitP6GapExponents3 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 1, 0, 1], [1, 1, 1, 0, 0], [1, 1, 0, 0, 1], [0, 1, 1, 1, 0], [0, 1, 0, 1, 1], [0, 0, 0, 1, 0], [0, 0, 1, 1, 1], [0, 0, 0, 0, 1], [0, 0, 1, 0, 0], [1, 0, 0, 1, 1], [1, 0, 1, 1, 0], [1, 1, 1, 1, 0], [1, 1, 0, 1, 1], [1, 1, 1, 0, 1], [1, 1, 0, 0, 0], [0, 1, 1, 0, 1], [0, 1, 0, 0, 0], [0, 1, 1, 1, 1], [0, 1, 0, 1, 0], [0, 0, 0, 1, 1], [0, 0, 1, 1, 0], [1, 0, 0, 0, 0], [1, 0, 1, 0, 1], [1, 0, 0, 1, 0], [1, 0, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 0, 1, 0], [0, 1, 1, 0, 0], [0, 1, 0, 0, 1], [1, 0, 0, 0, 1], [1, 0, 1, 0, 0]]
def orbitP6ToGap3 (x : orbitP6OrbitGroup3) :
    PCGroup smallGroup_32_12 :=
  evalVec (orbitP6GapExponents3 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_12.layers)

set_option maxHeartbeats 8000000 in
-- Finite verification of the generated 32-element PC isomorphism.
noncomputable def orbitP6GapEquiv3 :
    orbitP6OrbitGroup3 ≃* PCGroup smallGroup_32_12 :=
  mulEquivOfDecide orbitP6ToGap3
    (by decide +kernel) (by decide +kernel)

end Smallgroups.UsefulTheorems.Order32Certificate
