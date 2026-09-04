/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.GAP.Polycyclic.Imported.Order32

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 14, orbit 6, alignment to GAP id 50. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP14OrbitGroup6 := CocycleGroup
  (orbitP14SelectedCocycle 6) (orbitP14SelectedCocycle_consistent 6)
def orbitP14GapExponents6 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [0, 1, 0, 1, 0], [0, 1, 0, 1, 1], [1, 1, 1, 1, 0], [1, 1, 1, 1, 1], [0, 0, 1, 0, 0], [0, 0, 1, 0, 1], [0, 1, 0, 0, 1], [0, 1, 0, 0, 0], [1, 0, 1, 0, 1], [1, 0, 1, 0, 0], [0, 1, 1, 1, 0], [0, 1, 1, 1, 1], [0, 0, 0, 1, 0], [0, 0, 0, 1, 1], [1, 1, 0, 1, 1], [1, 1, 0, 1, 0], [1, 0, 1, 1, 0], [1, 0, 1, 1, 1], [0, 1, 1, 0, 1], [0, 1, 1, 0, 0], [1, 0, 0, 0, 1], [1, 0, 0, 0, 0], [1, 1, 1, 0, 1], [1, 1, 1, 0, 0], [0, 0, 1, 1, 1], [0, 0, 1, 1, 0], [1, 0, 0, 1, 0], [1, 0, 0, 1, 1], [1, 1, 0, 0, 1], [1, 1, 0, 0, 0]]
def orbitP14ToGap6 (x : orbitP14OrbitGroup6) :
    PCGroup smallGroup_32_50 :=
  evalVec (orbitP14GapExponents6 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_50.layers)

set_option maxHeartbeats 8000000 in
-- Finite verification of the generated 32-element PC isomorphism.
noncomputable def orbitP14GapEquiv6 :
    orbitP14OrbitGroup6 ≃* PCGroup smallGroup_32_50 :=
  mulEquivOfDecide orbitP14ToGap6
    (by decide +kernel) (by decide +kernel)

end Smallgroups.UsefulTheorems.Order32Certificate
