/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11Core
import Smallgroups.GAP.Polycyclic.Imported.Order32

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 11, orbit 11, alignment to GAP id 22. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP11OrbitGroup11 := CocycleGroup
  (orbitP11SelectedCocycle 11) (orbitP11SelectedCocycle_consistent 11)
def orbitP11GapExponents11 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [1, 0, 0, 1, 1], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [0, 1, 1, 0, 1], [0, 0, 1, 1, 1], [0, 0, 1, 1, 0], [0, 0, 0, 1, 1], [0, 0, 0, 1, 0], [1, 1, 1, 1, 0], [1, 1, 1, 1, 1], [1, 0, 1, 0, 1], [1, 0, 1, 0, 0], [1, 0, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0], [0, 1, 0, 1, 1], [0, 1, 1, 1, 1], [0, 1, 1, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 1], [1, 1, 0, 0, 1], [1, 1, 0, 0, 0], [1, 1, 1, 0, 1], [1, 1, 1, 0, 0], [1, 0, 1, 1, 0], [1, 0, 1, 1, 1], [0, 1, 0, 0, 1], [0, 1, 0, 0, 0], [1, 1, 0, 1, 0], [1, 1, 0, 1, 1]]
def orbitP11ToGap11 (x : orbitP11OrbitGroup11) :
    PCGroup smallGroup_32_22 :=
  evalVec (orbitP11GapExponents11 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_22.layers)

set_option maxHeartbeats 8000000 in
-- Finite verification of the generated 32-element PC isomorphism.
noncomputable def orbitP11GapEquiv11 :
    orbitP11OrbitGroup11 ≃* PCGroup smallGroup_32_22 :=
  mulEquivOfDecide orbitP11ToGap11
    (by decide +kernel) (by decide +kernel)

end Smallgroups.UsefulTheorems.Order32Certificate
