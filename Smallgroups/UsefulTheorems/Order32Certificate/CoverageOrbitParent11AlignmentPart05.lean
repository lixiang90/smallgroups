/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11Core
import Smallgroups.GAP.Polycyclic.Imported.Order32
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11AlignmentPart04

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 11, orbit 4, alignment to GAP id 28. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP11OrbitGroup4 := CocycleGroup
  (orbitP11SelectedCocycle 4) (orbitP11SelectedCocycle_consistent 4)
def orbitP11GapExponents4 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 1, 0], [1, 0, 0, 1, 1], [1, 0, 0, 0, 1], [0, 1, 1, 1, 1], [0, 1, 1, 0, 1], [0, 1, 0, 0, 1], [0, 1, 0, 1, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1, 1], [1, 1, 1, 0, 0], [1, 1, 1, 1, 0], [1, 1, 0, 1, 0], [1, 1, 0, 0, 0], [1, 0, 0, 1, 0], [1, 0, 0, 0, 0], [0, 0, 1, 1, 0], [0, 0, 1, 0, 0], [0, 1, 1, 1, 0], [0, 1, 1, 0, 0], [0, 1, 0, 0, 0], [0, 1, 0, 1, 0], [1, 0, 1, 0, 1], [1, 0, 1, 1, 1], [1, 1, 1, 0, 1], [1, 1, 1, 1, 1], [1, 1, 0, 1, 1], [1, 1, 0, 0, 1], [0, 0, 1, 1, 1], [0, 0, 1, 0, 1], [1, 0, 1, 0, 0], [1, 0, 1, 1, 0]]
def orbitP11ToGap4 (x : orbitP11OrbitGroup4) :
    PCGroup smallGroup_32_28 :=
  evalVec (orbitP11GapExponents4 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_28.layers)

set_option maxHeartbeats 8000000 in
-- Finite verification of the generated 32-element PC isomorphism.
noncomputable def orbitP11GapEquiv4 :
    orbitP11OrbitGroup4 ≃* PCGroup smallGroup_32_28 :=
  mulEquivOfDecide orbitP11ToGap4
    (by decide +kernel) (by decide +kernel)

end Smallgroups.UsefulTheorems.Order32Certificate
