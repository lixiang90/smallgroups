/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11Core
import Smallgroups.GAP.Polycyclic.Imported.Order32
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11AlignmentPart13

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 11, orbit 13, alignment to GAP id 39. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP11OrbitGroup13 := CocycleGroup
  (orbitP11SelectedCocycle 13) (orbitP11SelectedCocycle_consistent 13)
def orbitP11GapExponents13 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [1, 0, 1, 0, 0], [1, 0, 1, 0, 1], [0, 1, 0, 0, 1], [0, 1, 0, 0, 0], [0, 0, 1, 1, 0], [0, 0, 1, 1, 1], [0, 0, 0, 1, 1], [0, 0, 0, 1, 0], [1, 1, 1, 0, 0], [1, 1, 1, 0, 1], [1, 0, 0, 1, 1], [1, 0, 0, 1, 0], [1, 0, 1, 1, 1], [1, 0, 1, 1, 0], [0, 1, 1, 1, 0], [0, 1, 1, 1, 1], [0, 1, 0, 1, 0], [0, 1, 0, 1, 1], [0, 0, 1, 0, 1], [0, 0, 1, 0, 0], [1, 1, 0, 1, 1], [1, 1, 0, 1, 0], [1, 1, 1, 1, 0], [1, 1, 1, 1, 1], [1, 0, 0, 0, 1], [1, 0, 0, 0, 0], [0, 1, 1, 0, 1], [0, 1, 1, 0, 0], [1, 1, 0, 0, 1], [1, 1, 0, 0, 0]]
def orbitP11ToGap13 (x : orbitP11OrbitGroup13) :
    PCGroup smallGroup_32_39 :=
  evalVec (orbitP11GapExponents13 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_39.layers)

set_option maxHeartbeats 8000000 in
-- Finite verification of the generated 32-element PC isomorphism.
noncomputable def orbitP11GapEquiv13 :
    orbitP11OrbitGroup13 ≃* PCGroup smallGroup_32_39 :=
  mulEquivOfDecide orbitP11ToGap13
    (by decide +kernel) (by decide +kernel)

end Smallgroups.UsefulTheorems.Order32Certificate
