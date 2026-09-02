/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13Core
import Smallgroups.GAP.Polycyclic.Imported.Order32
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13AlignmentPart08

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 13, orbit 8, alignment to GAP id 26. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP13OrbitGroup8 := CocycleGroup
  (orbitP13SelectedCocycle 8) (orbitP13SelectedCocycle_consistent 8)
def orbitP13GapExponents8 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 0, 0, 0], [1, 0, 0, 0, 1], [0, 0, 1, 1, 0], [0, 0, 1, 1, 1], [0, 0, 0, 1, 0], [0, 0, 0, 1, 1], [0, 1, 0, 1, 0], [0, 1, 0, 1, 1], [1, 1, 1, 1, 0], [1, 1, 1, 1, 1], [1, 1, 0, 1, 0], [1, 1, 0, 1, 1], [1, 0, 1, 1, 1], [1, 0, 1, 1, 0], [1, 0, 0, 1, 0], [1, 0, 0, 1, 1], [0, 0, 1, 0, 0], [0, 0, 1, 0, 1], [0, 1, 1, 0, 1], [0, 1, 1, 0, 0], [0, 1, 0, 0, 0], [0, 1, 0, 0, 1], [1, 1, 1, 0, 1], [1, 1, 1, 0, 0], [1, 0, 1, 0, 1], [1, 0, 1, 0, 0], [0, 1, 1, 1, 0], [0, 1, 1, 1, 1]]
def orbitP13ToGap8 (x : orbitP13OrbitGroup8) :
    PCGroup smallGroup_32_26 :=
  evalVec (orbitP13GapExponents8 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_26.layers)

set_option maxHeartbeats 8000000 in
-- Finite verification of the generated 32-element PC isomorphism.
noncomputable def orbitP13GapEquiv8 :
    orbitP13OrbitGroup8 ≃* PCGroup smallGroup_32_26 :=
  mulEquivOfDecide orbitP13ToGap8
    (by decide +kernel) (by decide +kernel)

end Smallgroups.UsefulTheorems.Order32Certificate
