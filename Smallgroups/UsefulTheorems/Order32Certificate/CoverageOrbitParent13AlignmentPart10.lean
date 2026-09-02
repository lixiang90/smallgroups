/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13Core
import Smallgroups.GAP.Polycyclic.Imported.Order32
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13AlignmentPart09

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 13, orbit 9, alignment to GAP id 32. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP13OrbitGroup9 := CocycleGroup
  (orbitP13SelectedCocycle 9) (orbitP13SelectedCocycle_consistent 9)
def orbitP13GapExponents9 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 0, 1, 1], [1, 1, 0, 1, 0], [1, 0, 1, 1, 0], [1, 0, 1, 1, 1], [0, 0, 1, 0, 1], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 1], [0, 1, 1, 0, 0], [0, 1, 1, 0, 1], [1, 1, 1, 1, 0], [1, 1, 1, 1, 1], [1, 1, 0, 0, 1], [1, 1, 0, 0, 0], [1, 0, 0, 0, 1], [1, 0, 0, 0, 0], [1, 0, 1, 0, 0], [1, 0, 1, 0, 1], [0, 0, 1, 1, 1], [0, 0, 1, 1, 0], [0, 1, 0, 1, 1], [0, 1, 0, 1, 0], [0, 1, 1, 1, 0], [0, 1, 1, 1, 1], [1, 1, 1, 0, 1], [1, 1, 1, 0, 0], [1, 0, 0, 1, 1], [1, 0, 0, 1, 0], [0, 1, 0, 0, 0], [0, 1, 0, 0, 1]]
def orbitP13ToGap9 (x : orbitP13OrbitGroup9) :
    PCGroup smallGroup_32_32 :=
  evalVec (orbitP13GapExponents9 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_32.layers)

set_option maxHeartbeats 8000000 in
-- Finite verification of the generated 32-element PC isomorphism.
noncomputable def orbitP13GapEquiv9 :
    orbitP13OrbitGroup9 ≃* PCGroup smallGroup_32_32 :=
  mulEquivOfDecide orbitP13ToGap9
    (by decide +kernel) (by decide +kernel)

end Smallgroups.UsefulTheorems.Order32Certificate
