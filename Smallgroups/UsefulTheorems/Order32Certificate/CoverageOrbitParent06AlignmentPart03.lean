/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent06Core
import Smallgroups.GAP.Polycyclic.Imported.Order32
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent06AlignmentPart02

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 6, orbit 2, alignment to GAP id 5. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP6OrbitGroup2 := CocycleGroup
  (orbitP6SelectedCocycle 2) (orbitP6SelectedCocycle_consistent 2)
def orbitP6GapExponents2 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 1, 0, 1], [1, 0, 0, 0, 1], [1, 0, 1, 0, 0], [0, 1, 1, 0, 1], [0, 1, 0, 0, 0], [0, 0, 1, 1, 1], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1], [0, 0, 1, 0, 0], [1, 1, 1, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0], [1, 0, 0, 1, 1], [1, 0, 0, 0, 0], [1, 0, 1, 0, 1], [0, 1, 0, 1, 0], [0, 1, 1, 1, 1], [0, 1, 1, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [0, 0, 0, 1, 1], [1, 1, 0, 1, 1], [1, 1, 1, 1, 0], [1, 1, 1, 0, 1], [1, 1, 0, 0, 0], [1, 0, 1, 1, 1], [1, 0, 0, 1, 0], [0, 1, 0, 1, 1], [0, 1, 1, 1, 0], [1, 1, 0, 1, 0], [1, 1, 1, 1, 1]]
def orbitP6ToGap2 (x : orbitP6OrbitGroup2) :
    PCGroup smallGroup_32_5 :=
  evalVec (orbitP6GapExponents2 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_5.layers)

set_option maxHeartbeats 8000000 in
-- Finite verification of the generated 32-element PC isomorphism.
noncomputable def orbitP6GapEquiv2 :
    orbitP6OrbitGroup2 ≃* PCGroup smallGroup_32_5 :=
  mulEquivOfDecide orbitP6ToGap2
    (by decide +kernel) (by decide +kernel)

end Smallgroups.UsefulTheorems.Order32Certificate
