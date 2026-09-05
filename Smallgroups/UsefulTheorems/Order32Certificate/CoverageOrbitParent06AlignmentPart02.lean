/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent06Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart04
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 6, orbit 1, alignment to GAP id 4. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP6OrbitGroup1 := CocycleGroup
  (orbitP6SelectedCocycle 1) (orbitP6SelectedCocycle_consistent 1)
def orbitP6Standard1ForwardIndex : Fin 32 → Fin 32 := ![0, 21, 2, 27, 24, 23, 9, 6, 1, 20, 5, 28, 14, 13, 3, 26, 10, 31, 25, 22, 8, 7, 18, 17, 4, 29, 15, 12, 11, 30, 19, 16]
def orbitP6Standard1BackwardIndex : Fin 32 → Fin 32 := ![0, 8, 2, 14, 24, 10, 7, 21, 20, 6, 16, 28, 27, 13, 12, 26, 31, 23, 22, 30, 9, 1, 19, 5, 4, 18, 15, 3, 11, 25, 29, 17]

def orbitP6Standard1ToGenerated (x : orbitP6OrbitGroup1) : generatedGroup4 where
  fst := (((orbitP6Standard1ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP6Standard1ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP6Standard1FromGenerated (x : generatedGroup4) : orbitP6OrbitGroup1 where
  fst := (((orbitP6Standard1BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP6Standard1BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP6GapEquiv1 :
    orbitP6OrbitGroup1 ≃* PCGroup smallGroup_32_4 :=
  (CycExt.mulEquivOfExplicitInverse orbitP6Standard1ToGenerated orbitP6Standard1FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv4

end Smallgroups.UsefulTheorems.Order32Certificate
