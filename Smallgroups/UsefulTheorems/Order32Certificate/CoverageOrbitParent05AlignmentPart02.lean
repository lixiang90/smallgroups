/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent05Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart03
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 5, orbit 1, alignment to GAP id 3. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP5OrbitGroup1 := CocycleGroup
  (orbitP5SelectedCocycle 1) (orbitP5SelectedCocycle_consistent 1)
def orbitP5Standard1ForwardIndex : Fin 32 → Fin 32 := ![0, 21, 2, 27, 22, 25, 8, 7, 1, 20, 29, 4, 14, 13, 3, 26, 31, 10, 23, 24, 9, 6, 16, 19, 28, 5, 15, 12, 30, 11, 17, 18]
def orbitP5Standard1BackwardIndex : Fin 32 → Fin 32 := ![0, 8, 2, 14, 11, 25, 21, 7, 6, 20, 17, 29, 27, 13, 12, 26, 22, 30, 31, 23, 9, 1, 4, 18, 19, 5, 15, 3, 24, 10, 28, 16]

def orbitP5Standard1ToGenerated (x : orbitP5OrbitGroup1) : generatedGroup3 where
  fst := (((orbitP5Standard1ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP5Standard1ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP5Standard1FromGenerated (x : generatedGroup3) : orbitP5OrbitGroup1 where
  fst := (((orbitP5Standard1BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP5Standard1BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP5GapEquiv1 :
    orbitP5OrbitGroup1 ≃* PCGroup smallGroup_32_3 :=
  (CycExt.mulEquivOfExplicitInverse orbitP5Standard1ToGenerated orbitP5Standard1FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv3

end Smallgroups.UsefulTheorems.Order32Certificate
