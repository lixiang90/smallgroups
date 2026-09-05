/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent09Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart14
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 9, orbit 1, alignment to GAP id 14. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP9OrbitGroup1 := CocycleGroup
  (orbitP9SelectedCocycle 1) (orbitP9SelectedCocycle_consistent 1)
def orbitP9Standard1ForwardIndex : Fin 32 → Fin 32 := ![0, 9, 22, 31, 15, 2, 6, 21, 1, 8, 18, 5, 10, 25, 23, 30, 27, 12, 14, 3, 7, 20, 28, 17, 19, 4, 11, 24, 26, 13, 29, 16]
def orbitP9Standard1BackwardIndex : Fin 32 → Fin 32 := ![0, 8, 5, 19, 25, 11, 6, 20, 9, 1, 12, 26, 17, 29, 18, 4, 31, 23, 10, 24, 21, 7, 2, 14, 27, 13, 28, 16, 22, 30, 15, 3]

def orbitP9Standard1ToGenerated (x : orbitP9OrbitGroup1) : generatedGroup14 where
  fst := (((orbitP9Standard1ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP9Standard1ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP9Standard1FromGenerated (x : generatedGroup14) : orbitP9OrbitGroup1 where
  fst := (((orbitP9Standard1BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP9Standard1BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP9GapEquiv1 :
    orbitP9OrbitGroup1 ≃* PCGroup smallGroup_32_14 :=
  (CycExt.mulEquivOfExplicitInverse orbitP9Standard1ToGenerated orbitP9Standard1FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv14

end Smallgroups.UsefulTheorems.Order32Certificate
