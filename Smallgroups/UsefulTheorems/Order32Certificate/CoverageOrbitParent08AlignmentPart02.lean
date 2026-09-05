/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent08Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart13
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 8, orbit 1, alignment to GAP id 13. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP8OrbitGroup1 := CocycleGroup
  (orbitP8SelectedCocycle 1) (orbitP8SelectedCocycle_consistent 1)
def orbitP8Standard1ForwardIndex : Fin 32 → Fin 32 := ![0, 9, 31, 22, 27, 12, 6, 21, 1, 8, 17, 28, 25, 10, 30, 23, 15, 2, 26, 13, 7, 20, 5, 18, 16, 29, 24, 11, 14, 3, 4, 19]
def orbitP8Standard1BackwardIndex : Fin 32 → Fin 32 := ![0, 8, 17, 29, 30, 22, 6, 20, 9, 1, 13, 27, 5, 19, 28, 16, 24, 10, 23, 31, 21, 7, 3, 15, 26, 12, 18, 4, 11, 25, 14, 2]

def orbitP8Standard1ToGenerated (x : orbitP8OrbitGroup1) : generatedGroup13 where
  fst := (((orbitP8Standard1ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP8Standard1ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP8Standard1FromGenerated (x : generatedGroup13) : orbitP8OrbitGroup1 where
  fst := (((orbitP8Standard1BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP8Standard1BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP8GapEquiv1 :
    orbitP8OrbitGroup1 ≃* PCGroup smallGroup_32_13 :=
  (CycExt.mulEquivOfExplicitInverse orbitP8Standard1ToGenerated orbitP8Standard1FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv13

end Smallgroups.UsefulTheorems.Order32Certificate
