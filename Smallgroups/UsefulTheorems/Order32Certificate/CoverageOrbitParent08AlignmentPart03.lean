/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent08Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart09
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 8, orbit 2, alignment to GAP id 9. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP8OrbitGroup2 := CocycleGroup
  (orbitP8SelectedCocycle 2) (orbitP8SelectedCocycle_consistent 2)
def orbitP8Standard2ForwardIndex : Fin 32 → Fin 32 := ![0, 21, 22, 25, 5, 28, 9, 6, 1, 20, 13, 14, 30, 11, 23, 24, 19, 16, 4, 29, 8, 7, 26, 3, 12, 15, 31, 10, 18, 17, 27, 2]
def orbitP8Standard2BackwardIndex : Fin 32 → Fin 32 := ![0, 8, 31, 23, 18, 4, 7, 21, 20, 6, 27, 13, 24, 10, 11, 25, 17, 29, 28, 16, 9, 1, 2, 14, 15, 3, 22, 30, 5, 19, 12, 26]

def orbitP8Standard2ToGenerated (x : orbitP8OrbitGroup2) : generatedGroup9 where
  fst := (((orbitP8Standard2ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP8Standard2ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP8Standard2FromGenerated (x : generatedGroup9) : orbitP8OrbitGroup2 where
  fst := (((orbitP8Standard2BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP8Standard2BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP8GapEquiv2 :
    orbitP8OrbitGroup2 ≃* PCGroup smallGroup_32_9 :=
  (CycExt.mulEquivOfExplicitInverse orbitP8Standard2ToGenerated orbitP8Standard2FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv9

end Smallgroups.UsefulTheorems.Order32Certificate
