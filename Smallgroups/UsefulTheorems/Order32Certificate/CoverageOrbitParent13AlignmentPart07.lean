/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart24
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 13, orbit 6, alignment to GAP id 24. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP13OrbitGroup6 := CocycleGroup
  (orbitP13SelectedCocycle 6) (orbitP13SelectedCocycle_consistent 6)
def orbitP13Standard6ForwardIndex : Fin 32 → Fin 32 := ![0, 9, 3, 14, 10, 25, 17, 28, 8, 1, 18, 5, 30, 23, 2, 15, 27, 12, 11, 24, 29, 16, 6, 21, 4, 19, 31, 22, 26, 13, 20, 7]
def orbitP13Standard6BackwardIndex : Fin 32 → Fin 32 := ![0, 9, 14, 2, 24, 11, 22, 31, 8, 1, 4, 18, 17, 29, 3, 15, 21, 6, 10, 25, 30, 23, 27, 13, 19, 5, 28, 16, 7, 20, 12, 26]

def orbitP13Standard6ToGenerated (x : orbitP13OrbitGroup6) : generatedGroup24 where
  fst := (((orbitP13Standard6ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP13Standard6ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP13Standard6FromGenerated (x : generatedGroup24) : orbitP13OrbitGroup6 where
  fst := (((orbitP13Standard6BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP13Standard6BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP13GapEquiv6 :
    orbitP13OrbitGroup6 ≃* PCGroup smallGroup_32_24 :=
  (CycExt.mulEquivOfExplicitInverse orbitP13Standard6ToGenerated orbitP13Standard6FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv24

end Smallgroups.UsefulTheorems.Order32Certificate
