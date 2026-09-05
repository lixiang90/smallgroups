/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart23
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 11, orbit 6, alignment to GAP id 23. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP11OrbitGroup6 := CocycleGroup
  (orbitP11SelectedCocycle 6) (orbitP11SelectedCocycle_consistent 6)
def orbitP11Standard6ForwardIndex : Fin 32 → Fin 32 := ![0, 8, 25, 11, 13, 27, 21, 7, 6, 20, 4, 18, 30, 22, 31, 23, 2, 14, 3, 15, 9, 1, 29, 17, 16, 28, 24, 10, 12, 26, 19, 5]
def orbitP11Standard6BackwardIndex : Fin 32 → Fin 32 := ![0, 21, 16, 18, 10, 31, 8, 7, 1, 20, 27, 3, 28, 4, 17, 19, 24, 23, 11, 30, 9, 6, 13, 15, 26, 2, 29, 5, 25, 22, 12, 14]

def orbitP11Standard6ToGenerated (x : orbitP11OrbitGroup6) : generatedGroup23 where
  fst := (((orbitP11Standard6ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP11Standard6ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP11Standard6FromGenerated (x : generatedGroup23) : orbitP11OrbitGroup6 where
  fst := (((orbitP11Standard6BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP11Standard6BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP11GapEquiv6 :
    orbitP11OrbitGroup6 ≃* PCGroup smallGroup_32_23 :=
  (CycExt.mulEquivOfExplicitInverse orbitP11Standard6ToGenerated orbitP11Standard6FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv23

end Smallgroups.UsefulTheorems.Order32Certificate
