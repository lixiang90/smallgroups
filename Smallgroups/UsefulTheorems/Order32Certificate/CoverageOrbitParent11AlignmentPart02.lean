/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart25
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 11, orbit 1, alignment to GAP id 25. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP11OrbitGroup1 := CocycleGroup
  (orbitP11SelectedCocycle 1) (orbitP11SelectedCocycle_consistent 1)
def orbitP11Standard1ForwardIndex : Fin 32 → Fin 32 := ![0, 8, 19, 5, 14, 2, 23, 31, 1, 9, 10, 24, 26, 12, 18, 4, 29, 17, 15, 3, 22, 30, 7, 21, 11, 25, 27, 13, 28, 16, 6, 20]
def orbitP11Standard1BackwardIndex : Fin 32 → Fin 32 := ![0, 8, 5, 19, 15, 3, 30, 22, 1, 9, 10, 24, 13, 27, 4, 18, 29, 17, 14, 2, 31, 23, 20, 6, 11, 25, 12, 26, 28, 16, 21, 7]

def orbitP11Standard1ToGenerated (x : orbitP11OrbitGroup1) : generatedGroup25 where
  fst := (((orbitP11Standard1ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP11Standard1ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP11Standard1FromGenerated (x : generatedGroup25) : orbitP11OrbitGroup1 where
  fst := (((orbitP11Standard1BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP11Standard1BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP11GapEquiv1 :
    orbitP11OrbitGroup1 ≃* PCGroup smallGroup_32_25 :=
  (CycExt.mulEquivOfExplicitInverse orbitP11Standard1ToGenerated orbitP11Standard1FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv25

end Smallgroups.UsefulTheorems.Order32Certificate
