/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart41
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 11, orbit 16, alignment to GAP id 41. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP11OrbitGroup16 := CocycleGroup
  (orbitP11SelectedCocycle 16) (orbitP11SelectedCocycle_consistent 16)
def orbitP11Standard16ForwardIndex : Fin 32 → Fin 32 := ![0, 8, 19, 5, 15, 3, 21, 7, 6, 20, 30, 22, 16, 28, 29, 17, 12, 26, 27, 13, 9, 1, 11, 25, 24, 10, 18, 4, 2, 14, 23, 31]
def orbitP11Standard16BackwardIndex : Fin 32 → Fin 32 := ![0, 21, 28, 5, 27, 3, 8, 7, 1, 20, 25, 22, 16, 19, 29, 4, 12, 15, 26, 2, 9, 6, 11, 30, 24, 23, 17, 18, 13, 14, 10, 31]

def orbitP11Standard16ToGenerated (x : orbitP11OrbitGroup16) : generatedGroup41 where
  fst := (((orbitP11Standard16ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP11Standard16ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP11Standard16FromGenerated (x : generatedGroup41) : orbitP11OrbitGroup16 where
  fst := (((orbitP11Standard16BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP11Standard16BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP11GapEquiv16 :
    orbitP11OrbitGroup16 ≃* PCGroup smallGroup_32_41 :=
  (CycExt.mulEquivOfExplicitInverse orbitP11Standard16ToGenerated orbitP11Standard16FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv41

end Smallgroups.UsefulTheorems.Order32Certificate
