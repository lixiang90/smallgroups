/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart28
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 11, orbit 4, alignment to GAP id 28. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP11OrbitGroup4 := CocycleGroup
  (orbitP11SelectedCocycle 4) (orbitP11SelectedCocycle_consistent 4)
def orbitP11Standard4ForwardIndex : Fin 32 → Fin 32 := ![0, 8, 16, 28, 11, 25, 23, 31, 1, 9, 27, 13, 15, 3, 17, 29, 6, 20, 10, 24, 22, 30, 4, 18, 26, 12, 14, 2, 7, 21, 5, 19]
def orbitP11Standard4BackwardIndex : Fin 32 → Fin 32 := ![0, 8, 27, 13, 22, 30, 16, 28, 1, 9, 18, 4, 25, 11, 26, 12, 2, 14, 23, 31, 17, 29, 20, 6, 19, 5, 24, 10, 3, 15, 21, 7]

def orbitP11Standard4ToGenerated (x : orbitP11OrbitGroup4) : generatedGroup28 where
  fst := (((orbitP11Standard4ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP11Standard4ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP11Standard4FromGenerated (x : generatedGroup28) : orbitP11OrbitGroup4 where
  fst := (((orbitP11Standard4BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP11Standard4BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP11GapEquiv4 :
    orbitP11OrbitGroup4 ≃* PCGroup smallGroup_32_28 :=
  (CycExt.mulEquivOfExplicitInverse orbitP11Standard4ToGenerated orbitP11Standard4FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv28

end Smallgroups.UsefulTheorems.Order32Certificate
