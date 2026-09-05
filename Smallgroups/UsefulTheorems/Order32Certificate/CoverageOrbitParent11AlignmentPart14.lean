/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart39
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 11, orbit 13, alignment to GAP id 39. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP11OrbitGroup13 := CocycleGroup
  (orbitP11SelectedCocycle 13) (orbitP11SelectedCocycle_consistent 13)
def orbitP11Standard13ForwardIndex : Fin 32 → Fin 32 := ![0, 8, 12, 26, 29, 17, 7, 21, 20, 6, 11, 25, 3, 15, 2, 14, 18, 4, 19, 5, 9, 1, 30, 22, 23, 31, 27, 13, 28, 16, 24, 10]
def orbitP11Standard13BackwardIndex : Fin 32 → Fin 32 := ![0, 21, 14, 12, 17, 19, 9, 6, 1, 20, 31, 10, 2, 27, 15, 13, 29, 5, 16, 18, 8, 7, 23, 24, 30, 11, 3, 26, 28, 4, 22, 25]

def orbitP11Standard13ToGenerated (x : orbitP11OrbitGroup13) : generatedGroup39 where
  fst := (((orbitP11Standard13ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP11Standard13ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP11Standard13FromGenerated (x : generatedGroup39) : orbitP11OrbitGroup13 where
  fst := (((orbitP11Standard13BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP11Standard13BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP11GapEquiv13 :
    orbitP11OrbitGroup13 ≃* PCGroup smallGroup_32_39 :=
  (CycExt.mulEquivOfExplicitInverse orbitP11Standard13ToGenerated orbitP11Standard13FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv39

end Smallgroups.UsefulTheorems.Order32Certificate
