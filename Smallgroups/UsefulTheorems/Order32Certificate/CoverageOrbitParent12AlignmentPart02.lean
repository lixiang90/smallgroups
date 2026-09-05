/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent12Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart26
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 12, orbit 1, alignment to GAP id 26. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP12OrbitGroup1 := CocycleGroup
  (orbitP12SelectedCocycle 1) (orbitP12SelectedCocycle_consistent 1)
def orbitP12Standard1ForwardIndex : Fin 32 → Fin 32 := ![0, 8, 6, 20, 2, 14, 23, 31, 1, 9, 12, 26, 11, 25, 7, 21, 17, 29, 3, 15, 22, 30, 5, 19, 13, 27, 10, 24, 16, 28, 4, 18]
def orbitP12Standard1BackwardIndex : Fin 32 → Fin 32 := ![0, 8, 4, 18, 30, 22, 2, 14, 1, 9, 26, 12, 10, 24, 5, 19, 28, 16, 31, 23, 3, 15, 20, 6, 27, 13, 11, 25, 29, 17, 21, 7]

def orbitP12Standard1ToGenerated (x : orbitP12OrbitGroup1) : generatedGroup26 where
  fst := (((orbitP12Standard1ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP12Standard1ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP12Standard1FromGenerated (x : generatedGroup26) : orbitP12OrbitGroup1 where
  fst := (((orbitP12Standard1BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP12Standard1BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP12GapEquiv1 :
    orbitP12OrbitGroup1 ≃* PCGroup smallGroup_32_26 :=
  (CycExt.mulEquivOfExplicitInverse orbitP12Standard1ToGenerated orbitP12Standard1FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv26

end Smallgroups.UsefulTheorems.Order32Certificate
