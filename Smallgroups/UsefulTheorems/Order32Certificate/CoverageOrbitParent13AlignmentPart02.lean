/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart25
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 13, orbit 1, alignment to GAP id 25. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP13OrbitGroup1 := CocycleGroup
  (orbitP13SelectedCocycle 1) (orbitP13SelectedCocycle_consistent 1)
def orbitP13Standard1ForwardIndex : Fin 32 → Fin 32 := ![0, 9, 17, 28, 24, 11, 22, 31, 1, 8, 27, 12, 3, 14, 16, 29, 21, 6, 25, 10, 23, 30, 18, 5, 26, 13, 2, 15, 20, 7, 19, 4]
def orbitP13Standard1BackwardIndex : Fin 32 → Fin 32 := ![0, 8, 26, 12, 31, 23, 17, 29, 9, 1, 19, 5, 11, 25, 13, 27, 14, 2, 22, 30, 28, 16, 6, 20, 4, 18, 24, 10, 3, 15, 21, 7]

def orbitP13Standard1ToGenerated (x : orbitP13OrbitGroup1) : generatedGroup25 where
  fst := (((orbitP13Standard1ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP13Standard1ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP13Standard1FromGenerated (x : generatedGroup25) : orbitP13OrbitGroup1 where
  fst := (((orbitP13Standard1BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP13Standard1BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP13GapEquiv1 :
    orbitP13OrbitGroup1 ≃* PCGroup smallGroup_32_25 :=
  (CycExt.mulEquivOfExplicitInverse orbitP13Standard1ToGenerated orbitP13Standard1FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv25

end Smallgroups.UsefulTheorems.Order32Certificate
