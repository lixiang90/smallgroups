/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart26
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 13, orbit 8, alignment to GAP id 26. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP13OrbitGroup8 := CocycleGroup
  (orbitP13SelectedCocycle 8) (orbitP13SelectedCocycle_consistent 8)
def orbitP13Standard8ForwardIndex : Fin 32 → Fin 32 := ![0, 9, 13, 26, 3, 14, 23, 30, 1, 8, 6, 21, 18, 5, 12, 27, 17, 28, 2, 15, 22, 31, 24, 11, 7, 20, 4, 19, 16, 29, 10, 25]
def orbitP13Standard8BackwardIndex : Fin 32 → Fin 32 := ![0, 8, 18, 4, 26, 13, 10, 24, 9, 1, 30, 23, 14, 2, 5, 19, 28, 16, 12, 27, 25, 11, 20, 6, 22, 31, 3, 15, 17, 29, 7, 21]

def orbitP13Standard8ToGenerated (x : orbitP13OrbitGroup8) : generatedGroup26 where
  fst := (((orbitP13Standard8ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP13Standard8ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP13Standard8FromGenerated (x : generatedGroup26) : orbitP13OrbitGroup8 where
  fst := (((orbitP13Standard8BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP13Standard8BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP13GapEquiv8 :
    orbitP13OrbitGroup8 ≃* PCGroup smallGroup_32_26 :=
  (CycExt.mulEquivOfExplicitInverse orbitP13Standard8ToGenerated orbitP13Standard8FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv26

end Smallgroups.UsefulTheorems.Order32Certificate
