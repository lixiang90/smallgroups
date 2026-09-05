/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart28
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 13, orbit 2, alignment to GAP id 28. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP13OrbitGroup2 := CocycleGroup
  (orbitP13SelectedCocycle 2) (orbitP13SelectedCocycle_consistent 2)
def orbitP13Standard2ForwardIndex : Fin 32 → Fin 32 := ![0, 9, 16, 29, 2, 15, 25, 10, 1, 8, 30, 23, 13, 26, 17, 28, 4, 19, 3, 14, 24, 11, 6, 21, 31, 22, 12, 27, 5, 18, 7, 20]
def orbitP13Standard2BackwardIndex : Fin 32 → Fin 32 := ![0, 8, 4, 18, 16, 28, 22, 30, 9, 1, 7, 21, 26, 12, 19, 5, 2, 14, 29, 17, 31, 23, 25, 11, 20, 6, 13, 27, 15, 3, 10, 24]

def orbitP13Standard2ToGenerated (x : orbitP13OrbitGroup2) : generatedGroup28 where
  fst := (((orbitP13Standard2ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP13Standard2ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP13Standard2FromGenerated (x : generatedGroup28) : orbitP13OrbitGroup2 where
  fst := (((orbitP13Standard2BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP13Standard2BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP13GapEquiv2 :
    orbitP13OrbitGroup2 ≃* PCGroup smallGroup_32_28 :=
  (CycExt.mulEquivOfExplicitInverse orbitP13Standard2ToGenerated orbitP13Standard2FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv28

end Smallgroups.UsefulTheorems.Order32Certificate
