/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent05Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart05
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 5, orbit 2, alignment to GAP id 5. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP5OrbitGroup2 := CocycleGroup
  (orbitP5SelectedCocycle 2) (orbitP5SelectedCocycle_consistent 2)
def orbitP5Standard2ForwardIndex : Fin 32 → Fin 32 := ![0, 6, 30, 25, 19, 29, 9, 20, 1, 7, 13, 3, 23, 10, 31, 24, 4, 16, 18, 28, 8, 21, 26, 14, 12, 2, 22, 11, 5, 17, 27, 15]
def orbitP5Standard2BackwardIndex : Fin 32 → Fin 32 := ![0, 8, 25, 11, 16, 28, 1, 9, 20, 6, 13, 27, 24, 10, 23, 31, 17, 29, 18, 4, 7, 21, 26, 12, 15, 3, 22, 30, 19, 5, 2, 14]

def orbitP5Standard2ToGenerated (x : orbitP5OrbitGroup2) : generatedGroup5 where
  fst := (((orbitP5Standard2ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP5Standard2ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP5Standard2FromGenerated (x : generatedGroup5) : orbitP5OrbitGroup2 where
  fst := (((orbitP5Standard2BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP5Standard2BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP5GapEquiv2 :
    orbitP5OrbitGroup2 ≃* PCGroup smallGroup_32_5 :=
  (CycExt.mulEquivOfExplicitInverse orbitP5Standard2ToGenerated orbitP5Standard2FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv5

end Smallgroups.UsefulTheorems.Order32Certificate
