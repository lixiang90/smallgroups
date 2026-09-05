/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent09Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart10
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 9, orbit 2, alignment to GAP id 10. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP9OrbitGroup2 := CocycleGroup
  (orbitP9SelectedCocycle 2) (orbitP9SelectedCocycle_consistent 2)
def orbitP9Standard2ForwardIndex : Fin 32 → Fin 32 := ![0, 21, 11, 30, 5, 28, 9, 6, 1, 20, 2, 27, 24, 23, 10, 31, 18, 17, 4, 29, 8, 7, 15, 12, 3, 26, 25, 22, 19, 16, 14, 13]
def orbitP9Standard2BackwardIndex : Fin 32 → Fin 32 := ![0, 8, 10, 24, 18, 4, 7, 21, 20, 6, 14, 2, 23, 31, 30, 22, 29, 17, 16, 28, 9, 1, 27, 13, 12, 26, 25, 11, 5, 19, 3, 15]

def orbitP9Standard2ToGenerated (x : orbitP9OrbitGroup2) : generatedGroup10 where
  fst := (((orbitP9Standard2ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP9Standard2ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP9Standard2FromGenerated (x : generatedGroup10) : orbitP9OrbitGroup2 where
  fst := (((orbitP9Standard2BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP9Standard2BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP9GapEquiv2 :
    orbitP9OrbitGroup2 ≃* PCGroup smallGroup_32_10 :=
  (CycExt.mulEquivOfExplicitInverse orbitP9Standard2ToGenerated orbitP9Standard2FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv10

end Smallgroups.UsefulTheorems.Order32Certificate
