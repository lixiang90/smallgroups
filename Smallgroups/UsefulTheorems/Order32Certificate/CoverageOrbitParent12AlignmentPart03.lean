/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent12Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart35
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 12, orbit 2, alignment to GAP id 35. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP12OrbitGroup2 := CocycleGroup
  (orbitP12SelectedCocycle 2) (orbitP12SelectedCocycle_consistent 2)
def orbitP12Standard2ForwardIndex : Fin 32 → Fin 32 := ![0, 9, 2, 15, 17, 28, 10, 25, 1, 8, 22, 31, 5, 18, 3, 14, 13, 26, 16, 29, 11, 24, 7, 20, 23, 30, 4, 19, 12, 27, 6, 21]
def orbitP12Standard2BackwardIndex : Fin 32 → Fin 32 := ![0, 8, 2, 14, 26, 12, 30, 22, 9, 1, 6, 20, 28, 16, 15, 3, 18, 4, 13, 27, 23, 31, 10, 24, 21, 7, 17, 29, 5, 19, 25, 11]

def orbitP12Standard2ToGenerated (x : orbitP12OrbitGroup2) : generatedGroup35 where
  fst := (((orbitP12Standard2ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP12Standard2ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP12Standard2FromGenerated (x : generatedGroup35) : orbitP12OrbitGroup2 where
  fst := (((orbitP12Standard2BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP12Standard2BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP12GapEquiv2 :
    orbitP12OrbitGroup2 ≃* PCGroup smallGroup_32_35 :=
  (CycExt.mulEquivOfExplicitInverse orbitP12Standard2ToGenerated orbitP12Standard2FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv35

end Smallgroups.UsefulTheorems.Order32Certificate
