/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent12Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart23
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 12, orbit 4, alignment to GAP id 23. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP12OrbitGroup4 := CocycleGroup
  (orbitP12SelectedCocycle 4) (orbitP12SelectedCocycle_consistent 4)
def orbitP12Standard4ForwardIndex : Fin 32 → Fin 32 := ![0, 20, 23, 25, 15, 13, 9, 7, 6, 8, 4, 28, 10, 30, 11, 31, 26, 2, 27, 3, 21, 1, 19, 17, 16, 18, 22, 24, 14, 12, 29, 5]
def orbitP12Standard4BackwardIndex : Fin 32 → Fin 32 := ![0, 21, 17, 19, 10, 31, 8, 7, 9, 6, 12, 14, 29, 5, 28, 4, 24, 23, 25, 22, 1, 20, 26, 2, 27, 3, 16, 18, 11, 30, 13, 15]

def orbitP12Standard4ToGenerated (x : orbitP12OrbitGroup4) : generatedGroup23 where
  fst := (((orbitP12Standard4ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP12Standard4ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP12Standard4FromGenerated (x : generatedGroup23) : orbitP12OrbitGroup4 where
  fst := (((orbitP12Standard4BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP12Standard4BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP12GapEquiv4 :
    orbitP12OrbitGroup4 ≃* PCGroup smallGroup_32_23 :=
  (CycExt.mulEquivOfExplicitInverse orbitP12Standard4ToGenerated orbitP12Standard4FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv23

end Smallgroups.UsefulTheorems.Order32Certificate
