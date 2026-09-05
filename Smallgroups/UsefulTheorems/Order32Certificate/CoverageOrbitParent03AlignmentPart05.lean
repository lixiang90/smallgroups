/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent03Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart02
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 3, orbit 4, alignment to GAP id 2. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP3OrbitGroup4 := CocycleGroup
  (orbitP3SelectedCocycle 4) (orbitP3SelectedCocycle_consistent 4)
def orbitP3Standard4ForwardIndex : Fin 32 → Fin 32 := ![0, 20, 13, 15, 25, 23, 21, 1, 7, 9, 16, 18, 12, 14, 27, 3, 24, 22, 10, 30, 8, 6, 19, 17, 4, 28, 26, 2, 11, 31, 29, 5]
def orbitP3Standard4BackwardIndex : Fin 32 → Fin 32 := ![0, 7, 27, 15, 24, 31, 21, 8, 20, 9, 18, 28, 12, 2, 13, 3, 10, 23, 11, 22, 1, 6, 17, 5, 16, 4, 26, 14, 25, 30, 19, 29]

def orbitP3Standard4ToGenerated (x : orbitP3OrbitGroup4) : generatedGroup2 where
  fst := (((orbitP3Standard4ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP3Standard4ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP3Standard4FromGenerated (x : generatedGroup2) : orbitP3OrbitGroup4 where
  fst := (((orbitP3Standard4BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP3Standard4BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP3GapEquiv4 :
    orbitP3OrbitGroup4 ≃* PCGroup smallGroup_32_2 :=
  (CycExt.mulEquivOfExplicitInverse orbitP3Standard4ToGenerated orbitP3Standard4FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv2

end Smallgroups.UsefulTheorems.Order32Certificate
