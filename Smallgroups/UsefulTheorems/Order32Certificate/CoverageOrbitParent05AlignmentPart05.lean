/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent05Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart16
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 5, orbit 4, alignment to GAP id 16. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP5OrbitGroup4 := CocycleGroup
  (orbitP5SelectedCocycle 4) (orbitP5SelectedCocycle_consistent 4)
def orbitP5Standard4ForwardIndex : Fin 32 → Fin 32 := ![0, 8, 2, 14, 1, 9, 18, 4, 20, 6, 15, 3, 10, 24, 12, 26, 19, 5, 21, 7, 28, 16, 11, 25, 13, 27, 22, 30, 29, 17, 23, 31]
def orbitP5Standard4BackwardIndex : Fin 32 → Fin 32 := ![0, 4, 2, 11, 7, 17, 9, 19, 1, 5, 12, 22, 14, 24, 3, 10, 21, 29, 6, 16, 8, 18, 26, 30, 13, 23, 15, 25, 20, 28, 27, 31]

def orbitP5Standard4ToGenerated (x : orbitP5OrbitGroup4) : generatedGroup16 where
  fst := (((orbitP5Standard4ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP5Standard4ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP5Standard4FromGenerated (x : generatedGroup16) : orbitP5OrbitGroup4 where
  fst := (((orbitP5Standard4BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP5Standard4BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP5GapEquiv4 :
    orbitP5OrbitGroup4 ≃* PCGroup smallGroup_32_16 :=
  (CycExt.mulEquivOfExplicitInverse orbitP5Standard4ToGenerated orbitP5Standard4FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv16

end Smallgroups.UsefulTheorems.Order32Certificate
