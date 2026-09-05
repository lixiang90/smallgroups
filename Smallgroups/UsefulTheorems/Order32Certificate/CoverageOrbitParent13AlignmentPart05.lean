/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart31
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 13, orbit 4, alignment to GAP id 31. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP13OrbitGroup4 := CocycleGroup
  (orbitP13SelectedCocycle 4) (orbitP13SelectedCocycle_consistent 4)
def orbitP13Standard4ForwardIndex : Fin 32 → Fin 32 := ![0, 8, 29, 17, 23, 31, 11, 25, 1, 9, 3, 15, 12, 26, 28, 16, 6, 20, 22, 30, 10, 24, 18, 4, 2, 14, 13, 27, 7, 21, 19, 5]
def orbitP13Standard4BackwardIndex : Fin 32 → Fin 32 := ![0, 8, 24, 10, 23, 31, 16, 28, 1, 9, 20, 6, 12, 26, 25, 11, 15, 3, 22, 30, 17, 29, 18, 4, 21, 7, 13, 27, 14, 2, 19, 5]

def orbitP13Standard4ToGenerated (x : orbitP13OrbitGroup4) : generatedGroup31 where
  fst := (((orbitP13Standard4ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP13Standard4ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP13Standard4FromGenerated (x : generatedGroup31) : orbitP13OrbitGroup4 where
  fst := (((orbitP13Standard4BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP13Standard4BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP13GapEquiv4 :
    orbitP13OrbitGroup4 ≃* PCGroup smallGroup_32_31 :=
  (CycExt.mulEquivOfExplicitInverse orbitP13Standard4ToGenerated orbitP13Standard4FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv31

end Smallgroups.UsefulTheorems.Order32Certificate
