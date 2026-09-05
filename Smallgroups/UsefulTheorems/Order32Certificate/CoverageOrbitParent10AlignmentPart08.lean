/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart36
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 10, orbit 7, alignment to GAP id 36. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP10OrbitGroup7 := CocycleGroup
  (orbitP10SelectedCocycle 7) (orbitP10SelectedCocycle_consistent 7)
def orbitP10Standard7ForwardIndex : Fin 32 → Fin 32 := ![0, 8, 2, 14, 1, 9, 16, 28, 6, 20, 15, 3, 22, 30, 26, 12, 17, 29, 21, 7, 4, 18, 23, 31, 13, 27, 10, 24, 19, 5, 25, 11]
def orbitP10Standard7BackwardIndex : Fin 32 → Fin 32 := ![0, 4, 2, 11, 20, 29, 8, 19, 1, 5, 26, 31, 15, 24, 3, 10, 6, 16, 21, 28, 9, 18, 12, 22, 27, 30, 14, 25, 7, 17, 13, 23]

def orbitP10Standard7ToGenerated (x : orbitP10OrbitGroup7) : generatedGroup36 where
  fst := (((orbitP10Standard7ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP10Standard7ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP10Standard7FromGenerated (x : generatedGroup36) : orbitP10OrbitGroup7 where
  fst := (((orbitP10Standard7BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP10Standard7BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP10GapEquiv7 :
    orbitP10OrbitGroup7 ≃* PCGroup smallGroup_32_36 :=
  (CycExt.mulEquivOfExplicitInverse orbitP10Standard7ToGenerated orbitP10Standard7FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv36

end Smallgroups.UsefulTheorems.Order32Certificate
