/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart21
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 10, orbit 1, alignment to GAP id 21. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP10OrbitGroup1 := CocycleGroup
  (orbitP10SelectedCocycle 1) (orbitP10SelectedCocycle_consistent 1)
def orbitP10Standard1ForwardIndex : Fin 32 → Fin 32 := ![0, 8, 2, 14, 4, 18, 5, 19, 6, 20, 10, 24, 11, 25, 12, 26, 1, 9, 16, 28, 17, 29, 3, 15, 22, 30, 23, 31, 7, 21, 13, 27]
def orbitP10Standard1BackwardIndex : Fin 32 → Fin 32 := ![0, 16, 2, 22, 4, 6, 8, 28, 1, 17, 10, 12, 14, 30, 3, 23, 18, 20, 5, 7, 9, 29, 24, 26, 11, 13, 15, 31, 19, 21, 25, 27]

def orbitP10Standard1ToGenerated (x : orbitP10OrbitGroup1) : generatedGroup21 where
  fst := (((orbitP10Standard1ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP10Standard1ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP10Standard1FromGenerated (x : generatedGroup21) : orbitP10OrbitGroup1 where
  fst := (((orbitP10Standard1BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP10Standard1BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP10GapEquiv1 :
    orbitP10OrbitGroup1 ≃* PCGroup smallGroup_32_21 :=
  (CycExt.mulEquivOfExplicitInverse orbitP10Standard1ToGenerated orbitP10Standard1FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv21

end Smallgroups.UsefulTheorems.Order32Certificate
