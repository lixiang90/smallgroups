/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent07Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart14
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 7, orbit 1, alignment to GAP id 14. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP7OrbitGroup1 := CocycleGroup
  (orbitP7SelectedCocycle 1) (orbitP7SelectedCocycle_consistent 1)
def orbitP7Standard1ForwardIndex : Fin 32 → Fin 32 := ![0, 8, 23, 31, 12, 26, 7, 21, 1, 9, 17, 29, 10, 24, 22, 30, 2, 14, 13, 27, 6, 20, 5, 19, 16, 28, 11, 25, 3, 15, 4, 18]
def orbitP7Standard1BackwardIndex : Fin 32 → Fin 32 := ![0, 8, 16, 28, 30, 22, 20, 6, 1, 9, 12, 26, 4, 18, 17, 29, 24, 10, 31, 23, 21, 7, 14, 2, 13, 27, 5, 19, 25, 11, 15, 3]

def orbitP7Standard1ToGenerated (x : orbitP7OrbitGroup1) : generatedGroup14 where
  fst := (((orbitP7Standard1ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP7Standard1ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP7Standard1FromGenerated (x : generatedGroup14) : orbitP7OrbitGroup1 where
  fst := (((orbitP7Standard1BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP7Standard1BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP7GapEquiv1 :
    orbitP7OrbitGroup1 ≃* PCGroup smallGroup_32_14 :=
  (CycExt.mulEquivOfExplicitInverse orbitP7Standard1ToGenerated orbitP7Standard1FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv14

end Smallgroups.UsefulTheorems.Order32Certificate
