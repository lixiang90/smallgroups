/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart37
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 10, orbit 9, alignment to GAP id 37. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP10OrbitGroup9 := CocycleGroup
  (orbitP10SelectedCocycle 9) (orbitP10SelectedCocycle_consistent 9)
def orbitP10Standard9ForwardIndex : Fin 32 → Fin 32 := ![0, 8, 25, 11, 28, 16, 19, 5, 20, 6, 27, 13, 2, 14, 31, 23, 21, 7, 4, 18, 29, 17, 22, 30, 3, 15, 12, 26, 9, 1, 10, 24]
def orbitP10Standard9BackwardIndex : Fin 32 → Fin 32 := ![0, 29, 12, 24, 18, 7, 9, 17, 1, 28, 30, 3, 26, 11, 13, 25, 5, 21, 19, 6, 8, 16, 22, 15, 31, 2, 27, 10, 4, 20, 23, 14]

def orbitP10Standard9ToGenerated (x : orbitP10OrbitGroup9) : generatedGroup37 where
  fst := (((orbitP10Standard9ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP10Standard9ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP10Standard9FromGenerated (x : generatedGroup37) : orbitP10OrbitGroup9 where
  fst := (((orbitP10Standard9BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP10Standard9BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP10GapEquiv9 :
    orbitP10OrbitGroup9 ≃* PCGroup smallGroup_32_37 :=
  (CycExt.mulEquivOfExplicitInverse orbitP10Standard9ToGenerated orbitP10Standard9FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv37

end Smallgroups.UsefulTheorems.Order32Certificate
