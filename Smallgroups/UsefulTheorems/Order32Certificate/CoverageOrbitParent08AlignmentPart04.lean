/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent08Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart10
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 8, orbit 3, alignment to GAP id 10. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP8OrbitGroup3 := CocycleGroup
  (orbitP8SelectedCocycle 3) (orbitP8SelectedCocycle_consistent 3)
def orbitP8Standard3ForwardIndex : Fin 32 → Fin 32 := ![0, 20, 28, 4, 31, 11, 9, 7, 1, 21, 15, 13, 17, 19, 29, 5, 22, 24, 30, 10, 8, 6, 3, 27, 14, 12, 16, 18, 23, 25, 2, 26]
def orbitP8Standard3BackwardIndex : Fin 32 → Fin 32 := ![0, 8, 30, 22, 3, 15, 21, 7, 20, 6, 19, 5, 25, 11, 24, 10, 26, 12, 27, 13, 1, 9, 16, 28, 17, 29, 31, 23, 2, 14, 18, 4]

def orbitP8Standard3ToGenerated (x : orbitP8OrbitGroup3) : generatedGroup10 where
  fst := (((orbitP8Standard3ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP8Standard3ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP8Standard3FromGenerated (x : generatedGroup10) : orbitP8OrbitGroup3 where
  fst := (((orbitP8Standard3BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP8Standard3BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP8GapEquiv3 :
    orbitP8OrbitGroup3 ≃* PCGroup smallGroup_32_10 :=
  (CycExt.mulEquivOfExplicitInverse orbitP8Standard3ToGenerated orbitP8Standard3FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv10

end Smallgroups.UsefulTheorems.Order32Certificate
