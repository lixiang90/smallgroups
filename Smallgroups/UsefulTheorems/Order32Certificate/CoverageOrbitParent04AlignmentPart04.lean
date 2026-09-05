/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent04Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart02
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 4, orbit 3, alignment to GAP id 2. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP4OrbitGroup3 := CocycleGroup
  (orbitP4SelectedCocycle 3) (orbitP4SelectedCocycle_consistent 3)
def orbitP4Standard3ForwardIndex : Fin 32 → Fin 32 := ![0, 21, 14, 13, 10, 31, 20, 1, 8, 7, 29, 4, 15, 12, 3, 26, 11, 30, 24, 23, 6, 9, 5, 28, 16, 19, 2, 27, 25, 22, 18, 17]
def orbitP4Standard3BackwardIndex : Fin 32 → Fin 32 := ![0, 7, 26, 14, 11, 22, 20, 9, 8, 21, 4, 16, 13, 3, 2, 12, 24, 31, 30, 25, 6, 1, 29, 19, 18, 28, 15, 27, 23, 10, 17, 5]

def orbitP4Standard3ToGenerated (x : orbitP4OrbitGroup3) : generatedGroup2 where
  fst := (((orbitP4Standard3ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP4Standard3ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP4Standard3FromGenerated (x : generatedGroup2) : orbitP4OrbitGroup3 where
  fst := (((orbitP4Standard3BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP4Standard3BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP4GapEquiv3 :
    orbitP4OrbitGroup3 ≃* PCGroup smallGroup_32_2 :=
  (CycExt.mulEquivOfExplicitInverse orbitP4Standard3ToGenerated orbitP4Standard3FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv2

end Smallgroups.UsefulTheorems.Order32Certificate
