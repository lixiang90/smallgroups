/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent05Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart12
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 5, orbit 3, alignment to GAP id 12. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP5OrbitGroup3 := CocycleGroup
  (orbitP5SelectedCocycle 3) (orbitP5SelectedCocycle_consistent 3)
def orbitP5Standard3ForwardIndex : Fin 32 → Fin 32 := ![0, 6, 22, 10, 18, 28, 9, 20, 1, 7, 26, 14, 31, 24, 23, 11, 4, 16, 19, 29, 8, 21, 13, 3, 27, 15, 30, 25, 5, 17, 12, 2]
def orbitP5Standard3BackwardIndex : Fin 32 → Fin 32 := ![0, 8, 31, 23, 16, 28, 1, 9, 20, 6, 3, 15, 30, 22, 11, 25, 17, 29, 4, 18, 7, 21, 2, 14, 13, 27, 10, 24, 5, 19, 26, 12]

def orbitP5Standard3ToGenerated (x : orbitP5OrbitGroup3) : generatedGroup12 where
  fst := (((orbitP5Standard3ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP5Standard3ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP5Standard3FromGenerated (x : generatedGroup12) : orbitP5OrbitGroup3 where
  fst := (((orbitP5Standard3BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP5Standard3BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP5GapEquiv3 :
    orbitP5OrbitGroup3 ≃* PCGroup smallGroup_32_12 :=
  (CycExt.mulEquivOfExplicitInverse orbitP5Standard3ToGenerated orbitP5Standard3FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv12

end Smallgroups.UsefulTheorems.Order32Certificate
