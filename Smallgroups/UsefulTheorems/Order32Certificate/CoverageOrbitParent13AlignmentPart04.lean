/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart30
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 13, orbit 3, alignment to GAP id 30. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP13OrbitGroup3 := CocycleGroup
  (orbitP13SelectedCocycle 3) (orbitP13SelectedCocycle_consistent 3)
def orbitP13Standard3ForwardIndex : Fin 32 → Fin 32 := ![0, 9, 27, 12, 24, 11, 4, 19, 1, 8, 17, 28, 30, 23, 26, 13, 15, 2, 25, 10, 5, 18, 7, 20, 16, 29, 31, 22, 14, 3, 6, 21]
def orbitP13Standard3BackwardIndex : Fin 32 → Fin 32 := ![0, 8, 17, 29, 6, 20, 30, 22, 9, 1, 19, 5, 3, 15, 28, 16, 24, 10, 21, 7, 23, 31, 27, 13, 4, 18, 14, 2, 11, 25, 12, 26]

def orbitP13Standard3ToGenerated (x : orbitP13OrbitGroup3) : generatedGroup30 where
  fst := (((orbitP13Standard3ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP13Standard3ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP13Standard3FromGenerated (x : generatedGroup30) : orbitP13OrbitGroup3 where
  fst := (((orbitP13Standard3BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP13Standard3BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP13GapEquiv3 :
    orbitP13OrbitGroup3 ≃* PCGroup smallGroup_32_30 :=
  (CycExt.mulEquivOfExplicitInverse orbitP13Standard3ToGenerated orbitP13Standard3FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv30

end Smallgroups.UsefulTheorems.Order32Certificate
