/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart29
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 13, orbit 5, alignment to GAP id 29. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP13OrbitGroup5 := CocycleGroup
  (orbitP13SelectedCocycle 5) (orbitP13SelectedCocycle_consistent 5)
def orbitP13Standard5ForwardIndex : Fin 32 → Fin 32 := ![0, 8, 22, 30, 11, 25, 16, 28, 1, 9, 21, 7, 14, 2, 31, 23, 12, 26, 24, 10, 17, 29, 18, 4, 20, 6, 3, 15, 27, 13, 19, 5]
def orbitP13Standard5BackwardIndex : Fin 32 → Fin 32 := ![0, 8, 13, 26, 23, 31, 25, 11, 1, 9, 19, 4, 16, 29, 12, 27, 6, 20, 22, 30, 24, 10, 2, 15, 18, 5, 17, 28, 7, 21, 3, 14]

def orbitP13Standard5ToGenerated (x : orbitP13OrbitGroup5) : generatedGroup29 where
  fst := (((orbitP13Standard5ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP13Standard5ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP13Standard5FromGenerated (x : generatedGroup29) : orbitP13OrbitGroup5 where
  fst := (((orbitP13Standard5BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP13Standard5BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP13GapEquiv5 :
    orbitP13OrbitGroup5 ≃* PCGroup smallGroup_32_29 :=
  (CycExt.mulEquivOfExplicitInverse orbitP13Standard5ToGenerated orbitP13Standard5FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv29

end Smallgroups.UsefulTheorems.Order32Certificate
