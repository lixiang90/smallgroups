/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent12Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart29
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 12, orbit 3, alignment to GAP id 29. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP12OrbitGroup3 := CocycleGroup
  (orbitP12SelectedCocycle 3) (orbitP12SelectedCocycle_consistent 3)
def orbitP12Standard3ForwardIndex : Fin 32 → Fin 32 := ![0, 9, 14, 3, 31, 22, 4, 19, 1, 8, 17, 28, 24, 11, 15, 2, 27, 12, 30, 23, 5, 18, 7, 20, 16, 29, 25, 10, 26, 13, 6, 21]
def orbitP12Standard3BackwardIndex : Fin 32 → Fin 32 := ![0, 8, 15, 3, 6, 20, 30, 22, 9, 1, 27, 13, 17, 29, 2, 14, 24, 10, 21, 7, 23, 31, 5, 19, 12, 26, 28, 16, 11, 25, 18, 4]

def orbitP12Standard3ToGenerated (x : orbitP12OrbitGroup3) : generatedGroup29 where
  fst := (((orbitP12Standard3ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP12Standard3ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP12Standard3FromGenerated (x : generatedGroup29) : orbitP12OrbitGroup3 where
  fst := (((orbitP12Standard3BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP12Standard3BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP12GapEquiv3 :
    orbitP12OrbitGroup3 ≃* PCGroup smallGroup_32_29 :=
  (CycExt.mulEquivOfExplicitInverse orbitP12Standard3ToGenerated orbitP12Standard3FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv29

end Smallgroups.UsefulTheorems.Order32Certificate
