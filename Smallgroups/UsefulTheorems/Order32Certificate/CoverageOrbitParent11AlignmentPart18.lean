/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart40
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 11, orbit 17, alignment to GAP id 40. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP11OrbitGroup17 := CocycleGroup
  (orbitP11SelectedCocycle 17) (orbitP11SelectedCocycle_consistent 17)
def orbitP11Standard17ForwardIndex : Fin 32 → Fin 32 := ![0, 8, 26, 12, 5, 19, 9, 1, 6, 20, 23, 31, 13, 27, 2, 14, 4, 18, 17, 29, 7, 21, 30, 22, 11, 25, 15, 3, 28, 16, 10, 24]
def orbitP11Standard17BackwardIndex : Fin 32 → Fin 32 := ![0, 7, 14, 27, 16, 4, 8, 20, 1, 6, 30, 24, 3, 12, 15, 26, 29, 18, 17, 5, 9, 21, 23, 10, 31, 25, 2, 13, 28, 19, 22, 11]

def orbitP11Standard17ToGenerated (x : orbitP11OrbitGroup17) : generatedGroup40 where
  fst := (((orbitP11Standard17ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP11Standard17ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP11Standard17FromGenerated (x : generatedGroup40) : orbitP11OrbitGroup17 where
  fst := (((orbitP11Standard17BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP11Standard17BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP11GapEquiv17 :
    orbitP11OrbitGroup17 ≃* PCGroup smallGroup_32_40 :=
  (CycExt.mulEquivOfExplicitInverse orbitP11Standard17ToGenerated orbitP11Standard17FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv40

end Smallgroups.UsefulTheorems.Order32Certificate
