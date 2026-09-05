/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart22
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 11, orbit 11, alignment to GAP id 22. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP11OrbitGroup11 := CocycleGroup
  (orbitP11SelectedCocycle 11) (orbitP11SelectedCocycle_consistent 11)
def orbitP11Standard11ForwardIndex : Fin 32 → Fin 32 := ![0, 20, 23, 25, 18, 16, 9, 7, 8, 6, 3, 27, 10, 30, 31, 11, 29, 5, 4, 28, 1, 21, 14, 12, 15, 13, 24, 22, 17, 19, 2, 26]
def orbitP11Standard11BackwardIndex : Fin 32 → Fin 32 := ![0, 20, 30, 10, 18, 17, 9, 7, 8, 6, 12, 15, 23, 25, 22, 24, 5, 28, 4, 29, 1, 21, 27, 2, 26, 3, 31, 11, 19, 16, 13, 14]

def orbitP11Standard11ToGenerated (x : orbitP11OrbitGroup11) : generatedGroup22 where
  fst := (((orbitP11Standard11ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP11Standard11ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP11Standard11FromGenerated (x : generatedGroup22) : orbitP11OrbitGroup11 where
  fst := (((orbitP11Standard11BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP11Standard11BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP11GapEquiv11 :
    orbitP11OrbitGroup11 ≃* PCGroup smallGroup_32_22 :=
  (CycExt.mulEquivOfExplicitInverse orbitP11Standard11ToGenerated orbitP11Standard11FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv22

end Smallgroups.UsefulTheorems.Order32Certificate
