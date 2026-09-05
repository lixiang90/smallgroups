/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart32
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 13, orbit 9, alignment to GAP id 32. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP13OrbitGroup9 := CocycleGroup
  (orbitP13SelectedCocycle 9) (orbitP13SelectedCocycle_consistent 9)
def orbitP13Standard9ForwardIndex : Fin 32 → Fin 32 := ![0, 9, 13, 26, 15, 2, 4, 19, 8, 1, 20, 7, 23, 30, 27, 12, 25, 10, 3, 14, 18, 5, 28, 17, 6, 21, 22, 31, 11, 24, 29, 16]
def orbitP13Standard9BackwardIndex : Fin 32 → Fin 32 := ![0, 9, 5, 18, 6, 21, 24, 11, 8, 1, 17, 28, 15, 2, 19, 4, 31, 23, 20, 7, 10, 25, 26, 12, 29, 16, 3, 14, 22, 30, 13, 27]

def orbitP13Standard9ToGenerated (x : orbitP13OrbitGroup9) : generatedGroup32 where
  fst := (((orbitP13Standard9ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP13Standard9ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP13Standard9FromGenerated (x : generatedGroup32) : orbitP13OrbitGroup9 where
  fst := (((orbitP13Standard9BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP13Standard9BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP13GapEquiv9 :
    orbitP13OrbitGroup9 ≃* PCGroup smallGroup_32_32 :=
  (CycExt.mulEquivOfExplicitInverse orbitP13Standard9ToGenerated orbitP13Standard9FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv32

end Smallgroups.UsefulTheorems.Order32Certificate
