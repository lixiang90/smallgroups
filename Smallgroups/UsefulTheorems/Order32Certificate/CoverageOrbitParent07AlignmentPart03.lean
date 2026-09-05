/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent07Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart09
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 7, orbit 2, alignment to GAP id 9. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP7OrbitGroup2 := CocycleGroup
  (orbitP7SelectedCocycle 2) (orbitP7SelectedCocycle_consistent 2)
def orbitP7Standard2ForwardIndex : Fin 32 → Fin 32 := ![0, 20, 10, 30, 28, 4, 9, 7, 1, 21, 26, 2, 25, 23, 11, 31, 16, 18, 29, 5, 8, 6, 12, 14, 27, 3, 24, 22, 17, 19, 13, 15]
def orbitP7Standard2BackwardIndex : Fin 32 → Fin 32 := ![0, 8, 11, 25, 5, 19, 21, 7, 20, 6, 2, 14, 22, 30, 23, 31, 16, 28, 17, 29, 1, 9, 27, 13, 26, 12, 10, 24, 4, 18, 3, 15]

def orbitP7Standard2ToGenerated (x : orbitP7OrbitGroup2) : generatedGroup9 where
  fst := (((orbitP7Standard2ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP7Standard2ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP7Standard2FromGenerated (x : generatedGroup9) : orbitP7OrbitGroup2 where
  fst := (((orbitP7Standard2BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP7Standard2BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP7GapEquiv2 :
    orbitP7OrbitGroup2 ≃* PCGroup smallGroup_32_9 :=
  (CycExt.mulEquivOfExplicitInverse orbitP7Standard2ToGenerated orbitP7Standard2FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv9

end Smallgroups.UsefulTheorems.Order32Certificate
