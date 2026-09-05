/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent06Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart05
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 6, orbit 2, alignment to GAP id 5. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP6OrbitGroup2 := CocycleGroup
  (orbitP6SelectedCocycle 2) (orbitP6SelectedCocycle_consistent 2)
def orbitP6Standard2ForwardIndex : Fin 32 → Fin 32 := ![0, 7, 15, 26, 19, 28, 20, 8, 1, 6, 11, 23, 13, 2, 14, 27, 16, 5, 18, 29, 21, 9, 30, 24, 10, 22, 12, 3, 17, 4, 31, 25]
def orbitP6Standard2BackwardIndex : Fin 32 → Fin 32 := ![0, 8, 13, 27, 29, 17, 9, 1, 7, 21, 24, 10, 26, 12, 14, 2, 16, 28, 18, 4, 6, 20, 25, 11, 23, 31, 3, 15, 5, 19, 22, 30]

def orbitP6Standard2ToGenerated (x : orbitP6OrbitGroup2) : generatedGroup5 where
  fst := (((orbitP6Standard2ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP6Standard2ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP6Standard2FromGenerated (x : generatedGroup5) : orbitP6OrbitGroup2 where
  fst := (((orbitP6Standard2BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP6Standard2BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP6GapEquiv2 :
    orbitP6OrbitGroup2 ≃* PCGroup smallGroup_32_5 :=
  (CycExt.mulEquivOfExplicitInverse orbitP6Standard2ToGenerated orbitP6Standard2FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv5

end Smallgroups.UsefulTheorems.Order32Certificate
