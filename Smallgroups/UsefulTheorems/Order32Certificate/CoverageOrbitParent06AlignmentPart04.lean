/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent06Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart12
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 6, orbit 3, alignment to GAP id 12. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP6OrbitGroup3 := CocycleGroup
  (orbitP6SelectedCocycle 3) (orbitP6SelectedCocycle_consistent 3)
def orbitP6Standard3ForwardIndex : Fin 32 → Fin 32 := ![0, 7, 25, 31, 4, 17, 8, 20, 1, 6, 15, 26, 11, 22, 24, 30, 18, 29, 5, 16, 9, 21, 3, 12, 14, 27, 10, 23, 19, 28, 2, 13]
def orbitP6Standard3BackwardIndex : Fin 32 → Fin 32 := ![0, 8, 30, 22, 4, 18, 9, 1, 6, 20, 26, 12, 23, 31, 24, 10, 19, 5, 16, 28, 7, 21, 13, 27, 14, 2, 11, 25, 29, 17, 15, 3]

def orbitP6Standard3ToGenerated (x : orbitP6OrbitGroup3) : generatedGroup12 where
  fst := (((orbitP6Standard3ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP6Standard3ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP6Standard3FromGenerated (x : generatedGroup12) : orbitP6OrbitGroup3 where
  fst := (((orbitP6Standard3BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP6Standard3BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP6GapEquiv3 :
    orbitP6OrbitGroup3 ≃* PCGroup smallGroup_32_12 :=
  (CycExt.mulEquivOfExplicitInverse orbitP6Standard3ToGenerated orbitP6Standard3FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv12

end Smallgroups.UsefulTheorems.Order32Certificate
