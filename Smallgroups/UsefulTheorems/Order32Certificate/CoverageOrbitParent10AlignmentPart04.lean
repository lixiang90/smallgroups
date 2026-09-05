/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart23
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 10, orbit 3, alignment to GAP id 23. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP10OrbitGroup3 := CocycleGroup
  (orbitP10SelectedCocycle 3) (orbitP10SelectedCocycle_consistent 3)
def orbitP10Standard3ForwardIndex : Fin 32 → Fin 32 := ![0, 6, 26, 14, 17, 5, 18, 28, 8, 20, 25, 31, 22, 10, 12, 2, 21, 9, 29, 19, 4, 16, 3, 13, 11, 23, 30, 24, 7, 1, 15, 27]
def orbitP10Standard3BackwardIndex : Fin 32 → Fin 32 := ![0, 29, 15, 22, 20, 5, 1, 28, 8, 17, 13, 24, 14, 23, 3, 30, 21, 4, 6, 19, 9, 16, 12, 25, 27, 10, 2, 31, 7, 18, 26, 11]

def orbitP10Standard3ToGenerated (x : orbitP10OrbitGroup3) : generatedGroup23 where
  fst := (((orbitP10Standard3ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP10Standard3ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP10Standard3FromGenerated (x : generatedGroup23) : orbitP10OrbitGroup3 where
  fst := (((orbitP10Standard3BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP10Standard3BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP10GapEquiv3 :
    orbitP10OrbitGroup3 ≃* PCGroup smallGroup_32_23 :=
  (CycExt.mulEquivOfExplicitInverse orbitP10Standard3ToGenerated orbitP10Standard3FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv23

end Smallgroups.UsefulTheorems.Order32Certificate
