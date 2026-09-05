/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart22
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 10, orbit 4, alignment to GAP id 22. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP10OrbitGroup4 := CocycleGroup
  (orbitP10SelectedCocycle 4) (orbitP10SelectedCocycle_consistent 4)
def orbitP10Standard4ForwardIndex : Fin 32 → Fin 32 := ![0, 6, 10, 22, 28, 18, 19, 29, 20, 8, 26, 14, 15, 27, 30, 24, 7, 1, 4, 16, 17, 5, 23, 11, 2, 12, 13, 3, 9, 21, 25, 31]
def orbitP10Standard4BackwardIndex : Fin 32 → Fin 32 := ![0, 17, 24, 27, 18, 21, 1, 16, 9, 28, 2, 23, 25, 26, 11, 12, 19, 20, 5, 6, 8, 29, 3, 22, 15, 30, 10, 13, 4, 7, 14, 31]

def orbitP10Standard4ToGenerated (x : orbitP10OrbitGroup4) : generatedGroup22 where
  fst := (((orbitP10Standard4ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP10Standard4ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP10Standard4FromGenerated (x : generatedGroup22) : orbitP10OrbitGroup4 where
  fst := (((orbitP10Standard4BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP10Standard4BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP10GapEquiv4 :
    orbitP10OrbitGroup4 ≃* PCGroup smallGroup_32_22 :=
  (CycExt.mulEquivOfExplicitInverse orbitP10Standard4ToGenerated orbitP10Standard4FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv22

end Smallgroups.UsefulTheorems.Order32Certificate
