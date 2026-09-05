/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart48
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 14, orbit 4, alignment to GAP id 48. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP14OrbitGroup4 := CocycleGroup
  (orbitP14SelectedCocycle 4) (orbitP14SelectedCocycle_consistent 4)
def orbitP14Standard4ForwardIndex : Fin 32 → Fin 32 := ![0, 8, 30, 22, 6, 20, 4, 18, 3, 15, 10, 24, 26, 12, 17, 29, 16, 28, 27, 13, 11, 25, 2, 14, 5, 19, 7, 21, 31, 23, 1, 9]
def orbitP14Standard4BackwardIndex : Fin 32 → Fin 32 := ![0, 30, 22, 8, 6, 24, 4, 26, 1, 31, 10, 20, 13, 19, 23, 9, 16, 14, 7, 25, 5, 27, 3, 29, 11, 21, 12, 18, 17, 15, 2, 28]

def orbitP14Standard4ToGenerated (x : orbitP14OrbitGroup4) : generatedGroup48 where
  fst := (((orbitP14Standard4ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP14Standard4ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP14Standard4FromGenerated (x : generatedGroup48) : orbitP14OrbitGroup4 where
  fst := (((orbitP14Standard4BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP14Standard4BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP14GapEquiv4 :
    orbitP14OrbitGroup4 ≃* PCGroup smallGroup_32_48 :=
  (CycExt.mulEquivOfExplicitInverse orbitP14Standard4ToGenerated orbitP14Standard4FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv48

end Smallgroups.UsefulTheorems.Order32Certificate
