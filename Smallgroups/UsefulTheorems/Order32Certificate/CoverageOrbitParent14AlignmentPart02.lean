/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart45
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 14, orbit 1, alignment to GAP id 45. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP14OrbitGroup1 := CocycleGroup
  (orbitP14SelectedCocycle 1) (orbitP14SelectedCocycle_consistent 1)
def orbitP14Standard1ForwardIndex : Fin 32 → Fin 32 := ![0, 8, 1, 9, 4, 18, 2, 14, 12, 26, 5, 19, 3, 15, 13, 27, 10, 24, 22, 30, 6, 20, 11, 25, 23, 31, 7, 21, 16, 28, 17, 29]
def orbitP14Standard1BackwardIndex : Fin 32 → Fin 32 := ![0, 2, 6, 12, 4, 10, 20, 26, 1, 3, 16, 22, 8, 14, 7, 13, 28, 30, 5, 11, 21, 27, 18, 24, 17, 23, 9, 15, 29, 31, 19, 25]

def orbitP14Standard1ToGenerated (x : orbitP14OrbitGroup1) : generatedGroup45 where
  fst := (((orbitP14Standard1ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP14Standard1ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP14Standard1FromGenerated (x : generatedGroup45) : orbitP14OrbitGroup1 where
  fst := (((orbitP14Standard1BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP14Standard1BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP14GapEquiv1 :
    orbitP14OrbitGroup1 ≃* PCGroup smallGroup_32_45 :=
  (CycExt.mulEquivOfExplicitInverse orbitP14Standard1ToGenerated orbitP14Standard1FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv45

end Smallgroups.UsefulTheorems.Order32Certificate
