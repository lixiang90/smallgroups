/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart51
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 14, orbit 0, alignment to GAP id 51. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP14OrbitGroup0 := CocycleGroup
  (orbitP14SelectedCocycle 0) (orbitP14SelectedCocycle_consistent 0)
def orbitP14Standard0ForwardIndex : Fin 32 → Fin 32 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]
def orbitP14Standard0BackwardIndex : Fin 32 → Fin 32 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]

def orbitP14Standard0ToGenerated (x : orbitP14OrbitGroup0) : generatedGroup51 where
  fst := (((orbitP14Standard0ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP14Standard0ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP14Standard0FromGenerated (x : generatedGroup51) : orbitP14OrbitGroup0 where
  fst := (((orbitP14Standard0BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP14Standard0BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP14GapEquiv0 :
    orbitP14OrbitGroup0 ≃* PCGroup smallGroup_32_51 :=
  (CycExt.mulEquivOfExplicitInverse orbitP14Standard0ToGenerated orbitP14Standard0FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv51

end Smallgroups.UsefulTheorems.Order32Certificate
