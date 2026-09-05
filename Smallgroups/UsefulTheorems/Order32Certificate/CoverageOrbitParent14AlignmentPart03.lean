/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart46
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 14, orbit 2, alignment to GAP id 46. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP14OrbitGroup2 := CocycleGroup
  (orbitP14SelectedCocycle 2) (orbitP14SelectedCocycle_consistent 2)
def orbitP14Standard2ForwardIndex : Fin 32 → Fin 32 := ![0, 8, 1, 9, 19, 5, 13, 27, 11, 25, 18, 4, 12, 26, 10, 24, 22, 30, 2, 14, 28, 16, 23, 31, 3, 15, 29, 17, 7, 21, 6, 20]
def orbitP14Standard2BackwardIndex : Fin 32 → Fin 32 := ![0, 2, 18, 24, 11, 5, 30, 28, 1, 3, 14, 8, 12, 6, 19, 25, 21, 27, 10, 4, 31, 29, 16, 22, 15, 9, 13, 7, 20, 26, 17, 23]

def orbitP14Standard2ToGenerated (x : orbitP14OrbitGroup2) : generatedGroup46 where
  fst := (((orbitP14Standard2ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP14Standard2ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP14Standard2FromGenerated (x : generatedGroup46) : orbitP14OrbitGroup2 where
  fst := (((orbitP14Standard2BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP14Standard2BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP14GapEquiv2 :
    orbitP14OrbitGroup2 ≃* PCGroup smallGroup_32_46 :=
  (CycExt.mulEquivOfExplicitInverse orbitP14Standard2ToGenerated orbitP14Standard2FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv46

end Smallgroups.UsefulTheorems.Order32Certificate
