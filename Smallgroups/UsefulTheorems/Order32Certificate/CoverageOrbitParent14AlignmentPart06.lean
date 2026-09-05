/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart49
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 14, orbit 5, alignment to GAP id 49. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP14OrbitGroup5 := CocycleGroup
  (orbitP14SelectedCocycle 5) (orbitP14SelectedCocycle_consistent 5)
def orbitP14Standard5ForwardIndex : Fin 32 → Fin 32 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]
def orbitP14Standard5BackwardIndex : Fin 32 → Fin 32 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]

def orbitP14Standard5ToGenerated (x : orbitP14OrbitGroup5) : generatedGroup49 where
  fst := (((orbitP14Standard5ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP14Standard5ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP14Standard5FromGenerated (x : generatedGroup49) : orbitP14OrbitGroup5 where
  fst := (((orbitP14Standard5BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP14Standard5BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP14GapEquiv5 :
    orbitP14OrbitGroup5 ≃* PCGroup smallGroup_32_49 :=
  (CycExt.mulEquivOfExplicitInverse orbitP14Standard5ToGenerated orbitP14Standard5FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv49

end Smallgroups.UsefulTheorems.Order32Certificate
