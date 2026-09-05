/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart47
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 14, orbit 3, alignment to GAP id 47. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP14OrbitGroup3 := CocycleGroup
  (orbitP14SelectedCocycle 3) (orbitP14SelectedCocycle_consistent 3)
def orbitP14Standard3ForwardIndex : Fin 32 → Fin 32 := ![0, 8, 9, 1, 12, 26, 28, 16, 22, 30, 27, 13, 17, 29, 31, 23, 24, 10, 4, 18, 14, 2, 11, 25, 19, 5, 3, 15, 20, 6, 7, 21]
def orbitP14Standard3BackwardIndex : Fin 32 → Fin 32 := ![0, 3, 21, 26, 18, 25, 29, 30, 1, 2, 17, 22, 4, 11, 20, 27, 7, 12, 19, 24, 28, 31, 8, 15, 16, 23, 5, 10, 6, 13, 9, 14]

def orbitP14Standard3ToGenerated (x : orbitP14OrbitGroup3) : generatedGroup47 where
  fst := (((orbitP14Standard3ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP14Standard3ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

def orbitP14Standard3FromGenerated (x : generatedGroup47) : orbitP14OrbitGroup3 where
  fst := (((orbitP14Standard3BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨(orbitP14Standard3BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks multiplication and both inverse tables.
noncomputable def orbitP14GapEquiv3 :
    orbitP14OrbitGroup3 ≃* PCGroup smallGroup_32_47 :=
  (CycExt.mulEquivOfExplicitInverse orbitP14Standard3ToGenerated orbitP14Standard3FromGenerated
    (by decide +kernel) (by decide +kernel)).trans
    generatedGapEquiv47

end Smallgroups.UsefulTheorems.Order32Certificate
