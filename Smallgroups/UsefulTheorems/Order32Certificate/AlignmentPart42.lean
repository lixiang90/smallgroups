/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.RepsPart04
import Smallgroups.GAP.Polycyclic.Imported.Order32Part03
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Generated explicit alignment maps to GAP pc presentations; do not edit. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def gapExponents42 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [0, 1, 0, 1, 0], [0, 1, 0, 1, 1], [1, 0, 1, 1, 1], [1, 0, 1, 1, 0], [0, 0, 1, 1, 1], [0, 0, 1, 1, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 1], [1, 1, 1, 1, 0], [1, 1, 1, 1, 1], [0, 1, 1, 0, 1], [0, 1, 1, 0, 0], [0, 1, 0, 0, 1], [0, 1, 0, 0, 0], [1, 0, 0, 0, 0], [1, 0, 0, 0, 1], [1, 0, 1, 0, 0], [1, 0, 1, 0, 1], [0, 0, 1, 0, 1], [0, 0, 1, 0, 0], [1, 1, 0, 0, 1], [1, 1, 0, 0, 0], [1, 1, 1, 0, 0], [1, 1, 1, 0, 1], [0, 1, 1, 1, 1], [0, 1, 1, 1, 0], [1, 0, 0, 1, 1], [1, 0, 0, 1, 0], [1, 1, 0, 1, 1], [1, 1, 0, 1, 0]]
def generatedToGap42 (x : generatedGroup42) :
    PCGroup smallGroup_32_42 :=
  evalVec (gapExponents42 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_42.layers)

-- The per-layer relation certificates require a larger kernel-reduction budget.
set_option maxHeartbeats 8000000

def generatedRelation42FromIndex (i : Fin 32) : generatedGroup42 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation42Map0 : pcTower [] →* generatedGroup42 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

def generatedRelation42Map5 : pcTower [sg32_42_L5] →* generatedGroup42 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_42_L5 [])
    generatedRelation42Map0 (generatedRelation42FromIndex 1)
    (by decide +kernel)

def generatedRelation42Map4 : pcTower [sg32_42_L4, sg32_42_L5] →* generatedGroup42 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_42_L4 [sg32_42_L5])
    generatedRelation42Map5 (generatedRelation42FromIndex 8)
    (by decide +kernel)

def generatedRelation42Map3 : pcTower [sg32_42_L3, sg32_42_L4, sg32_42_L5] →* generatedGroup42 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_42_L3 [sg32_42_L4, sg32_42_L5])
    generatedRelation42Map4 (generatedRelation42FromIndex 21)
    (by decide +kernel)

def generatedRelation42Map2 : pcTower [sg32_42_L2, sg32_42_L3, sg32_42_L4, sg32_42_L5] →* generatedGroup42 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_42_L2 [sg32_42_L3, sg32_42_L4, sg32_42_L5])
    generatedRelation42Map3 (generatedRelation42FromIndex 15)
    (by decide +kernel)

def generatedRelation42ToSource : PCGroup smallGroup_32_42 →* generatedGroup42 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_42_L1 [sg32_42_L2, sg32_42_L3, sg32_42_L4, sg32_42_L5])
    generatedRelation42Map2 (generatedRelation42FromIndex 16) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv42 :
    generatedGroup42 ≃* PCGroup smallGroup_32_42 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation42ToSource generatedToGap42
    (by decide +kernel) (by rw [card_smallGroup_32_42, card_generatedGroup42])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
