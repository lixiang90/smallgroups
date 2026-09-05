/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.RepsPart01
import Smallgroups.GAP.Polycyclic.Imported.Order32Part01
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Generated explicit alignment maps to GAP pc presentations; do not edit. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def gapExponents5 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [1, 0, 0, 1, 1], [1, 0, 0, 1, 0], [0, 1, 1, 1, 0], [0, 1, 1, 1, 1], [0, 0, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 1, 0], [0, 0, 0, 1, 1], [1, 1, 1, 0, 1], [1, 1, 1, 0, 0], [1, 0, 1, 1, 1], [1, 0, 1, 1, 0], [1, 0, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0], [0, 1, 0, 1, 1], [0, 1, 1, 0, 0], [0, 1, 1, 0, 1], [0, 0, 1, 1, 1], [0, 0, 1, 1, 0], [1, 1, 0, 0, 0], [1, 1, 0, 0, 1], [1, 1, 1, 1, 0], [1, 1, 1, 1, 1], [1, 0, 1, 0, 0], [1, 0, 1, 0, 1], [0, 1, 0, 0, 0], [0, 1, 0, 0, 1], [1, 1, 0, 1, 1], [1, 1, 0, 1, 0]]
def generatedToGap5 (x : generatedGroup5) :
    PCGroup smallGroup_32_5 :=
  evalVec (gapExponents5 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_5.layers)

-- The per-layer relation certificates require a larger kernel-reduction budget.
set_option maxHeartbeats 8000000

def generatedRelation5FromIndex (i : Fin 32) : generatedGroup5 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation5Map0 : pcTower [] →* generatedGroup5 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

def generatedRelation5Map5 : pcTower [sg32_5_L5] →* generatedGroup5 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_5_L5 [])
    generatedRelation5Map0 (generatedRelation5FromIndex 1)
    (by decide +kernel)

def generatedRelation5Map4 : pcTower [sg32_5_L4, sg32_5_L5] →* generatedGroup5 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_5_L4 [sg32_5_L5])
    generatedRelation5Map5 (generatedRelation5FromIndex 8)
    (by decide +kernel)

def generatedRelation5Map3 : pcTower [sg32_5_L3, sg32_5_L4, sg32_5_L5] →* generatedGroup5 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_5_L3 [sg32_5_L4, sg32_5_L5])
    generatedRelation5Map4 (generatedRelation5FromIndex 6)
    (by decide +kernel)

def generatedRelation5Map2 : pcTower [sg32_5_L2, sg32_5_L3, sg32_5_L4, sg32_5_L5] →* generatedGroup5 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_5_L2 [sg32_5_L3, sg32_5_L4, sg32_5_L5])
    generatedRelation5Map3 (generatedRelation5FromIndex 28)
    (by decide +kernel)

def generatedRelation5ToSource : PCGroup smallGroup_32_5 →* generatedGroup5 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_5_L1 [sg32_5_L2, sg32_5_L3, sg32_5_L4, sg32_5_L5])
    generatedRelation5Map2 (generatedRelation5FromIndex 14) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv5 :
    generatedGroup5 ≃* PCGroup smallGroup_32_5 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation5ToSource generatedToGap5
    (by decide +kernel) (by rw [card_smallGroup_32_5, card_generatedGroup5])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
