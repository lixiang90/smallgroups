/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.RepsPart02
import Smallgroups.GAP.Polycyclic.Imported.Order32Part01
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Generated explicit alignment maps to GAP pc presentations; do not edit. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def gapExponents16 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 1, 0, 0, 1], [1, 0, 0, 1, 0], [1, 1, 0, 1, 1], [0, 0, 1, 0, 1], [0, 1, 1, 0, 0], [0, 0, 0, 1, 0], [0, 1, 0, 1, 1], [0, 0, 0, 0, 1], [0, 1, 0, 0, 0], [1, 0, 1, 1, 1], [1, 1, 1, 1, 0], [1, 0, 0, 0, 1], [1, 1, 0, 0, 0], [1, 0, 0, 1, 1], [1, 1, 0, 1, 0], [0, 0, 1, 1, 1], [0, 1, 1, 1, 0], [0, 0, 1, 0, 0], [0, 1, 1, 0, 1], [0, 0, 0, 1, 1], [0, 1, 0, 1, 0], [1, 0, 1, 0, 0], [1, 1, 1, 0, 1], [1, 0, 1, 1, 0], [1, 1, 1, 1, 1], [1, 0, 0, 0, 0], [1, 1, 0, 0, 1], [0, 0, 1, 1, 0], [0, 1, 1, 1, 1], [1, 0, 1, 0, 1], [1, 1, 1, 0, 0]]
def generatedToGap16 (x : generatedGroup16) :
    PCGroup smallGroup_32_16 :=
  evalVec (gapExponents16 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_16.layers)

def generatedRelation16FromIndex (i : Fin 32) : generatedGroup16 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation16Map0 : pcTower [] →* generatedGroup16 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation16Map5 : pcTower [sg32_16_L5] →* generatedGroup16 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_16_L5 [])
    generatedRelation16Map0 (generatedRelation16FromIndex 8)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation16Map4 : pcTower [sg32_16_L4, sg32_16_L5] →* generatedGroup16 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_16_L4 [sg32_16_L5])
    generatedRelation16Map5 (generatedRelation16FromIndex 6)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation16Map3 : pcTower [sg32_16_L3, sg32_16_L4, sg32_16_L5] →* generatedGroup16 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_16_L3 [sg32_16_L4, sg32_16_L5])
    generatedRelation16Map4 (generatedRelation16FromIndex 18)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation16Map2 : pcTower [sg32_16_L2, sg32_16_L3, sg32_16_L4, sg32_16_L5] →* generatedGroup16 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_16_L2 [sg32_16_L3, sg32_16_L4, sg32_16_L5])
    generatedRelation16Map3 (generatedRelation16FromIndex 9)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks the outer generator power and conjugation relations.
def generatedRelation16ToSource : PCGroup smallGroup_32_16 →* generatedGroup16 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_16_L1 [sg32_16_L2, sg32_16_L3, sg32_16_L4, sg32_16_L5])
    generatedRelation16Map2 (generatedRelation16FromIndex 26) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv16 :
    generatedGroup16 ≃* PCGroup smallGroup_32_16 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation16ToSource generatedToGap16
    (by decide +kernel) (by rw [card_smallGroup_32_16, card_generatedGroup16])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
