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

def gapExponents12 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [1, 0, 0, 0, 1], [1, 0, 0, 0, 0], [0, 1, 1, 1, 0], [0, 1, 1, 1, 1], [0, 0, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 1, 0], [0, 0, 0, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 0], [1, 0, 1, 0, 1], [1, 0, 1, 0, 0], [1, 0, 0, 1, 0], [1, 0, 0, 1, 1], [0, 1, 0, 1, 0], [0, 1, 0, 1, 1], [0, 1, 1, 0, 1], [0, 1, 1, 0, 0], [0, 0, 1, 1, 1], [0, 0, 1, 1, 0], [1, 1, 0, 1, 1], [1, 1, 0, 1, 0], [1, 1, 1, 0, 1], [1, 1, 1, 0, 0], [1, 0, 1, 1, 0], [1, 0, 1, 1, 1], [0, 1, 0, 0, 1], [0, 1, 0, 0, 0], [1, 1, 0, 0, 0], [1, 1, 0, 0, 1]]
def generatedToGap12 (x : generatedGroup12) :
    PCGroup smallGroup_32_12 :=
  evalVec (gapExponents12 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_12.layers)

def generatedRelation12FromIndex (i : Fin 32) : generatedGroup12 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation12Map0 : pcTower [] →* generatedGroup12 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation12Map5 : pcTower [sg32_12_L5] →* generatedGroup12 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_12_L5 [])
    generatedRelation12Map0 (generatedRelation12FromIndex 1)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation12Map4 : pcTower [sg32_12_L4, sg32_12_L5] →* generatedGroup12 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_12_L4 [sg32_12_L5])
    generatedRelation12Map5 (generatedRelation12FromIndex 8)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation12Map3 : pcTower [sg32_12_L3, sg32_12_L4, sg32_12_L5] →* generatedGroup12 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_12_L3 [sg32_12_L4, sg32_12_L5])
    generatedRelation12Map4 (generatedRelation12FromIndex 6)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation12Map2 : pcTower [sg32_12_L2, sg32_12_L3, sg32_12_L4, sg32_12_L5] →* generatedGroup12 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_12_L2 [sg32_12_L3, sg32_12_L4, sg32_12_L5])
    generatedRelation12Map3 (generatedRelation12FromIndex 29)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks the outer generator power and conjugation relations.
def generatedRelation12ToSource : PCGroup smallGroup_32_12 →* generatedGroup12 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_12_L1 [sg32_12_L2, sg32_12_L3, sg32_12_L4, sg32_12_L5])
    generatedRelation12Map2 (generatedRelation12FromIndex 3) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv12 :
    generatedGroup12 ≃* PCGroup smallGroup_32_12 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation12ToSource generatedToGap12
    (by decide +kernel) (by rw [card_smallGroup_32_12, card_generatedGroup12])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
