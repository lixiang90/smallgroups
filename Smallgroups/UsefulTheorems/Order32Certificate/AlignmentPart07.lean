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

def gapExponents7 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [1, 0, 1, 0, 1], [1, 0, 1, 0, 0], [0, 1, 1, 0, 1], [0, 1, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 1, 0, 0], [0, 0, 0, 1, 1], [0, 0, 0, 1, 0], [1, 1, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 0, 0, 1], [1, 0, 0, 0, 0], [1, 0, 1, 1, 0], [1, 0, 1, 1, 1], [0, 1, 0, 0, 1], [0, 1, 0, 0, 0], [0, 1, 1, 1, 1], [0, 1, 1, 1, 0], [0, 0, 1, 1, 1], [0, 0, 1, 1, 0], [1, 1, 1, 0, 0], [1, 1, 1, 0, 1], [1, 1, 0, 1, 0], [1, 1, 0, 1, 1], [1, 0, 0, 1, 0], [1, 0, 0, 1, 1], [0, 1, 0, 1, 1], [0, 1, 0, 1, 0], [1, 1, 1, 1, 0], [1, 1, 1, 1, 1]]
def generatedToGap7 (x : generatedGroup7) :
    PCGroup smallGroup_32_7 :=
  evalVec (gapExponents7 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_7.layers)

def generatedRelation7FromIndex (i : Fin 32) : generatedGroup7 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation7Map0 : pcTower [] →* generatedGroup7 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation7Map5 : pcTower [sg32_7_L5] →* generatedGroup7 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_7_L5 [])
    generatedRelation7Map0 (generatedRelation7FromIndex 1)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation7Map4 : pcTower [sg32_7_L4, sg32_7_L5] →* generatedGroup7 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_7_L4 [sg32_7_L5])
    generatedRelation7Map5 (generatedRelation7FromIndex 9)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation7Map3 : pcTower [sg32_7_L3, sg32_7_L4, sg32_7_L5] →* generatedGroup7 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_7_L3 [sg32_7_L4, sg32_7_L5])
    generatedRelation7Map4 (generatedRelation7FromIndex 7)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation7Map2 : pcTower [sg32_7_L2, sg32_7_L3, sg32_7_L4, sg32_7_L5] →* generatedGroup7 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_7_L2 [sg32_7_L3, sg32_7_L4, sg32_7_L5])
    generatedRelation7Map3 (generatedRelation7FromIndex 17)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks the outer generator power and conjugation relations.
def generatedRelation7ToSource : PCGroup smallGroup_32_7 →* generatedGroup7 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_7_L1 [sg32_7_L2, sg32_7_L3, sg32_7_L4, sg32_7_L5])
    generatedRelation7Map2 (generatedRelation7FromIndex 13) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv7 :
    generatedGroup7 ≃* PCGroup smallGroup_32_7 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation7ToSource generatedToGap7
    (by decide +kernel) (by rw [card_smallGroup_32_7, card_generatedGroup7])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
