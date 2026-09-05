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

def gapExponents1 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 0, 1, 0], [1, 1, 0, 1, 1], [0, 1, 1, 0, 0], [0, 1, 1, 0, 1], [0, 0, 1, 1, 1], [0, 0, 1, 1, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 1], [1, 0, 0, 0, 0], [1, 0, 0, 0, 1], [1, 1, 1, 0, 1], [1, 1, 1, 0, 0], [1, 1, 0, 0, 0], [1, 1, 0, 0, 1], [0, 1, 0, 0, 1], [0, 1, 0, 0, 0], [0, 1, 1, 1, 1], [0, 1, 1, 1, 0], [0, 0, 1, 0, 1], [0, 0, 1, 0, 0], [1, 0, 1, 1, 0], [1, 0, 1, 1, 1], [1, 0, 0, 1, 1], [1, 0, 0, 1, 0], [1, 1, 1, 1, 0], [1, 1, 1, 1, 1], [0, 1, 0, 1, 0], [0, 1, 0, 1, 1], [1, 0, 1, 0, 0], [1, 0, 1, 0, 1]]
def generatedToGap1 (x : generatedGroup1) :
    PCGroup smallGroup_32_1 :=
  evalVec (gapExponents1 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_1.layers)

def generatedRelation1FromIndex (i : Fin 32) : generatedGroup1 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation1Map0 : pcTower [] →* generatedGroup1 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation1Map5 : pcTower [sg32_1_L5] →* generatedGroup1 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_1_L5 [])
    generatedRelation1Map0 (generatedRelation1FromIndex 1)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation1Map4 : pcTower [sg32_1_L4, sg32_1_L5] →* generatedGroup1 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_1_L4 [sg32_1_L5])
    generatedRelation1Map5 (generatedRelation1FromIndex 8)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation1Map3 : pcTower [sg32_1_L3, sg32_1_L4, sg32_1_L5] →* generatedGroup1 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_1_L3 [sg32_1_L4, sg32_1_L5])
    generatedRelation1Map4 (generatedRelation1FromIndex 21)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation1Map2 : pcTower [sg32_1_L2, sg32_1_L3, sg32_1_L4, sg32_1_L5] →* generatedGroup1 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_1_L2 [sg32_1_L3, sg32_1_L4, sg32_1_L5])
    generatedRelation1Map3 (generatedRelation1FromIndex 17)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks the outer generator power and conjugation relations.
def generatedRelation1ToSource : PCGroup smallGroup_32_1 →* generatedGroup1 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_1_L1 [sg32_1_L2, sg32_1_L3, sg32_1_L4, sg32_1_L5])
    generatedRelation1Map2 (generatedRelation1FromIndex 10) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv1 :
    generatedGroup1 ≃* PCGroup smallGroup_32_1 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation1ToSource generatedToGap1
    (by decide +kernel) (by rw [card_smallGroup_32_1, card_generatedGroup1])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
