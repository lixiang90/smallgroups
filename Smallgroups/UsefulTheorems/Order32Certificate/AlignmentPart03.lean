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

def gapExponents3 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [1, 0, 1, 0, 0], [1, 0, 1, 0, 1], [1, 1, 1, 0, 0], [1, 1, 1, 0, 1], [0, 0, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 1, 1, 1], [0, 0, 1, 1, 0], [0, 1, 1, 0, 1], [0, 1, 1, 0, 0], [1, 0, 0, 0, 1], [1, 0, 0, 0, 0], [1, 0, 0, 1, 0], [1, 0, 0, 1, 1], [1, 1, 0, 0, 0], [1, 1, 0, 0, 1], [1, 1, 0, 1, 1], [1, 1, 0, 1, 0], [0, 0, 0, 1, 1], [0, 0, 0, 1, 0], [0, 1, 0, 0, 0], [0, 1, 0, 0, 1], [0, 1, 0, 1, 1], [0, 1, 0, 1, 0], [1, 0, 1, 1, 1], [1, 0, 1, 1, 0], [1, 1, 1, 1, 1], [1, 1, 1, 1, 0], [0, 1, 1, 1, 0], [0, 1, 1, 1, 1]]
def generatedToGap3 (x : generatedGroup3) :
    PCGroup smallGroup_32_3 :=
  evalVec (gapExponents3 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_3.layers)

def generatedRelation3FromIndex (i : Fin 32) : generatedGroup3 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation3Map0 : pcTower [] →* generatedGroup3 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation3Map5 : pcTower [sg32_3_L5] →* generatedGroup3 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_3_L5 [])
    generatedRelation3Map0 (generatedRelation3FromIndex 1)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation3Map4 : pcTower [sg32_3_L4, sg32_3_L5] →* generatedGroup3 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_3_L4 [sg32_3_L5])
    generatedRelation3Map5 (generatedRelation3FromIndex 21)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation3Map3 : pcTower [sg32_3_L3, sg32_3_L4, sg32_3_L5] →* generatedGroup3 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_3_L3 [sg32_3_L4, sg32_3_L5])
    generatedRelation3Map4 (generatedRelation3FromIndex 6)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation3Map2 : pcTower [sg32_3_L2, sg32_3_L3, sg32_3_L4, sg32_3_L5] →* generatedGroup3 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_3_L2 [sg32_3_L3, sg32_3_L4, sg32_3_L5])
    generatedRelation3Map3 (generatedRelation3FromIndex 22)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks the outer generator power and conjugation relations.
def generatedRelation3ToSource : PCGroup smallGroup_32_3 →* generatedGroup3 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_3_L1 [sg32_3_L2, sg32_3_L3, sg32_3_L4, sg32_3_L5])
    generatedRelation3Map2 (generatedRelation3FromIndex 13) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv3 :
    generatedGroup3 ≃* PCGroup smallGroup_32_3 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation3ToSource generatedToGap3
    (by decide +kernel) (by rw [card_smallGroup_32_3, card_generatedGroup3])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
