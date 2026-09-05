/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.RepsPart02
import Smallgroups.GAP.Polycyclic.Imported.Order32Part02
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Generated explicit alignment maps to GAP pc presentations; do not edit. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def gapExponents22 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 1, 0, 0], [1, 1, 0, 1, 0], [1, 1, 1, 1, 0], [0, 1, 1, 1, 1], [0, 1, 0, 1, 1], [0, 0, 0, 1, 0], [0, 0, 1, 1, 0], [0, 0, 0, 1, 1], [0, 0, 1, 1, 1], [1, 0, 1, 0, 1], [1, 0, 0, 0, 1], [1, 1, 0, 0, 0], [1, 1, 1, 0, 0], [1, 1, 0, 0, 1], [1, 1, 1, 0, 1], [0, 1, 1, 0, 1], [0, 1, 0, 0, 1], [0, 1, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 1, 0, 1], [1, 0, 1, 1, 1], [1, 0, 0, 1, 1], [1, 0, 1, 1, 0], [1, 0, 0, 1, 0], [1, 1, 0, 1, 1], [1, 1, 1, 1, 1], [0, 1, 1, 1, 0], [0, 1, 0, 1, 0], [1, 0, 1, 0, 0], [1, 0, 0, 0, 0]]
def generatedToGap22 (x : generatedGroup22) :
    PCGroup smallGroup_32_22 :=
  evalVec (gapExponents22 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_22.layers)

def generatedRelation22FromIndex (i : Fin 32) : generatedGroup22 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation22Map0 : pcTower [] →* generatedGroup22 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation22Map5 : pcTower [sg32_22_L5] →* generatedGroup22 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_22_L5 [])
    generatedRelation22Map0 (generatedRelation22FromIndex 20)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation22Map4 : pcTower [sg32_22_L4, sg32_22_L5] →* generatedGroup22 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_22_L4 [sg32_22_L5])
    generatedRelation22Map5 (generatedRelation22FromIndex 6)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation22Map3 : pcTower [sg32_22_L3, sg32_22_L4, sg32_22_L5] →* generatedGroup22 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_22_L3 [sg32_22_L4, sg32_22_L5])
    generatedRelation22Map4 (generatedRelation22FromIndex 1)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation22Map2 : pcTower [sg32_22_L2, sg32_22_L3, sg32_22_L4, sg32_22_L5] →* generatedGroup22 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_22_L2 [sg32_22_L3, sg32_22_L4, sg32_22_L5])
    generatedRelation22Map3 (generatedRelation22FromIndex 19)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks the outer generator power and conjugation relations.
def generatedRelation22ToSource : PCGroup smallGroup_32_22 →* generatedGroup22 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_22_L1 [sg32_22_L2, sg32_22_L3, sg32_22_L4, sg32_22_L5])
    generatedRelation22Map2 (generatedRelation22FromIndex 31) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv22 :
    generatedGroup22 ≃* PCGroup smallGroup_32_22 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation22ToSource generatedToGap22
    (by decide +kernel) (by rw [card_smallGroup_32_22, card_generatedGroup22])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
