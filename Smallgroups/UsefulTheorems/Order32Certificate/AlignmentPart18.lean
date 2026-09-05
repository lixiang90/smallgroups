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

def gapExponents18 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [1, 0, 1, 0, 0], [1, 0, 1, 0, 1], [0, 1, 0, 1, 1], [0, 1, 0, 1, 0], [0, 0, 1, 1, 1], [0, 0, 1, 1, 0], [0, 0, 0, 1, 1], [0, 0, 0, 1, 0], [1, 1, 1, 0, 1], [1, 1, 1, 0, 0], [1, 0, 0, 0, 1], [1, 0, 0, 0, 0], [1, 0, 1, 1, 0], [1, 0, 1, 1, 1], [0, 1, 1, 0, 1], [0, 1, 1, 0, 0], [0, 1, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 0, 1], [0, 0, 1, 0, 0], [1, 1, 0, 0, 0], [1, 1, 0, 0, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 0], [1, 0, 0, 1, 1], [1, 0, 0, 1, 0], [0, 1, 1, 1, 0], [0, 1, 1, 1, 1], [1, 1, 0, 1, 0], [1, 1, 0, 1, 1]]
def generatedToGap18 (x : generatedGroup18) :
    PCGroup smallGroup_32_18 :=
  evalVec (gapExponents18 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_18.layers)

def generatedRelation18FromIndex (i : Fin 32) : generatedGroup18 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation18Map0 : pcTower [] →* generatedGroup18 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation18Map5 : pcTower [sg32_18_L5] →* generatedGroup18 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_18_L5 [])
    generatedRelation18Map0 (generatedRelation18FromIndex 1)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation18Map4 : pcTower [sg32_18_L4, sg32_18_L5] →* generatedGroup18 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_18_L4 [sg32_18_L5])
    generatedRelation18Map5 (generatedRelation18FromIndex 9)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation18Map3 : pcTower [sg32_18_L3, sg32_18_L4, sg32_18_L5] →* generatedGroup18 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_18_L3 [sg32_18_L4, sg32_18_L5])
    generatedRelation18Map4 (generatedRelation18FromIndex 21)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation18Map2 : pcTower [sg32_18_L2, sg32_18_L3, sg32_18_L4, sg32_18_L5] →* generatedGroup18 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_18_L2 [sg32_18_L3, sg32_18_L4, sg32_18_L5])
    generatedRelation18Map3 (generatedRelation18FromIndex 18)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks the outer generator power and conjugation relations.
def generatedRelation18ToSource : PCGroup smallGroup_32_18 →* generatedGroup18 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_18_L1 [sg32_18_L2, sg32_18_L3, sg32_18_L4, sg32_18_L5])
    generatedRelation18Map2 (generatedRelation18FromIndex 13) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv18 :
    generatedGroup18 ≃* PCGroup smallGroup_32_18 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation18ToSource generatedToGap18
    (by decide +kernel) (by rw [card_smallGroup_32_18, card_generatedGroup18])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
