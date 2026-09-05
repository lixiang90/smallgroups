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

def gapExponents48 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 1, 1], [0, 1, 0, 1, 0], [0, 1, 0, 0, 1], [1, 0, 0, 1, 1], [1, 0, 0, 0, 0], [0, 0, 1, 0, 1], [0, 0, 1, 1, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [1, 1, 0, 0, 0], [1, 1, 0, 1, 1], [0, 1, 1, 1, 1], [0, 1, 1, 0, 0], [0, 1, 0, 1, 1], [0, 1, 0, 0, 0], [1, 0, 1, 1, 0], [1, 0, 1, 0, 1], [1, 0, 0, 1, 0], [1, 0, 0, 0, 1], [0, 0, 1, 0, 0], [0, 0, 1, 1, 1], [1, 1, 1, 0, 1], [1, 1, 1, 1, 0], [1, 1, 0, 0, 1], [1, 1, 0, 1, 0], [0, 1, 1, 1, 0], [0, 1, 1, 0, 1], [1, 0, 1, 1, 1], [1, 0, 1, 0, 0], [1, 1, 1, 0, 0], [1, 1, 1, 1, 1]]
def generatedToGap48 (x : generatedGroup48) :
    PCGroup smallGroup_32_48 :=
  evalVec (gapExponents48 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_48.layers)

def generatedRelation48FromIndex (i : Fin 32) : generatedGroup48 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation48Map0 : pcTower [] →* generatedGroup48 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation48Map5 : pcTower [sg32_48_L5] →* generatedGroup48 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_48_L5 [])
    generatedRelation48Map0 (generatedRelation48FromIndex 8)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation48Map4 : pcTower [sg32_48_L4, sg32_48_L5] →* generatedGroup48 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_48_L4 [sg32_48_L5])
    generatedRelation48Map5 (generatedRelation48FromIndex 9)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation48Map3 : pcTower [sg32_48_L3, sg32_48_L4, sg32_48_L5] →* generatedGroup48 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_48_L3 [sg32_48_L4, sg32_48_L5])
    generatedRelation48Map4 (generatedRelation48FromIndex 20)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation48Map2 : pcTower [sg32_48_L2, sg32_48_L3, sg32_48_L4, sg32_48_L5] →* generatedGroup48 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_48_L2 [sg32_48_L3, sg32_48_L4, sg32_48_L5])
    generatedRelation48Map3 (generatedRelation48FromIndex 15)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks the outer generator power and conjugation relations.
def generatedRelation48ToSource : PCGroup smallGroup_32_48 →* generatedGroup48 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_48_L1 [sg32_48_L2, sg32_48_L3, sg32_48_L4, sg32_48_L5])
    generatedRelation48Map2 (generatedRelation48FromIndex 5) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv48 :
    generatedGroup48 ≃* PCGroup smallGroup_32_48 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation48ToSource generatedToGap48
    (by decide +kernel) (by rw [card_smallGroup_32_48, card_generatedGroup48])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
