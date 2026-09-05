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

def gapExponents25 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 1, 0], [1, 0, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 0, 0, 0], [0, 1, 0, 1, 0], [1, 1, 1, 0, 0], [1, 1, 1, 1, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 1], [1, 1, 0, 0, 0], [1, 1, 0, 1, 0], [0, 1, 1, 0, 1], [0, 1, 1, 1, 1], [1, 0, 0, 0, 1], [1, 0, 0, 1, 1], [1, 0, 1, 0, 0], [1, 0, 1, 1, 0], [0, 1, 0, 0, 1], [0, 1, 0, 1, 1], [1, 1, 1, 0, 1], [1, 1, 1, 1, 1], [0, 0, 1, 0, 1], [0, 0, 1, 1, 1], [1, 1, 0, 0, 1], [1, 1, 0, 1, 1], [0, 1, 1, 0, 0], [0, 1, 1, 1, 0], [1, 0, 1, 0, 1], [1, 0, 1, 1, 1], [0, 0, 1, 0, 0], [0, 0, 1, 1, 0]]
def generatedToGap25 (x : generatedGroup25) :
    PCGroup smallGroup_32_25 :=
  evalVec (gapExponents25 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_25.layers)

def generatedRelation25FromIndex (i : Fin 32) : generatedGroup25 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation25Map0 : pcTower [] →* generatedGroup25 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation25Map5 : pcTower [sg32_25_L5] →* generatedGroup25 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_25_L5 [])
    generatedRelation25Map0 (generatedRelation25FromIndex 8)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation25Map4 : pcTower [sg32_25_L4, sg32_25_L5] →* generatedGroup25 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_25_L4 [sg32_25_L5])
    generatedRelation25Map5 (generatedRelation25FromIndex 1)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation25Map3 : pcTower [sg32_25_L3, sg32_25_L4, sg32_25_L5] →* generatedGroup25 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_25_L3 [sg32_25_L4, sg32_25_L5])
    generatedRelation25Map4 (generatedRelation25FromIndex 30)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation25Map2 : pcTower [sg32_25_L2, sg32_25_L3, sg32_25_L4, sg32_25_L5] →* generatedGroup25 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_25_L2 [sg32_25_L3, sg32_25_L4, sg32_25_L5])
    generatedRelation25Map3 (generatedRelation25FromIndex 4)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks the outer generator power and conjugation relations.
def generatedRelation25ToSource : PCGroup smallGroup_32_25 →* generatedGroup25 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_25_L1 [sg32_25_L2, sg32_25_L3, sg32_25_L4, sg32_25_L5])
    generatedRelation25Map2 (generatedRelation25FromIndex 2) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv25 :
    generatedGroup25 ≃* PCGroup smallGroup_32_25 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation25ToSource generatedToGap25
    (by decide +kernel) (by rw [card_smallGroup_32_25, card_generatedGroup25])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
