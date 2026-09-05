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

def gapExponents15 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 1, 1, 0], [1, 1, 1, 1, 1], [0, 1, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 1, 0], [0, 0, 0, 1, 1], [1, 0, 0, 1, 0], [1, 0, 0, 1, 1], [1, 1, 0, 1, 1], [1, 1, 0, 1, 0], [1, 1, 1, 0, 0], [1, 1, 1, 0, 1], [0, 1, 1, 0, 0], [0, 1, 1, 0, 1], [0, 1, 0, 1, 0], [0, 1, 0, 1, 1], [0, 0, 1, 1, 1], [0, 0, 1, 1, 0], [1, 0, 1, 1, 1], [1, 0, 1, 1, 0], [1, 0, 0, 0, 0], [1, 0, 0, 0, 1], [1, 1, 0, 0, 1], [1, 1, 0, 0, 0], [0, 1, 1, 1, 0], [0, 1, 1, 1, 1], [1, 0, 1, 0, 0], [1, 0, 1, 0, 1]]
def generatedToGap15 (x : generatedGroup15) :
    PCGroup smallGroup_32_15 :=
  evalVec (gapExponents15 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_15.layers)

def generatedRelation15FromIndex (i : Fin 32) : generatedGroup15 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation15Map0 : pcTower [] →* generatedGroup15 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation15Map5 : pcTower [sg32_15_L5] →* generatedGroup15 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_15_L5 [])
    generatedRelation15Map0 (generatedRelation15FromIndex 1)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation15Map4 : pcTower [sg32_15_L4, sg32_15_L5] →* generatedGroup15 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_15_L4 [sg32_15_L5])
    generatedRelation15Map5 (generatedRelation15FromIndex 8)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation15Map3 : pcTower [sg32_15_L3, sg32_15_L4, sg32_15_L5] →* generatedGroup15 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_15_L3 [sg32_15_L4, sg32_15_L5])
    generatedRelation15Map4 (generatedRelation15FromIndex 6)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation15Map2 : pcTower [sg32_15_L2, sg32_15_L3, sg32_15_L4, sg32_15_L5] →* generatedGroup15 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_15_L2 [sg32_15_L3, sg32_15_L4, sg32_15_L5])
    generatedRelation15Map3 (generatedRelation15FromIndex 4)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks the outer generator power and conjugation relations.
def generatedRelation15ToSource : PCGroup smallGroup_32_15 →* generatedGroup15 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_15_L1 [sg32_15_L2, sg32_15_L3, sg32_15_L4, sg32_15_L5])
    generatedRelation15Map2 (generatedRelation15FromIndex 24) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv15 :
    generatedGroup15 ≃* PCGroup smallGroup_32_15 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation15ToSource generatedToGap15
    (by decide +kernel) (by rw [card_smallGroup_32_15, card_generatedGroup15])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
