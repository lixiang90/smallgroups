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

def gapExponents26 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 1, 0], [1, 0, 0, 1, 0], [1, 0, 0, 0, 0], [1, 1, 1, 0, 1], [1, 1, 1, 1, 1], [0, 1, 0, 1, 0], [0, 1, 0, 0, 0], [0, 0, 0, 1, 1], [0, 0, 0, 0, 1], [0, 1, 1, 1, 0], [0, 1, 1, 0, 0], [1, 1, 0, 1, 0], [1, 1, 0, 0, 0], [1, 0, 0, 0, 1], [1, 0, 0, 1, 1], [1, 0, 1, 0, 1], [1, 0, 1, 1, 1], [1, 1, 1, 1, 0], [1, 1, 1, 0, 0], [0, 1, 0, 0, 1], [0, 1, 0, 1, 1], [0, 0, 1, 0, 0], [0, 0, 1, 1, 0], [0, 1, 1, 0, 1], [0, 1, 1, 1, 1], [1, 1, 0, 0, 1], [1, 1, 0, 1, 1], [1, 0, 1, 1, 0], [1, 0, 1, 0, 0], [0, 0, 1, 1, 1], [0, 0, 1, 0, 1]]
def generatedToGap26 (x : generatedGroup26) :
    PCGroup smallGroup_32_26 :=
  evalVec (gapExponents26 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_26.layers)

def generatedRelation26FromIndex (i : Fin 32) : generatedGroup26 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation26Map0 : pcTower [] →* generatedGroup26 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation26Map5 : pcTower [sg32_26_L5] →* generatedGroup26 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_26_L5 [])
    generatedRelation26Map0 (generatedRelation26FromIndex 9)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation26Map4 : pcTower [sg32_26_L4, sg32_26_L5] →* generatedGroup26 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_26_L4 [sg32_26_L5])
    generatedRelation26Map5 (generatedRelation26FromIndex 1)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation26Map3 : pcTower [sg32_26_L3, sg32_26_L4, sg32_26_L5] →* generatedGroup26 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_26_L3 [sg32_26_L4, sg32_26_L5])
    generatedRelation26Map4 (generatedRelation26FromIndex 22)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation26Map2 : pcTower [sg32_26_L2, sg32_26_L3, sg32_26_L4, sg32_26_L5] →* generatedGroup26 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_26_L2 [sg32_26_L3, sg32_26_L4, sg32_26_L5])
    generatedRelation26Map3 (generatedRelation26FromIndex 7)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks the outer generator power and conjugation relations.
def generatedRelation26ToSource : PCGroup smallGroup_32_26 →* generatedGroup26 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_26_L1 [sg32_26_L2, sg32_26_L3, sg32_26_L4, sg32_26_L5])
    generatedRelation26Map2 (generatedRelation26FromIndex 3) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv26 :
    generatedGroup26 ≃* PCGroup smallGroup_32_26 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation26ToSource generatedToGap26
    (by decide +kernel) (by rw [card_smallGroup_32_26, card_generatedGroup26])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
