/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.RepsPart03
import Smallgroups.GAP.Polycyclic.Imported.Order32Part03
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Generated explicit alignment maps to GAP pc presentations; do not edit. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def gapExponents36 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 1, 0, 0], [1, 1, 1, 1, 0], [1, 1, 0, 1, 0], [0, 1, 1, 0, 1], [0, 1, 0, 0, 1], [0, 0, 0, 1, 1], [0, 0, 1, 1, 1], [0, 0, 0, 0, 1], [0, 0, 1, 0, 1], [1, 0, 0, 1, 1], [1, 0, 1, 1, 1], [1, 1, 1, 0, 0], [1, 1, 0, 0, 0], [1, 1, 1, 1, 1], [1, 1, 0, 1, 1], [0, 1, 1, 1, 0], [0, 1, 0, 1, 0], [0, 1, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 1, 0], [1, 0, 0, 0, 1], [1, 0, 1, 0, 1], [1, 0, 0, 1, 0], [1, 0, 1, 1, 0], [1, 1, 1, 0, 1], [1, 1, 0, 0, 1], [0, 1, 1, 1, 1], [0, 1, 0, 1, 1], [1, 0, 0, 0, 0], [1, 0, 1, 0, 0]]
def generatedToGap36 (x : generatedGroup36) :
    PCGroup smallGroup_32_36 :=
  evalVec (gapExponents36 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_36.layers)

def generatedRelation36FromIndex (i : Fin 32) : generatedGroup36 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation36Map0 : pcTower [] →* generatedGroup36 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation36Map5 : pcTower [sg32_36_L5] →* generatedGroup36 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_36_L5 [])
    generatedRelation36Map0 (generatedRelation36FromIndex 8)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation36Map4 : pcTower [sg32_36_L4, sg32_36_L5] →* generatedGroup36 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_36_L4 [sg32_36_L5])
    generatedRelation36Map5 (generatedRelation36FromIndex 20)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation36Map3 : pcTower [sg32_36_L3, sg32_36_L4, sg32_36_L5] →* generatedGroup36 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_36_L3 [sg32_36_L4, sg32_36_L5])
    generatedRelation36Map4 (generatedRelation36FromIndex 1)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation36Map2 : pcTower [sg32_36_L2, sg32_36_L3, sg32_36_L4, sg32_36_L5] →* generatedGroup36 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_36_L2 [sg32_36_L3, sg32_36_L4, sg32_36_L5])
    generatedRelation36Map3 (generatedRelation36FromIndex 19)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks the outer generator power and conjugation relations.
def generatedRelation36ToSource : PCGroup smallGroup_32_36 →* generatedGroup36 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_36_L1 [sg32_36_L2, sg32_36_L3, sg32_36_L4, sg32_36_L5])
    generatedRelation36Map2 (generatedRelation36FromIndex 30) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv36 :
    generatedGroup36 ≃* PCGroup smallGroup_32_36 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation36ToSource generatedToGap36
    (by decide +kernel) (by rw [card_smallGroup_32_36, card_generatedGroup36])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
