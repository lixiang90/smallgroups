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

def gapExponents46 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 1, 0], [0, 1, 1, 1, 0], [0, 1, 1, 0, 0], [1, 0, 0, 1, 1], [1, 0, 0, 0, 1], [0, 0, 1, 0, 0], [0, 0, 1, 1, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 1], [1, 1, 1, 0, 0], [1, 1, 1, 1, 0], [0, 1, 0, 1, 0], [0, 1, 0, 0, 0], [0, 1, 1, 1, 1], [0, 1, 1, 0, 1], [1, 0, 1, 1, 1], [1, 0, 1, 0, 1], [1, 0, 0, 1, 0], [1, 0, 0, 0, 0], [0, 0, 1, 0, 1], [0, 0, 1, 1, 1], [1, 1, 0, 0, 0], [1, 1, 0, 1, 0], [1, 1, 1, 0, 1], [1, 1, 1, 1, 1], [0, 1, 0, 1, 1], [0, 1, 0, 0, 1], [1, 0, 1, 1, 0], [1, 0, 1, 0, 0], [1, 1, 0, 0, 1], [1, 1, 0, 1, 1]]
def generatedToGap46 (x : generatedGroup46) :
    PCGroup smallGroup_32_46 :=
  evalVec (gapExponents46 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_46.layers)

def generatedRelation46FromIndex (i : Fin 32) : generatedGroup46 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation46Map0 : pcTower [] →* generatedGroup46 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation46Map5 : pcTower [sg32_46_L5] →* generatedGroup46 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_46_L5 [])
    generatedRelation46Map0 (generatedRelation46FromIndex 8)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation46Map4 : pcTower [sg32_46_L4, sg32_46_L5] →* generatedGroup46 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_46_L4 [sg32_46_L5])
    generatedRelation46Map5 (generatedRelation46FromIndex 1)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation46Map3 : pcTower [sg32_46_L3, sg32_46_L4, sg32_46_L5] →* generatedGroup46 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_46_L3 [sg32_46_L4, sg32_46_L5])
    generatedRelation46Map4 (generatedRelation46FromIndex 6)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation46Map2 : pcTower [sg32_46_L2, sg32_46_L3, sg32_46_L4, sg32_46_L5] →* generatedGroup46 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_46_L2 [sg32_46_L3, sg32_46_L4, sg32_46_L5])
    generatedRelation46Map3 (generatedRelation46FromIndex 13)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks the outer generator power and conjugation relations.
def generatedRelation46ToSource : PCGroup smallGroup_32_46 →* generatedGroup46 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_46_L1 [sg32_46_L2, sg32_46_L3, sg32_46_L4, sg32_46_L5])
    generatedRelation46Map2 (generatedRelation46FromIndex 19) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv46 :
    generatedGroup46 ≃* PCGroup smallGroup_32_46 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation46ToSource generatedToGap46
    (by decide +kernel) (by rw [card_smallGroup_32_46, card_generatedGroup46])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
