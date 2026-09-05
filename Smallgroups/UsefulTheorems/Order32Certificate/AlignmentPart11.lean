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

def gapExponents11 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [1, 0, 1, 1, 0], [1, 0, 1, 1, 1], [0, 1, 1, 1, 1], [0, 1, 1, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 1, 0], [0, 0, 0, 1, 1], [1, 1, 0, 0, 1], [1, 1, 0, 0, 0], [1, 0, 0, 1, 1], [1, 0, 0, 1, 0], [1, 0, 1, 0, 0], [1, 0, 1, 0, 1], [0, 1, 0, 1, 0], [0, 1, 0, 1, 1], [0, 1, 1, 0, 1], [0, 1, 1, 0, 0], [0, 0, 1, 1, 1], [0, 0, 1, 1, 0], [1, 1, 1, 0, 1], [1, 1, 1, 0, 0], [1, 1, 0, 1, 1], [1, 1, 0, 1, 0], [1, 0, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 0, 1], [0, 1, 0, 0, 0], [1, 1, 1, 1, 0], [1, 1, 1, 1, 1]]
def generatedToGap11 (x : generatedGroup11) :
    PCGroup smallGroup_32_11 :=
  evalVec (gapExponents11 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_11.layers)

def generatedRelation11FromIndex (i : Fin 32) : generatedGroup11 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation11Map0 : pcTower [] →* generatedGroup11 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation11Map5 : pcTower [sg32_11_L5] →* generatedGroup11 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_11_L5 [])
    generatedRelation11Map0 (generatedRelation11FromIndex 1)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation11Map4 : pcTower [sg32_11_L4, sg32_11_L5] →* generatedGroup11 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_11_L4 [sg32_11_L5])
    generatedRelation11Map5 (generatedRelation11FromIndex 8)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation11Map3 : pcTower [sg32_11_L3, sg32_11_L4, sg32_11_L5] →* generatedGroup11 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_11_L3 [sg32_11_L4, sg32_11_L5])
    generatedRelation11Map4 (generatedRelation11FromIndex 6)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation11Map2 : pcTower [sg32_11_L2, sg32_11_L3, sg32_11_L4, sg32_11_L5] →* generatedGroup11 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_11_L2 [sg32_11_L3, sg32_11_L4, sg32_11_L5])
    generatedRelation11Map3 (generatedRelation11FromIndex 29)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks the outer generator power and conjugation relations.
def generatedRelation11ToSource : PCGroup smallGroup_32_11 →* generatedGroup11 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_11_L1 [sg32_11_L2, sg32_11_L3, sg32_11_L4, sg32_11_L5])
    generatedRelation11Map2 (generatedRelation11FromIndex 26) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv11 :
    generatedGroup11 ≃* PCGroup smallGroup_32_11 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation11ToSource generatedToGap11
    (by decide +kernel) (by rw [card_smallGroup_32_11, card_generatedGroup11])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
