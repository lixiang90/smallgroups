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

def gapExponents20 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [1, 0, 0, 1, 1], [1, 0, 0, 1, 0], [0, 1, 0, 1, 0], [0, 1, 0, 1, 1], [0, 0, 1, 0, 1], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 1], [1, 1, 0, 0, 1], [1, 1, 0, 0, 0], [1, 0, 1, 1, 0], [1, 0, 1, 1, 1], [1, 0, 0, 0, 1], [1, 0, 0, 0, 0], [0, 1, 1, 1, 1], [0, 1, 1, 1, 0], [0, 1, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 1], [0, 0, 1, 1, 0], [1, 1, 1, 0, 0], [1, 1, 1, 0, 1], [1, 1, 0, 1, 0], [1, 1, 0, 1, 1], [1, 0, 1, 0, 0], [1, 0, 1, 0, 1], [0, 1, 1, 0, 0], [0, 1, 1, 0, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 0]]
def generatedToGap20 (x : generatedGroup20) :
    PCGroup smallGroup_32_20 :=
  evalVec (gapExponents20 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_20.layers)

def generatedRelation20FromIndex (i : Fin 32) : generatedGroup20 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation20Map0 : pcTower [] →* generatedGroup20 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation20Map5 : pcTower [sg32_20_L5] →* generatedGroup20 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_20_L5 [])
    generatedRelation20Map0 (generatedRelation20FromIndex 1)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation20Map4 : pcTower [sg32_20_L4, sg32_20_L5] →* generatedGroup20 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_20_L4 [sg32_20_L5])
    generatedRelation20Map5 (generatedRelation20FromIndex 8)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation20Map3 : pcTower [sg32_20_L3, sg32_20_L4, sg32_20_L5] →* generatedGroup20 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_20_L3 [sg32_20_L4, sg32_20_L5])
    generatedRelation20Map4 (generatedRelation20FromIndex 7)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation20Map2 : pcTower [sg32_20_L2, sg32_20_L3, sg32_20_L4, sg32_20_L5] →* generatedGroup20 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_20_L2 [sg32_20_L3, sg32_20_L4, sg32_20_L5])
    generatedRelation20Map3 (generatedRelation20FromIndex 18)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks the outer generator power and conjugation relations.
def generatedRelation20ToSource : PCGroup smallGroup_32_20 →* generatedGroup20 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_20_L1 [sg32_20_L2, sg32_20_L3, sg32_20_L4, sg32_20_L5])
    generatedRelation20Map2 (generatedRelation20FromIndex 15) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv20 :
    generatedGroup20 ≃* PCGroup smallGroup_32_20 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation20ToSource generatedToGap20
    (by decide +kernel) (by rw [card_smallGroup_32_20, card_generatedGroup20])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
