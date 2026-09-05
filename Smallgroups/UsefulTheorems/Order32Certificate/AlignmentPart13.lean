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

def gapExponents13 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 0, 1, 0], [1, 1, 0, 1, 1], [0, 1, 1, 1, 0], [0, 1, 1, 1, 1], [0, 0, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 1, 0], [0, 0, 0, 1, 1], [1, 0, 0, 0, 0], [1, 0, 0, 0, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 0], [1, 1, 0, 0, 0], [1, 1, 0, 0, 1], [0, 1, 0, 1, 0], [0, 1, 0, 1, 1], [0, 1, 1, 0, 0], [0, 1, 1, 0, 1], [0, 0, 1, 1, 0], [0, 0, 1, 1, 1], [1, 0, 1, 0, 1], [1, 0, 1, 0, 0], [1, 0, 0, 1, 0], [1, 0, 0, 1, 1], [1, 1, 1, 0, 1], [1, 1, 1, 0, 0], [0, 1, 0, 0, 0], [0, 1, 0, 0, 1], [1, 0, 1, 1, 1], [1, 0, 1, 1, 0]]
def generatedToGap13 (x : generatedGroup13) :
    PCGroup smallGroup_32_13 :=
  evalVec (gapExponents13 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_13.layers)

def generatedRelation13FromIndex (i : Fin 32) : generatedGroup13 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation13Map0 : pcTower [] →* generatedGroup13 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation13Map5 : pcTower [sg32_13_L5] →* generatedGroup13 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_13_L5 [])
    generatedRelation13Map0 (generatedRelation13FromIndex 1)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation13Map4 : pcTower [sg32_13_L4, sg32_13_L5] →* generatedGroup13 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_13_L4 [sg32_13_L5])
    generatedRelation13Map5 (generatedRelation13FromIndex 8)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation13Map3 : pcTower [sg32_13_L3, sg32_13_L4, sg32_13_L5] →* generatedGroup13 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_13_L3 [sg32_13_L4, sg32_13_L5])
    generatedRelation13Map4 (generatedRelation13FromIndex 6)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation13Map2 : pcTower [sg32_13_L2, sg32_13_L3, sg32_13_L4, sg32_13_L5] →* generatedGroup13 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_13_L2 [sg32_13_L3, sg32_13_L4, sg32_13_L5])
    generatedRelation13Map3 (generatedRelation13FromIndex 28)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks the outer generator power and conjugation relations.
def generatedRelation13ToSource : PCGroup smallGroup_32_13 →* generatedGroup13 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_13_L1 [sg32_13_L2, sg32_13_L3, sg32_13_L4, sg32_13_L5])
    generatedRelation13Map2 (generatedRelation13FromIndex 10) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv13 :
    generatedGroup13 ≃* PCGroup smallGroup_32_13 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation13ToSource generatedToGap13
    (by decide +kernel) (by rw [card_smallGroup_32_13, card_generatedGroup13])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
