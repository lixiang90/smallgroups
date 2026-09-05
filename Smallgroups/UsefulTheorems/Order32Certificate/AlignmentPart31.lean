/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.RepsPart03
import Smallgroups.GAP.Polycyclic.Imported.Order32Part02
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Generated explicit alignment maps to GAP pc presentations; do not edit. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def gapExponents31 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 1, 1], [1, 0, 1, 1, 1], [1, 0, 1, 0, 0], [1, 0, 0, 0, 1], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [0, 1, 1, 1, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 1, 1], [1, 1, 0, 1, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0], [1, 0, 1, 0, 1], [1, 1, 1, 0, 1], [1, 1, 1, 1, 0], [1, 0, 0, 0, 0], [1, 0, 0, 1, 1], [0, 1, 1, 0, 1], [0, 1, 1, 1, 0], [0, 1, 0, 0, 1], [0, 1, 0, 1, 0], [0, 0, 1, 0, 1], [0, 0, 1, 1, 0], [1, 1, 0, 1, 1], [1, 1, 0, 0, 0], [1, 1, 1, 0, 0], [1, 1, 1, 1, 1], [0, 1, 0, 0, 0], [0, 1, 0, 1, 1]]
def generatedToGap31 (x : generatedGroup31) :
    PCGroup smallGroup_32_31 :=
  evalVec (gapExponents31 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_31.layers)

def generatedRelation31FromIndex (i : Fin 32) : generatedGroup31 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation31Map0 : pcTower [] →* generatedGroup31 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation31Map5 : pcTower [sg32_31_L5] →* generatedGroup31 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_31_L5 [])
    generatedRelation31Map0 (generatedRelation31FromIndex 8)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation31Map4 : pcTower [sg32_31_L4, sg32_31_L5] →* generatedGroup31 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_31_L4 [sg32_31_L5])
    generatedRelation31Map5 (generatedRelation31FromIndex 9)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation31Map3 : pcTower [sg32_31_L3, sg32_31_L4, sg32_31_L5] →* generatedGroup31 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_31_L3 [sg32_31_L4, sg32_31_L5])
    generatedRelation31Map4 (generatedRelation31FromIndex 10)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation31Map2 : pcTower [sg32_31_L2, sg32_31_L3, sg32_31_L4, sg32_31_L5] →* generatedGroup31 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_31_L2 [sg32_31_L3, sg32_31_L4, sg32_31_L5])
    generatedRelation31Map3 (generatedRelation31FromIndex 30)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks the outer generator power and conjugation relations.
def generatedRelation31ToSource : PCGroup smallGroup_32_31 →* generatedGroup31 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_31_L1 [sg32_31_L2, sg32_31_L3, sg32_31_L4, sg32_31_L5])
    generatedRelation31Map2 (generatedRelation31FromIndex 18) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv31 :
    generatedGroup31 ≃* PCGroup smallGroup_32_31 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation31ToSource generatedToGap31
    (by decide +kernel) (by rw [card_smallGroup_32_31, card_generatedGroup31])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
