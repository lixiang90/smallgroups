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

def gapExponents45 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 1, 0, 0, 0], [1, 0, 0, 0, 0], [1, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 1, 0, 0], [0, 0, 0, 1, 0], [0, 1, 0, 1, 0], [0, 0, 0, 0, 1], [0, 1, 0, 0, 1], [1, 0, 1, 0, 0], [1, 1, 1, 0, 0], [1, 0, 0, 1, 0], [1, 1, 0, 1, 0], [1, 0, 0, 0, 1], [1, 1, 0, 0, 1], [0, 0, 1, 1, 0], [0, 1, 1, 1, 0], [0, 0, 1, 0, 1], [0, 1, 1, 0, 1], [0, 0, 0, 1, 1], [0, 1, 0, 1, 1], [1, 0, 1, 1, 0], [1, 1, 1, 1, 0], [1, 0, 1, 0, 1], [1, 1, 1, 0, 1], [1, 0, 0, 1, 1], [1, 1, 0, 1, 1], [0, 0, 1, 1, 1], [0, 1, 1, 1, 1], [1, 0, 1, 1, 1], [1, 1, 1, 1, 1]]
def generatedToGap45 (x : generatedGroup45) :
    PCGroup smallGroup_32_45 :=
  evalVec (gapExponents45 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_45.layers)

def generatedRelation45FromIndex (i : Fin 32) : generatedGroup45 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation45Map0 : pcTower [] →* generatedGroup45 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation45Map5 : pcTower [sg32_45_L5] →* generatedGroup45 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_45_L5 [])
    generatedRelation45Map0 (generatedRelation45FromIndex 8)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation45Map4 : pcTower [sg32_45_L4, sg32_45_L5] →* generatedGroup45 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_45_L4 [sg32_45_L5])
    generatedRelation45Map5 (generatedRelation45FromIndex 6)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation45Map3 : pcTower [sg32_45_L3, sg32_45_L4, sg32_45_L5] →* generatedGroup45 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_45_L3 [sg32_45_L4, sg32_45_L5])
    generatedRelation45Map4 (generatedRelation45FromIndex 4)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation45Map2 : pcTower [sg32_45_L2, sg32_45_L3, sg32_45_L4, sg32_45_L5] →* generatedGroup45 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_45_L2 [sg32_45_L3, sg32_45_L4, sg32_45_L5])
    generatedRelation45Map3 (generatedRelation45FromIndex 1)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks the outer generator power and conjugation relations.
def generatedRelation45ToSource : PCGroup smallGroup_32_45 →* generatedGroup45 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_45_L1 [sg32_45_L2, sg32_45_L3, sg32_45_L4, sg32_45_L5])
    generatedRelation45Map2 (generatedRelation45FromIndex 2) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv45 :
    generatedGroup45 ≃* PCGroup smallGroup_32_45 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation45ToSource generatedToGap45
    (by decide +kernel) (by rw [card_smallGroup_32_45, card_generatedGroup45])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
