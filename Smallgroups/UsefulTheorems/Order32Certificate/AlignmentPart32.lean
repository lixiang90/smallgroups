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

def gapExponents32 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 1, 1], [1, 0, 1, 1, 1], [1, 0, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 1, 1, 0], [0, 1, 1, 1, 0], [0, 1, 1, 0, 1], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1], [1, 0, 0, 0, 0], [1, 0, 0, 1, 1], [1, 1, 0, 0, 0], [1, 1, 0, 1, 1], [1, 0, 1, 0, 1], [1, 0, 1, 1, 0], [0, 1, 0, 0, 1], [0, 1, 0, 1, 0], [0, 0, 1, 1, 1], [0, 0, 1, 0, 0], [0, 1, 1, 0, 0], [0, 1, 1, 1, 1], [1, 1, 1, 0, 1], [1, 1, 1, 1, 0], [1, 0, 0, 1, 0], [1, 0, 0, 0, 1], [1, 1, 0, 1, 0], [1, 1, 0, 0, 1], [0, 1, 0, 1, 1], [0, 1, 0, 0, 0], [1, 1, 1, 1, 1], [1, 1, 1, 0, 0]]
def generatedToGap32 (x : generatedGroup32) :
    PCGroup smallGroup_32_32 :=
  evalVec (gapExponents32 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_32.layers)

def generatedRelation32FromIndex (i : Fin 32) : generatedGroup32 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation32Map0 : pcTower [] →* generatedGroup32 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation32Map5 : pcTower [sg32_32_L5] →* generatedGroup32 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_32_L5 [])
    generatedRelation32Map0 (generatedRelation32FromIndex 9)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation32Map4 : pcTower [sg32_32_L4, sg32_32_L5] →* generatedGroup32 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_32_L4 [sg32_32_L5])
    generatedRelation32Map5 (generatedRelation32FromIndex 8)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation32Map3 : pcTower [sg32_32_L3, sg32_32_L4, sg32_32_L5] →* generatedGroup32 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_32_L3 [sg32_32_L4, sg32_32_L5])
    generatedRelation32Map4 (generatedRelation32FromIndex 19)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation32Map2 : pcTower [sg32_32_L2, sg32_32_L3, sg32_32_L4, sg32_32_L5] →* generatedGroup32 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_32_L2 [sg32_32_L3, sg32_32_L4, sg32_32_L5])
    generatedRelation32Map3 (generatedRelation32FromIndex 29)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks the outer generator power and conjugation relations.
def generatedRelation32ToSource : PCGroup smallGroup_32_32 →* generatedGroup32 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_32_L1 [sg32_32_L2, sg32_32_L3, sg32_32_L4, sg32_32_L5])
    generatedRelation32Map2 (generatedRelation32FromIndex 10) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv32 :
    generatedGroup32 ≃* PCGroup smallGroup_32_32 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation32ToSource generatedToGap32
    (by decide +kernel) (by rw [card_smallGroup_32_32, card_generatedGroup32])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
