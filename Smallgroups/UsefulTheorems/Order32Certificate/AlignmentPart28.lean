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

def gapExponents28 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 0, 0, 1], [1, 1, 0, 0, 0], [1, 0, 1, 0, 1], [1, 0, 1, 0, 0], [0, 0, 1, 1, 0], [0, 0, 1, 1, 1], [0, 0, 0, 1, 0], [0, 0, 0, 1, 1], [0, 1, 1, 1, 0], [0, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 0], [1, 1, 0, 1, 1], [1, 1, 0, 1, 0], [1, 0, 0, 1, 1], [1, 0, 0, 1, 0], [1, 0, 1, 1, 1], [1, 0, 1, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 1], [0, 1, 0, 0, 0], [0, 1, 0, 0, 1], [0, 1, 1, 0, 0], [0, 1, 1, 0, 1], [1, 1, 1, 0, 1], [1, 1, 1, 0, 0], [1, 0, 0, 0, 1], [1, 0, 0, 0, 0], [0, 1, 0, 1, 0], [0, 1, 0, 1, 1]]
def generatedToGap28 (x : generatedGroup28) :
    PCGroup smallGroup_32_28 :=
  evalVec (gapExponents28 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_28.layers)

-- The per-layer relation certificates require a larger kernel-reduction budget.
set_option maxHeartbeats 8000000

def generatedRelation28FromIndex (i : Fin 32) : generatedGroup28 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation28Map0 : pcTower [] →* generatedGroup28 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

def generatedRelation28Map5 : pcTower [sg32_28_L5] →* generatedGroup28 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_28_L5 [])
    generatedRelation28Map0 (generatedRelation28FromIndex 1)
    (by decide +kernel)

def generatedRelation28Map4 : pcTower [sg32_28_L4, sg32_28_L5] →* generatedGroup28 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_28_L4 [sg32_28_L5])
    generatedRelation28Map5 (generatedRelation28FromIndex 8)
    (by decide +kernel)

def generatedRelation28Map3 : pcTower [sg32_28_L3, sg32_28_L4, sg32_28_L5] →* generatedGroup28 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_28_L3 [sg32_28_L4, sg32_28_L5])
    generatedRelation28Map4 (generatedRelation28FromIndex 20)
    (by decide +kernel)

def generatedRelation28Map2 : pcTower [sg32_28_L2, sg32_28_L3, sg32_28_L4, sg32_28_L5] →* generatedGroup28 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_28_L2 [sg32_28_L3, sg32_28_L4, sg32_28_L5])
    generatedRelation28Map3 (generatedRelation28FromIndex 22)
    (by decide +kernel)

def generatedRelation28ToSource : PCGroup smallGroup_32_28 →* generatedGroup28 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_28_L1 [sg32_28_L2, sg32_28_L3, sg32_28_L4, sg32_28_L5])
    generatedRelation28Map2 (generatedRelation28FromIndex 29) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv28 :
    generatedGroup28 ≃* PCGroup smallGroup_32_28 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation28ToSource generatedToGap28
    (by decide +kernel) (by rw [card_smallGroup_32_28, card_generatedGroup28])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
