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

def gapExponents24 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 1, 0], [1, 1, 0, 0, 0], [1, 1, 0, 1, 0], [0, 1, 1, 1, 1], [0, 1, 1, 0, 1], [0, 1, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 1], [1, 0, 1, 1, 1], [1, 0, 1, 0, 1], [1, 0, 0, 1, 0], [1, 0, 0, 0, 0], [1, 1, 0, 0, 1], [1, 1, 0, 1, 1], [0, 0, 1, 0, 1], [0, 0, 1, 1, 1], [0, 1, 1, 1, 0], [0, 1, 1, 0, 0], [0, 1, 0, 0, 1], [0, 1, 0, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 0, 1], [1, 0, 1, 1, 0], [1, 0, 1, 0, 0], [1, 0, 0, 1, 1], [1, 0, 0, 0, 1], [0, 0, 1, 0, 0], [0, 0, 1, 1, 0], [1, 1, 1, 1, 0], [1, 1, 1, 0, 0]]
def generatedToGap24 (x : generatedGroup24) :
    PCGroup smallGroup_32_24 :=
  evalVec (gapExponents24 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_24.layers)

-- The per-layer relation certificates require a larger kernel-reduction budget.
set_option maxHeartbeats 8000000

def generatedRelation24FromIndex (i : Fin 32) : generatedGroup24 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation24Map0 : pcTower [] →* generatedGroup24 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

def generatedRelation24Map5 : pcTower [sg32_24_L5] →* generatedGroup24 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_24_L5 [])
    generatedRelation24Map0 (generatedRelation24FromIndex 8)
    (by decide +kernel)

def generatedRelation24Map4 : pcTower [sg32_24_L4, sg32_24_L5] →* generatedGroup24 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_24_L4 [sg32_24_L5])
    generatedRelation24Map5 (generatedRelation24FromIndex 1)
    (by decide +kernel)

def generatedRelation24Map3 : pcTower [sg32_24_L3, sg32_24_L4, sg32_24_L5] →* generatedGroup24 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_24_L3 [sg32_24_L4, sg32_24_L5])
    generatedRelation24Map4 (generatedRelation24FromIndex 28)
    (by decide +kernel)

def generatedRelation24Map2 : pcTower [sg32_24_L2, sg32_24_L3, sg32_24_L4, sg32_24_L5] →* generatedGroup24 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_24_L2 [sg32_24_L3, sg32_24_L4, sg32_24_L5])
    generatedRelation24Map3 (generatedRelation24FromIndex 6)
    (by decide +kernel)

def generatedRelation24ToSource : PCGroup smallGroup_32_24 →* generatedGroup24 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_24_L1 [sg32_24_L2, sg32_24_L3, sg32_24_L4, sg32_24_L5])
    generatedRelation24Map2 (generatedRelation24FromIndex 13) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv24 :
    generatedGroup24 ≃* PCGroup smallGroup_32_24 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation24ToSource generatedToGap24
    (by decide +kernel) (by rw [card_smallGroup_32_24, card_generatedGroup24])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
