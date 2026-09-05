/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.RepsPart02
import Smallgroups.GAP.Polycyclic.Imported.Order32Part01
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Generated explicit alignment maps to GAP pc presentations; do not edit. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def gapExponents14 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 0, 0, 1], [1, 1, 0, 0, 0], [0, 1, 0, 0, 1], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 1, 0], [0, 0, 0, 1, 1], [1, 0, 1, 0, 0], [1, 0, 1, 0, 1], [1, 1, 1, 0, 1], [1, 1, 1, 0, 0], [1, 1, 0, 1, 1], [1, 1, 0, 1, 0], [0, 1, 1, 0, 1], [0, 1, 1, 0, 0], [0, 1, 0, 1, 1], [0, 1, 0, 1, 0], [0, 0, 1, 1, 0], [0, 0, 1, 1, 1], [1, 0, 0, 0, 0], [1, 0, 0, 0, 1], [1, 0, 1, 1, 0], [1, 0, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 0], [0, 1, 1, 1, 1], [0, 1, 1, 1, 0], [1, 0, 0, 1, 0], [1, 0, 0, 1, 1]]
def generatedToGap14 (x : generatedGroup14) :
    PCGroup smallGroup_32_14 :=
  evalVec (gapExponents14 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_14.layers)

-- The per-layer relation certificates require a larger kernel-reduction budget.
set_option maxHeartbeats 8000000

def generatedRelation14FromIndex (i : Fin 32) : generatedGroup14 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation14Map0 : pcTower [] →* generatedGroup14 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

def generatedRelation14Map5 : pcTower [sg32_14_L5] →* generatedGroup14 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_14_L5 [])
    generatedRelation14Map0 (generatedRelation14FromIndex 1)
    (by decide +kernel)

def generatedRelation14Map4 : pcTower [sg32_14_L4, sg32_14_L5] →* generatedGroup14 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_14_L4 [sg32_14_L5])
    generatedRelation14Map5 (generatedRelation14FromIndex 8)
    (by decide +kernel)

def generatedRelation14Map3 : pcTower [sg32_14_L3, sg32_14_L4, sg32_14_L5] →* generatedGroup14 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_14_L3 [sg32_14_L4, sg32_14_L5])
    generatedRelation14Map4 (generatedRelation14FromIndex 6)
    (by decide +kernel)

def generatedRelation14Map2 : pcTower [sg32_14_L2, sg32_14_L3, sg32_14_L4, sg32_14_L5] →* generatedGroup14 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_14_L2 [sg32_14_L3, sg32_14_L4, sg32_14_L5])
    generatedRelation14Map3 (generatedRelation14FromIndex 5)
    (by decide +kernel)

def generatedRelation14ToSource : PCGroup smallGroup_32_14 →* generatedGroup14 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_14_L1 [sg32_14_L2, sg32_14_L3, sg32_14_L4, sg32_14_L5])
    generatedRelation14Map2 (generatedRelation14FromIndex 22) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv14 :
    generatedGroup14 ≃* PCGroup smallGroup_32_14 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation14ToSource generatedToGap14
    (by decide +kernel) (by rw [card_smallGroup_32_14, card_generatedGroup14])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
