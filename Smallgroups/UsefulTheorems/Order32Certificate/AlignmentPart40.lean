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

def gapExponents40 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 1, 0, 1], [1, 0, 0, 0, 1], [1, 0, 1, 0, 0], [0, 1, 0, 0, 1], [0, 1, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 1, 1], [0, 0, 0, 0, 1], [0, 0, 1, 0, 0], [1, 1, 0, 0, 0], [1, 1, 1, 0, 1], [1, 0, 0, 1, 1], [1, 0, 1, 1, 0], [1, 0, 0, 0, 0], [1, 0, 1, 0, 1], [0, 1, 0, 1, 1], [0, 1, 1, 1, 0], [0, 1, 0, 0, 0], [0, 1, 1, 0, 1], [0, 0, 0, 1, 1], [0, 0, 1, 1, 0], [1, 1, 0, 1, 0], [1, 1, 1, 1, 1], [1, 1, 0, 0, 1], [1, 1, 1, 0, 0], [1, 0, 0, 1, 0], [1, 0, 1, 1, 1], [0, 1, 0, 1, 0], [0, 1, 1, 1, 1], [1, 1, 0, 1, 1], [1, 1, 1, 1, 0]]
def generatedToGap40 (x : generatedGroup40) :
    PCGroup smallGroup_32_40 :=
  evalVec (gapExponents40 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_40.layers)

-- The per-layer relation certificates require a larger kernel-reduction budget.
set_option maxHeartbeats 8000000

def generatedRelation40FromIndex (i : Fin 32) : generatedGroup40 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation40Map0 : pcTower [] →* generatedGroup40 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

def generatedRelation40Map5 : pcTower [sg32_40_L5] →* generatedGroup40 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_40_L5 [])
    generatedRelation40Map0 (generatedRelation40FromIndex 8)
    (by decide +kernel)

def generatedRelation40Map4 : pcTower [sg32_40_L4, sg32_40_L5] →* generatedGroup40 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_40_L4 [sg32_40_L5])
    generatedRelation40Map5 (generatedRelation40FromIndex 6)
    (by decide +kernel)

def generatedRelation40Map3 : pcTower [sg32_40_L3, sg32_40_L4, sg32_40_L5] →* generatedGroup40 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_40_L3 [sg32_40_L4, sg32_40_L5])
    generatedRelation40Map4 (generatedRelation40FromIndex 9)
    (by decide +kernel)

def generatedRelation40Map2 : pcTower [sg32_40_L2, sg32_40_L3, sg32_40_L4, sg32_40_L5] →* generatedGroup40 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_40_L2 [sg32_40_L3, sg32_40_L4, sg32_40_L5])
    generatedRelation40Map3 (generatedRelation40FromIndex 18)
    (by decide +kernel)

def generatedRelation40ToSource : PCGroup smallGroup_32_40 →* generatedGroup40 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_40_L1 [sg32_40_L2, sg32_40_L3, sg32_40_L4, sg32_40_L5])
    generatedRelation40Map2 (generatedRelation40FromIndex 14) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv40 :
    generatedGroup40 ≃* PCGroup smallGroup_32_40 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation40ToSource generatedToGap40
    (by decide +kernel) (by rw [card_smallGroup_32_40, card_generatedGroup40])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
