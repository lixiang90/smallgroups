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

def gapExponents2 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 1, 0], [0, 1, 1, 1, 0], [1, 0, 1, 0, 0], [1, 0, 0, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [0, 0, 1, 1, 0], [1, 1, 1, 1, 0], [1, 1, 0, 1, 0], [0, 1, 0, 1, 1], [0, 1, 1, 1, 1], [0, 1, 1, 0, 0], [0, 1, 0, 0, 0], [1, 0, 1, 0, 1], [1, 0, 0, 0, 1], [1, 0, 0, 1, 0], [1, 0, 1, 1, 0], [0, 0, 1, 1, 1], [0, 0, 0, 1, 1], [1, 1, 0, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 0, 0], [1, 1, 0, 0, 0], [0, 1, 1, 0, 1], [0, 1, 0, 0, 1], [1, 0, 0, 1, 1], [1, 0, 1, 1, 1], [1, 1, 0, 0, 1], [1, 1, 1, 0, 1]]
def generatedToGap2 (x : generatedGroup2) :
    PCGroup smallGroup_32_2 :=
  evalVec (gapExponents2 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_2.layers)

-- The per-layer relation certificates require a larger kernel-reduction budget.
set_option maxHeartbeats 8000000

def generatedRelation2FromIndex (i : Fin 32) : generatedGroup2 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation2Map0 : pcTower [] →* generatedGroup2 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

def generatedRelation2Map5 : pcTower [sg32_2_L5] →* generatedGroup2 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_2_L5 [])
    generatedRelation2Map0 (generatedRelation2FromIndex 7)
    (by decide +kernel)

def generatedRelation2Map4 : pcTower [sg32_2_L4, sg32_2_L5] →* generatedGroup2 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_2_L4 [sg32_2_L5])
    generatedRelation2Map5 (generatedRelation2FromIndex 8)
    (by decide +kernel)

def generatedRelation2Map3 : pcTower [sg32_2_L3, sg32_2_L4, sg32_2_L5] →* generatedGroup2 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_2_L3 [sg32_2_L4, sg32_2_L5])
    generatedRelation2Map4 (generatedRelation2FromIndex 1)
    (by decide +kernel)

def generatedRelation2Map2 : pcTower [sg32_2_L2, sg32_2_L3, sg32_2_L4, sg32_2_L5] →* generatedGroup2 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_2_L2 [sg32_2_L3, sg32_2_L4, sg32_2_L5])
    generatedRelation2Map3 (generatedRelation2FromIndex 15)
    (by decide +kernel)

def generatedRelation2ToSource : PCGroup smallGroup_32_2 →* generatedGroup2 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_2_L1 [sg32_2_L2, sg32_2_L3, sg32_2_L4, sg32_2_L5])
    generatedRelation2Map2 (generatedRelation2FromIndex 5) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv2 :
    generatedGroup2 ≃* PCGroup smallGroup_32_2 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation2ToSource generatedToGap2
    (by decide +kernel) (by rw [card_smallGroup_32_2, card_generatedGroup2])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
