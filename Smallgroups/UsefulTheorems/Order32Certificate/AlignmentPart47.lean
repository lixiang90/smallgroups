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

def gapExponents47 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 1, 1, 0], [0, 1, 1, 0, 1], [0, 1, 0, 1, 1], [1, 1, 1, 1, 1], [1, 1, 0, 0, 1], [0, 0, 0, 1, 1], [0, 0, 1, 0, 1], [0, 0, 0, 0, 1], [0, 0, 1, 1, 1], [1, 0, 0, 1, 0], [1, 0, 1, 0, 0], [0, 1, 1, 1, 0], [0, 1, 0, 0, 0], [0, 1, 1, 0, 0], [0, 1, 0, 1, 0], [1, 1, 1, 0, 0], [1, 1, 0, 1, 0], [1, 1, 1, 1, 0], [1, 1, 0, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [1, 0, 0, 0, 1], [1, 0, 1, 1, 1], [1, 0, 0, 1, 1], [1, 0, 1, 0, 1], [0, 1, 1, 1, 1], [0, 1, 0, 0, 1], [1, 1, 1, 0, 1], [1, 1, 0, 1, 1], [1, 0, 0, 0, 0], [1, 0, 1, 1, 0]]
def generatedToGap47 (x : generatedGroup47) :
    PCGroup smallGroup_32_47 :=
  evalVec (gapExponents47 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_47.layers)

-- The per-layer relation certificates require a larger kernel-reduction budget.
set_option maxHeartbeats 8000000

def generatedRelation47FromIndex (i : Fin 32) : generatedGroup47 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation47Map0 : pcTower [] →* generatedGroup47 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

def generatedRelation47Map5 : pcTower [sg32_47_L5] →* generatedGroup47 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_47_L5 [])
    generatedRelation47Map0 (generatedRelation47FromIndex 8)
    (by decide +kernel)

def generatedRelation47Map4 : pcTower [sg32_47_L4, sg32_47_L5] →* generatedGroup47 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_47_L4 [sg32_47_L5])
    generatedRelation47Map5 (generatedRelation47FromIndex 20)
    (by decide +kernel)

def generatedRelation47Map3 : pcTower [sg32_47_L3, sg32_47_L4, sg32_47_L5] →* generatedGroup47 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_47_L3 [sg32_47_L4, sg32_47_L5])
    generatedRelation47Map4 (generatedRelation47FromIndex 21)
    (by decide +kernel)

def generatedRelation47Map2 : pcTower [sg32_47_L2, sg32_47_L3, sg32_47_L4, sg32_47_L5] →* generatedGroup47 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_47_L2 [sg32_47_L3, sg32_47_L4, sg32_47_L5])
    generatedRelation47Map3 (generatedRelation47FromIndex 13)
    (by decide +kernel)

def generatedRelation47ToSource : PCGroup smallGroup_32_47 →* generatedGroup47 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_47_L1 [sg32_47_L2, sg32_47_L3, sg32_47_L4, sg32_47_L5])
    generatedRelation47Map2 (generatedRelation47FromIndex 30) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv47 :
    generatedGroup47 ≃* PCGroup smallGroup_32_47 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation47ToSource generatedToGap47
    (by decide +kernel) (by rw [card_smallGroup_32_47, card_generatedGroup47])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
