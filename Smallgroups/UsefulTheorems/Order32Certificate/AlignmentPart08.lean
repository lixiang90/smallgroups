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

def gapExponents8 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [1, 0, 1, 0, 0], [1, 0, 1, 0, 1], [0, 1, 0, 1, 0], [0, 1, 0, 1, 1], [0, 0, 1, 0, 1], [0, 0, 1, 0, 0], [0, 0, 0, 1, 1], [0, 0, 0, 1, 0], [1, 1, 1, 1, 1], [1, 1, 1, 1, 0], [1, 0, 0, 0, 1], [1, 0, 0, 0, 0], [1, 0, 1, 1, 0], [1, 0, 1, 1, 1], [0, 1, 1, 1, 1], [0, 1, 1, 1, 0], [0, 1, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 1], [0, 0, 1, 1, 0], [1, 1, 0, 1, 1], [1, 1, 0, 1, 0], [1, 1, 1, 0, 0], [1, 1, 1, 0, 1], [1, 0, 0, 1, 1], [1, 0, 0, 1, 0], [0, 1, 1, 0, 1], [0, 1, 1, 0, 0], [1, 1, 0, 0, 0], [1, 1, 0, 0, 1]]
def generatedToGap8 (x : generatedGroup8) :
    PCGroup smallGroup_32_8 :=
  evalVec (gapExponents8 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_8.layers)

-- The per-layer relation certificates require a larger kernel-reduction budget.
set_option maxHeartbeats 8000000

def generatedRelation8FromIndex (i : Fin 32) : generatedGroup8 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation8Map0 : pcTower [] →* generatedGroup8 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

def generatedRelation8Map5 : pcTower [sg32_8_L5] →* generatedGroup8 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_8_L5 [])
    generatedRelation8Map0 (generatedRelation8FromIndex 1)
    (by decide +kernel)

def generatedRelation8Map4 : pcTower [sg32_8_L4, sg32_8_L5] →* generatedGroup8 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_8_L4 [sg32_8_L5])
    generatedRelation8Map5 (generatedRelation8FromIndex 9)
    (by decide +kernel)

def generatedRelation8Map3 : pcTower [sg32_8_L3, sg32_8_L4, sg32_8_L5] →* generatedGroup8 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_8_L3 [sg32_8_L4, sg32_8_L5])
    generatedRelation8Map4 (generatedRelation8FromIndex 7)
    (by decide +kernel)

def generatedRelation8Map2 : pcTower [sg32_8_L2, sg32_8_L3, sg32_8_L4, sg32_8_L5] →* generatedGroup8 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_8_L2 [sg32_8_L3, sg32_8_L4, sg32_8_L5])
    generatedRelation8Map3 (generatedRelation8FromIndex 18)
    (by decide +kernel)

def generatedRelation8ToSource : PCGroup smallGroup_32_8 →* generatedGroup8 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_8_L1 [sg32_8_L2, sg32_8_L3, sg32_8_L4, sg32_8_L5])
    generatedRelation8Map2 (generatedRelation8FromIndex 13) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv8 :
    generatedGroup8 ≃* PCGroup smallGroup_32_8 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation8ToSource generatedToGap8
    (by decide +kernel) (by rw [card_smallGroup_32_8, card_generatedGroup8])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
