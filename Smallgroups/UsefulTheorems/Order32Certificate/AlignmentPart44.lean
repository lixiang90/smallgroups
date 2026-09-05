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

def gapExponents44 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [1, 0, 1, 1, 0], [1, 0, 1, 1, 1], [0, 1, 1, 0, 1], [0, 1, 1, 0, 0], [0, 0, 1, 1, 0], [0, 0, 1, 1, 1], [0, 0, 0, 1, 0], [0, 0, 0, 1, 1], [1, 1, 0, 1, 1], [1, 1, 0, 1, 0], [1, 0, 0, 0, 1], [1, 0, 0, 0, 0], [1, 0, 1, 0, 1], [1, 0, 1, 0, 0], [0, 1, 0, 1, 1], [0, 1, 0, 1, 0], [0, 1, 1, 1, 1], [0, 1, 1, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 1], [1, 1, 1, 0, 1], [1, 1, 1, 0, 0], [1, 1, 0, 0, 1], [1, 1, 0, 0, 0], [1, 0, 0, 1, 1], [1, 0, 0, 1, 0], [0, 1, 0, 0, 1], [0, 1, 0, 0, 0], [1, 1, 1, 1, 1], [1, 1, 1, 1, 0]]
def generatedToGap44 (x : generatedGroup44) :
    PCGroup smallGroup_32_44 :=
  evalVec (gapExponents44 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_44.layers)

-- The per-layer relation certificates require a larger kernel-reduction budget.
set_option maxHeartbeats 8000000

def generatedRelation44FromIndex (i : Fin 32) : generatedGroup44 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation44Map0 : pcTower [] →* generatedGroup44 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

def generatedRelation44Map5 : pcTower [sg32_44_L5] →* generatedGroup44 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_44_L5 [])
    generatedRelation44Map0 (generatedRelation44FromIndex 1)
    (by decide +kernel)

def generatedRelation44Map4 : pcTower [sg32_44_L4, sg32_44_L5] →* generatedGroup44 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_44_L4 [sg32_44_L5])
    generatedRelation44Map5 (generatedRelation44FromIndex 8)
    (by decide +kernel)

def generatedRelation44Map3 : pcTower [sg32_44_L3, sg32_44_L4, sg32_44_L5] →* generatedGroup44 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_44_L3 [sg32_44_L4, sg32_44_L5])
    generatedRelation44Map4 (generatedRelation44FromIndex 20)
    (by decide +kernel)

def generatedRelation44Map2 : pcTower [sg32_44_L2, sg32_44_L3, sg32_44_L4, sg32_44_L5] →* generatedGroup44 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_44_L2 [sg32_44_L3, sg32_44_L4, sg32_44_L5])
    generatedRelation44Map3 (generatedRelation44FromIndex 29)
    (by decide +kernel)

def generatedRelation44ToSource : PCGroup smallGroup_32_44 →* generatedGroup44 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_44_L1 [sg32_44_L2, sg32_44_L3, sg32_44_L4, sg32_44_L5])
    generatedRelation44Map2 (generatedRelation44FromIndex 13) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv44 :
    generatedGroup44 ≃* PCGroup smallGroup_32_44 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation44ToSource generatedToGap44
    (by decide +kernel) (by rw [card_smallGroup_32_44, card_generatedGroup44])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
