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

def gapExponents21 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 1, 0, 0], [1, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 1, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 1, 0], [0, 0, 0, 0, 1], [0, 0, 1, 0, 1], [1, 1, 0, 0, 0], [1, 1, 1, 0, 0], [1, 0, 0, 1, 0], [1, 0, 1, 1, 0], [1, 0, 0, 0, 1], [1, 0, 1, 0, 1], [0, 1, 0, 1, 0], [0, 1, 1, 1, 0], [0, 1, 0, 0, 1], [0, 1, 1, 0, 1], [0, 0, 0, 1, 1], [0, 0, 1, 1, 1], [1, 1, 0, 1, 0], [1, 1, 1, 1, 0], [1, 1, 0, 0, 1], [1, 1, 1, 0, 1], [1, 0, 0, 1, 1], [1, 0, 1, 1, 1], [0, 1, 0, 1, 1], [0, 1, 1, 1, 1], [1, 1, 0, 1, 1], [1, 1, 1, 1, 1]]
def generatedToGap21 (x : generatedGroup21) :
    PCGroup smallGroup_32_21 :=
  evalVec (gapExponents21 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_21.layers)

-- The per-layer relation certificates require a larger kernel-reduction budget.
set_option maxHeartbeats 8000000

def generatedRelation21FromIndex (i : Fin 32) : generatedGroup21 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation21Map0 : pcTower [] →* generatedGroup21 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

def generatedRelation21Map5 : pcTower [sg32_21_L5] →* generatedGroup21 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_21_L5 [])
    generatedRelation21Map0 (generatedRelation21FromIndex 8)
    (by decide +kernel)

def generatedRelation21Map4 : pcTower [sg32_21_L4, sg32_21_L5] →* generatedGroup21 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_21_L4 [sg32_21_L5])
    generatedRelation21Map5 (generatedRelation21FromIndex 6)
    (by decide +kernel)

def generatedRelation21Map3 : pcTower [sg32_21_L3, sg32_21_L4, sg32_21_L5] →* generatedGroup21 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_21_L3 [sg32_21_L4, sg32_21_L5])
    generatedRelation21Map4 (generatedRelation21FromIndex 1)
    (by decide +kernel)

def generatedRelation21Map2 : pcTower [sg32_21_L2, sg32_21_L3, sg32_21_L4, sg32_21_L5] →* generatedGroup21 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_21_L2 [sg32_21_L3, sg32_21_L4, sg32_21_L5])
    generatedRelation21Map3 (generatedRelation21FromIndex 4)
    (by decide +kernel)

def generatedRelation21ToSource : PCGroup smallGroup_32_21 →* generatedGroup21 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_21_L1 [sg32_21_L2, sg32_21_L3, sg32_21_L4, sg32_21_L5])
    generatedRelation21Map2 (generatedRelation21FromIndex 2) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv21 :
    generatedGroup21 ≃* PCGroup smallGroup_32_21 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation21ToSource generatedToGap21
    (by decide +kernel) (by rw [card_smallGroup_32_21, card_generatedGroup21])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
