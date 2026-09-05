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

def gapExponents43 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [0, 1, 1, 1, 0], [0, 1, 1, 1, 1], [1, 0, 1, 1, 1], [1, 0, 1, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 1, 0], [0, 0, 0, 1, 1], [1, 1, 0, 1, 1], [1, 1, 0, 1, 0], [0, 1, 0, 1, 1], [0, 1, 0, 1, 0], [0, 1, 1, 0, 1], [0, 1, 1, 0, 0], [1, 0, 0, 1, 1], [1, 0, 0, 1, 0], [1, 0, 1, 0, 0], [1, 0, 1, 0, 1], [0, 0, 1, 1, 1], [0, 0, 1, 1, 0], [1, 1, 1, 1, 1], [1, 1, 1, 1, 0], [1, 1, 0, 0, 1], [1, 1, 0, 0, 0], [0, 1, 0, 0, 0], [0, 1, 0, 0, 1], [1, 0, 0, 0, 1], [1, 0, 0, 0, 0], [1, 1, 1, 0, 0], [1, 1, 1, 0, 1]]
def generatedToGap43 (x : generatedGroup43) :
    PCGroup smallGroup_32_43 :=
  evalVec (gapExponents43 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_43.layers)

-- The per-layer relation certificates require a larger kernel-reduction budget.
set_option maxHeartbeats 8000000

def generatedRelation43FromIndex (i : Fin 32) : generatedGroup43 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation43Map0 : pcTower [] →* generatedGroup43 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

def generatedRelation43Map5 : pcTower [sg32_43_L5] →* generatedGroup43 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_43_L5 [])
    generatedRelation43Map0 (generatedRelation43FromIndex 1)
    (by decide +kernel)

def generatedRelation43Map4 : pcTower [sg32_43_L4, sg32_43_L5] →* generatedGroup43 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_43_L4 [sg32_43_L5])
    generatedRelation43Map5 (generatedRelation43FromIndex 8)
    (by decide +kernel)

def generatedRelation43Map3 : pcTower [sg32_43_L3, sg32_43_L4, sg32_43_L5] →* generatedGroup43 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_43_L3 [sg32_43_L4, sg32_43_L5])
    generatedRelation43Map4 (generatedRelation43FromIndex 6)
    (by decide +kernel)

def generatedRelation43Map2 : pcTower [sg32_43_L2, sg32_43_L3, sg32_43_L4, sg32_43_L5] →* generatedGroup43 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_43_L2 [sg32_43_L3, sg32_43_L4, sg32_43_L5])
    generatedRelation43Map3 (generatedRelation43FromIndex 26)
    (by decide +kernel)

def generatedRelation43ToSource : PCGroup smallGroup_32_43 →* generatedGroup43 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_43_L1 [sg32_43_L2, sg32_43_L3, sg32_43_L4, sg32_43_L5])
    generatedRelation43Map2 (generatedRelation43FromIndex 29) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv43 :
    generatedGroup43 ≃* PCGroup smallGroup_32_43 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation43ToSource generatedToGap43
    (by decide +kernel) (by rw [card_smallGroup_32_43, card_generatedGroup43])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
