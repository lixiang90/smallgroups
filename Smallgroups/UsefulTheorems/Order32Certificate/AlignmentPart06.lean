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

def gapExponents6 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [1, 0, 1, 0, 1], [1, 0, 1, 0, 0], [0, 1, 0, 1, 0], [0, 1, 0, 1, 1], [0, 0, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 1, 0], [0, 0, 0, 1, 1], [1, 1, 1, 1, 0], [1, 1, 1, 1, 1], [1, 0, 0, 0, 0], [1, 0, 0, 0, 1], [1, 0, 1, 1, 1], [1, 0, 1, 1, 0], [0, 1, 1, 1, 1], [0, 1, 1, 1, 0], [0, 1, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [0, 0, 1, 1, 1], [1, 1, 0, 1, 0], [1, 1, 0, 1, 1], [1, 1, 1, 0, 0], [1, 1, 1, 0, 1], [1, 0, 0, 1, 0], [1, 0, 0, 1, 1], [0, 1, 1, 0, 1], [0, 1, 1, 0, 0], [1, 1, 0, 0, 0], [1, 1, 0, 0, 1]]
def generatedToGap6 (x : generatedGroup6) :
    PCGroup smallGroup_32_6 :=
  evalVec (gapExponents6 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_6.layers)

-- The per-layer relation certificates require a larger kernel-reduction budget.
set_option maxHeartbeats 8000000

def generatedRelation6FromIndex (i : Fin 32) : generatedGroup6 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation6Map0 : pcTower [] →* generatedGroup6 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

def generatedRelation6Map5 : pcTower [sg32_6_L5] →* generatedGroup6 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_6_L5 [])
    generatedRelation6Map0 (generatedRelation6FromIndex 1)
    (by decide +kernel)

def generatedRelation6Map4 : pcTower [sg32_6_L4, sg32_6_L5] →* generatedGroup6 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_6_L4 [sg32_6_L5])
    generatedRelation6Map5 (generatedRelation6FromIndex 8)
    (by decide +kernel)

def generatedRelation6Map3 : pcTower [sg32_6_L3, sg32_6_L4, sg32_6_L5] →* generatedGroup6 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_6_L3 [sg32_6_L4, sg32_6_L5])
    generatedRelation6Map4 (generatedRelation6FromIndex 6)
    (by decide +kernel)

def generatedRelation6Map2 : pcTower [sg32_6_L2, sg32_6_L3, sg32_6_L4, sg32_6_L5] →* generatedGroup6 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_6_L2 [sg32_6_L3, sg32_6_L4, sg32_6_L5])
    generatedRelation6Map3 (generatedRelation6FromIndex 18)
    (by decide +kernel)

def generatedRelation6ToSource : PCGroup smallGroup_32_6 →* generatedGroup6 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_6_L1 [sg32_6_L2, sg32_6_L3, sg32_6_L4, sg32_6_L5])
    generatedRelation6Map2 (generatedRelation6FromIndex 12) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv6 :
    generatedGroup6 ≃* PCGroup smallGroup_32_6 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation6ToSource generatedToGap6
    (by decide +kernel) (by rw [card_smallGroup_32_6, card_generatedGroup6])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
