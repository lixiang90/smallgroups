/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.RepsPart03
import Smallgroups.GAP.Polycyclic.Imported.Order32Part03
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Generated explicit alignment maps to GAP pc presentations; do not edit. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def gapExponents34 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 1, 0], [1, 0, 1, 0, 0], [1, 0, 1, 1, 0], [1, 0, 0, 1, 1], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0], [0, 1, 0, 0, 0], [0, 0, 0, 1, 1], [0, 0, 0, 0, 1], [0, 0, 1, 1, 0], [0, 0, 1, 0, 0], [1, 1, 1, 1, 0], [1, 1, 1, 0, 0], [1, 0, 1, 1, 1], [1, 0, 1, 0, 1], [1, 1, 0, 1, 1], [1, 1, 0, 0, 1], [1, 0, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 0, 0, 1], [0, 1, 0, 1, 1], [0, 1, 1, 1, 0], [0, 1, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 1, 1, 1], [1, 1, 1, 0, 1], [1, 1, 1, 1, 1], [1, 1, 0, 0, 0], [1, 1, 0, 1, 0], [0, 1, 1, 0, 1], [0, 1, 1, 1, 1]]
def generatedToGap34 (x : generatedGroup34) :
    PCGroup smallGroup_32_34 :=
  evalVec (gapExponents34 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_34.layers)

-- The per-layer relation certificates require a larger kernel-reduction budget.
set_option maxHeartbeats 8000000

def generatedRelation34FromIndex (i : Fin 32) : generatedGroup34 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation34Map0 : pcTower [] →* generatedGroup34 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

def generatedRelation34Map5 : pcTower [sg32_34_L5] →* generatedGroup34 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_34_L5 [])
    generatedRelation34Map0 (generatedRelation34FromIndex 9)
    (by decide +kernel)

def generatedRelation34Map4 : pcTower [sg32_34_L4, sg32_34_L5] →* generatedGroup34 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_34_L4 [sg32_34_L5])
    generatedRelation34Map5 (generatedRelation34FromIndex 1)
    (by decide +kernel)

def generatedRelation34Map3 : pcTower [sg32_34_L3, sg32_34_L4, sg32_34_L5] →* generatedGroup34 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_34_L3 [sg32_34_L4, sg32_34_L5])
    generatedRelation34Map4 (generatedRelation34FromIndex 11)
    (by decide +kernel)

def generatedRelation34Map2 : pcTower [sg32_34_L2, sg32_34_L3, sg32_34_L4, sg32_34_L5] →* generatedGroup34 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_34_L2 [sg32_34_L3, sg32_34_L4, sg32_34_L5])
    generatedRelation34Map3 (generatedRelation34FromIndex 7)
    (by decide +kernel)

def generatedRelation34ToSource : PCGroup smallGroup_32_34 →* generatedGroup34 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_34_L1 [sg32_34_L2, sg32_34_L3, sg32_34_L4, sg32_34_L5])
    generatedRelation34Map2 (generatedRelation34FromIndex 18) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv34 :
    generatedGroup34 ≃* PCGroup smallGroup_32_34 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation34ToSource generatedToGap34
    (by decide +kernel) (by rw [card_smallGroup_32_34, card_generatedGroup34])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
