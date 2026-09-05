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

def gapExponents17 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [1, 0, 1, 1, 0], [1, 0, 1, 1, 1], [0, 1, 0, 0, 1], [0, 1, 0, 0, 0], [0, 0, 1, 1, 1], [0, 0, 1, 1, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 1], [1, 1, 1, 1, 0], [1, 1, 1, 1, 1], [1, 0, 0, 1, 1], [1, 0, 0, 1, 0], [1, 0, 1, 0, 0], [1, 0, 1, 0, 1], [0, 1, 1, 1, 0], [0, 1, 1, 1, 1], [0, 1, 0, 1, 1], [0, 1, 0, 1, 0], [0, 0, 1, 0, 1], [0, 0, 1, 0, 0], [1, 1, 0, 1, 0], [1, 1, 0, 1, 1], [1, 1, 1, 0, 1], [1, 1, 1, 0, 0], [1, 0, 0, 0, 1], [1, 0, 0, 0, 0], [0, 1, 1, 0, 0], [0, 1, 1, 0, 1], [1, 1, 0, 0, 0], [1, 1, 0, 0, 1]]
def generatedToGap17 (x : generatedGroup17) :
    PCGroup smallGroup_32_17 :=
  evalVec (gapExponents17 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_17.layers)

-- The per-layer relation certificates require a larger kernel-reduction budget.
set_option maxHeartbeats 8000000

def generatedRelation17FromIndex (i : Fin 32) : generatedGroup17 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation17Map0 : pcTower [] →* generatedGroup17 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

def generatedRelation17Map5 : pcTower [sg32_17_L5] →* generatedGroup17 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_17_L5 [])
    generatedRelation17Map0 (generatedRelation17FromIndex 1)
    (by decide +kernel)

def generatedRelation17Map4 : pcTower [sg32_17_L4, sg32_17_L5] →* generatedGroup17 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_17_L4 [sg32_17_L5])
    generatedRelation17Map5 (generatedRelation17FromIndex 8)
    (by decide +kernel)

def generatedRelation17Map3 : pcTower [sg32_17_L3, sg32_17_L4, sg32_17_L5] →* generatedGroup17 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_17_L3 [sg32_17_L4, sg32_17_L5])
    generatedRelation17Map4 (generatedRelation17FromIndex 21)
    (by decide +kernel)

def generatedRelation17Map2 : pcTower [sg32_17_L2, sg32_17_L3, sg32_17_L4, sg32_17_L5] →* generatedGroup17 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_17_L2 [sg32_17_L3, sg32_17_L4, sg32_17_L5])
    generatedRelation17Map3 (generatedRelation17FromIndex 5)
    (by decide +kernel)

def generatedRelation17ToSource : PCGroup smallGroup_32_17 →* generatedGroup17 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_17_L1 [sg32_17_L2, sg32_17_L3, sg32_17_L4, sg32_17_L5])
    generatedRelation17Map2 (generatedRelation17FromIndex 27) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv17 :
    generatedGroup17 ≃* PCGroup smallGroup_32_17 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation17ToSource generatedToGap17
    (by decide +kernel) (by rw [card_smallGroup_32_17, card_generatedGroup17])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
