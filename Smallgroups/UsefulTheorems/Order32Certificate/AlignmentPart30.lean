/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.RepsPart03
import Smallgroups.GAP.Polycyclic.Imported.Order32Part02
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Generated explicit alignment maps to GAP pc presentations; do not edit. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def gapExponents30 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 1, 0], [1, 1, 0, 0, 0], [1, 1, 0, 1, 0], [0, 1, 1, 0, 1], [0, 1, 1, 1, 1], [0, 1, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 1], [1, 0, 1, 0, 1], [1, 0, 1, 1, 1], [1, 0, 0, 1, 0], [1, 0, 0, 0, 0], [1, 1, 0, 0, 1], [1, 1, 0, 1, 1], [0, 0, 1, 1, 1], [0, 0, 1, 0, 1], [0, 1, 1, 0, 0], [0, 1, 1, 1, 0], [0, 1, 0, 0, 1], [0, 1, 0, 1, 1], [1, 1, 1, 0, 1], [1, 1, 1, 1, 1], [1, 0, 1, 0, 0], [1, 0, 1, 1, 0], [1, 0, 0, 1, 1], [1, 0, 0, 0, 1], [0, 0, 1, 1, 0], [0, 0, 1, 0, 0], [1, 1, 1, 0, 0], [1, 1, 1, 1, 0]]
def generatedToGap30 (x : generatedGroup30) :
    PCGroup smallGroup_32_30 :=
  evalVec (gapExponents30 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_30.layers)

-- The per-layer relation certificates require a larger kernel-reduction budget.
set_option maxHeartbeats 8000000

def generatedRelation30FromIndex (i : Fin 32) : generatedGroup30 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation30Map0 : pcTower [] →* generatedGroup30 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

def generatedRelation30Map5 : pcTower [sg32_30_L5] →* generatedGroup30 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_30_L5 [])
    generatedRelation30Map0 (generatedRelation30FromIndex 8)
    (by decide +kernel)

def generatedRelation30Map4 : pcTower [sg32_30_L4, sg32_30_L5] →* generatedGroup30 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_30_L4 [sg32_30_L5])
    generatedRelation30Map5 (generatedRelation30FromIndex 1)
    (by decide +kernel)

def generatedRelation30Map3 : pcTower [sg32_30_L3, sg32_30_L4, sg32_30_L5] →* generatedGroup30 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_30_L3 [sg32_30_L4, sg32_30_L5])
    generatedRelation30Map4 (generatedRelation30FromIndex 29)
    (by decide +kernel)

def generatedRelation30Map2 : pcTower [sg32_30_L2, sg32_30_L3, sg32_30_L4, sg32_30_L5] →* generatedGroup30 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_30_L2 [sg32_30_L3, sg32_30_L4, sg32_30_L5])
    generatedRelation30Map3 (generatedRelation30FromIndex 6)
    (by decide +kernel)

def generatedRelation30ToSource : PCGroup smallGroup_32_30 →* generatedGroup30 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_30_L1 [sg32_30_L2, sg32_30_L3, sg32_30_L4, sg32_30_L5])
    generatedRelation30Map2 (generatedRelation30FromIndex 13) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv30 :
    generatedGroup30 ≃* PCGroup smallGroup_32_30 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation30ToSource generatedToGap30
    (by decide +kernel) (by rw [card_smallGroup_32_30, card_generatedGroup30])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
