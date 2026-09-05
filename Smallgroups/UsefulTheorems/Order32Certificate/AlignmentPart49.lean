/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.RepsPart04
import Smallgroups.GAP.Polycyclic.Imported.Order32Part04
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Generated explicit alignment maps to GAP pc presentations; do not edit. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def gapExponents49 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 1, 0, 1], [1, 1, 1, 0, 0], [1, 0, 0, 0, 1], [1, 0, 0, 0, 0], [1, 1, 0, 0, 0], [1, 1, 0, 0, 1], [0, 1, 1, 1, 0], [0, 1, 1, 1, 1], [0, 1, 1, 0, 1], [0, 1, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 1, 0, 0], [1, 0, 0, 1, 0], [1, 0, 0, 1, 1], [0, 1, 0, 0, 1], [0, 1, 0, 0, 0], [1, 1, 1, 1, 0], [1, 1, 1, 1, 1], [1, 0, 1, 1, 0], [1, 0, 1, 1, 1], [1, 0, 1, 0, 1], [1, 0, 1, 0, 0], [0, 0, 0, 1, 1], [0, 0, 0, 1, 0], [0, 1, 0, 1, 0], [0, 1, 0, 1, 1], [0, 0, 1, 1, 0], [0, 0, 1, 1, 1], [1, 1, 0, 1, 1], [1, 1, 0, 1, 0]]
def generatedToGap49 (x : generatedGroup49) :
    PCGroup smallGroup_32_49 :=
  evalVec (gapExponents49 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_49.layers)

-- The per-layer relation certificates require a larger kernel-reduction budget.
set_option maxHeartbeats 8000000

def generatedRelation49FromIndex (i : Fin 32) : generatedGroup49 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation49Map0 : pcTower [] →* generatedGroup49 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

def generatedRelation49Map5 : pcTower [sg32_49_L5] →* generatedGroup49 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_49_L5 [])
    generatedRelation49Map0 (generatedRelation49FromIndex 1)
    (by decide +kernel)

def generatedRelation49Map4 : pcTower [sg32_49_L4, sg32_49_L5] →* generatedGroup49 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_49_L4 [sg32_49_L5])
    generatedRelation49Map5 (generatedRelation49FromIndex 25)
    (by decide +kernel)

def generatedRelation49Map3 : pcTower [sg32_49_L3, sg32_49_L4, sg32_49_L5] →* generatedGroup49 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_49_L3 [sg32_49_L4, sg32_49_L5])
    generatedRelation49Map4 (generatedRelation49FromIndex 13)
    (by decide +kernel)

def generatedRelation49Map2 : pcTower [sg32_49_L2, sg32_49_L3, sg32_49_L4, sg32_49_L5] →* generatedGroup49 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_49_L2 [sg32_49_L3, sg32_49_L4, sg32_49_L5])
    generatedRelation49Map3 (generatedRelation49FromIndex 17)
    (by decide +kernel)

def generatedRelation49ToSource : PCGroup smallGroup_32_49 →* generatedGroup49 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_49_L1 [sg32_49_L2, sg32_49_L3, sg32_49_L4, sg32_49_L5])
    generatedRelation49Map2 (generatedRelation49FromIndex 5) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv49 :
    generatedGroup49 ≃* PCGroup smallGroup_32_49 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation49ToSource generatedToGap49
    (by decide +kernel) (by rw [card_smallGroup_32_49, card_generatedGroup49])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
