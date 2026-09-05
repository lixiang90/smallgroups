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

def gapExponents9 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 1, 1, 0], [1, 1, 1, 1, 1], [0, 1, 0, 0, 1], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 1, 1, 0], [0, 0, 1, 1, 1], [1, 0, 1, 1, 0], [1, 0, 1, 1, 1], [1, 1, 0, 1, 0], [1, 1, 0, 1, 1], [1, 1, 0, 0, 0], [1, 1, 0, 0, 1], [0, 1, 1, 0, 0], [0, 1, 1, 0, 1], [0, 1, 1, 1, 0], [0, 1, 1, 1, 1], [0, 0, 0, 1, 0], [0, 0, 0, 1, 1], [1, 0, 0, 1, 1], [1, 0, 0, 1, 0], [1, 0, 0, 0, 1], [1, 0, 0, 0, 0], [1, 1, 1, 0, 0], [1, 1, 1, 0, 1], [0, 1, 0, 1, 1], [0, 1, 0, 1, 0], [1, 0, 1, 0, 0], [1, 0, 1, 0, 1]]
def generatedToGap9 (x : generatedGroup9) :
    PCGroup smallGroup_32_9 :=
  evalVec (gapExponents9 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_9.layers)

-- The per-layer relation certificates require a larger kernel-reduction budget.
set_option maxHeartbeats 8000000

def generatedRelation9FromIndex (i : Fin 32) : generatedGroup9 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation9Map0 : pcTower [] →* generatedGroup9 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

def generatedRelation9Map5 : pcTower [sg32_9_L5] →* generatedGroup9 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_9_L5 [])
    generatedRelation9Map0 (generatedRelation9FromIndex 1)
    (by decide +kernel)

def generatedRelation9Map4 : pcTower [sg32_9_L4, sg32_9_L5] →* generatedGroup9 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_9_L4 [sg32_9_L5])
    generatedRelation9Map5 (generatedRelation9FromIndex 20)
    (by decide +kernel)

def generatedRelation9Map3 : pcTower [sg32_9_L3, sg32_9_L4, sg32_9_L5] →* generatedGroup9 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_9_L3 [sg32_9_L4, sg32_9_L5])
    generatedRelation9Map4 (generatedRelation9FromIndex 6)
    (by decide +kernel)

def generatedRelation9Map2 : pcTower [sg32_9_L2, sg32_9_L3, sg32_9_L4, sg32_9_L5] →* generatedGroup9 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_9_L2 [sg32_9_L3, sg32_9_L4, sg32_9_L5])
    generatedRelation9Map3 (generatedRelation9FromIndex 5)
    (by decide +kernel)

def generatedRelation9ToSource : PCGroup smallGroup_32_9 →* generatedGroup9 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_9_L1 [sg32_9_L2, sg32_9_L3, sg32_9_L4, sg32_9_L5])
    generatedRelation9Map2 (generatedRelation9FromIndex 25) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv9 :
    generatedGroup9 ≃* PCGroup smallGroup_32_9 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation9ToSource generatedToGap9
    (by decide +kernel) (by rw [card_smallGroup_32_9, card_generatedGroup9])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
