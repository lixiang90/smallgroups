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

def gapExponents35 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 1, 0], [1, 1, 1, 0, 1], [1, 1, 1, 1, 1], [1, 1, 0, 1, 0], [1, 1, 0, 0, 0], [0, 1, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 0, 1, 1], [0, 0, 0, 0, 1], [0, 0, 1, 0, 0], [0, 0, 1, 1, 0], [1, 0, 1, 0, 1], [1, 0, 1, 1, 1], [1, 1, 1, 1, 0], [1, 1, 1, 0, 0], [1, 0, 0, 0, 0], [1, 0, 0, 1, 0], [1, 1, 0, 0, 1], [1, 1, 0, 1, 1], [0, 1, 0, 1, 1], [0, 1, 0, 0, 1], [0, 1, 1, 1, 0], [0, 1, 1, 0, 0], [0, 0, 1, 1, 1], [0, 0, 1, 0, 1], [1, 0, 1, 1, 0], [1, 0, 1, 0, 0], [1, 0, 0, 1, 1], [1, 0, 0, 0, 1], [0, 1, 1, 0, 1], [0, 1, 1, 1, 1]]
def generatedToGap35 (x : generatedGroup35) :
    PCGroup smallGroup_32_35 :=
  evalVec (gapExponents35 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_35.layers)

-- The per-layer relation certificates require a larger kernel-reduction budget.
set_option maxHeartbeats 8000000

def generatedRelation35FromIndex (i : Fin 32) : generatedGroup35 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation35Map0 : pcTower [] →* generatedGroup35 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

def generatedRelation35Map5 : pcTower [sg32_35_L5] →* generatedGroup35 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_35_L5 [])
    generatedRelation35Map0 (generatedRelation35FromIndex 9)
    (by decide +kernel)

def generatedRelation35Map4 : pcTower [sg32_35_L4, sg32_35_L5] →* generatedGroup35 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_35_L4 [sg32_35_L5])
    generatedRelation35Map5 (generatedRelation35FromIndex 1)
    (by decide +kernel)

def generatedRelation35Map3 : pcTower [sg32_35_L3, sg32_35_L4, sg32_35_L5] →* generatedGroup35 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_35_L3 [sg32_35_L4, sg32_35_L5])
    generatedRelation35Map4 (generatedRelation35FromIndex 10)
    (by decide +kernel)

def generatedRelation35Map2 : pcTower [sg32_35_L2, sg32_35_L3, sg32_35_L4, sg32_35_L5] →* generatedGroup35 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_35_L2 [sg32_35_L3, sg32_35_L4, sg32_35_L5])
    generatedRelation35Map3 (generatedRelation35FromIndex 6)
    (by decide +kernel)

def generatedRelation35ToSource : PCGroup smallGroup_32_35 →* generatedGroup35 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_35_L1 [sg32_35_L2, sg32_35_L3, sg32_35_L4, sg32_35_L5])
    generatedRelation35Map2 (generatedRelation35FromIndex 16) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv35 :
    generatedGroup35 ≃* PCGroup smallGroup_32_35 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation35ToSource generatedToGap35
    (by decide +kernel) (by rw [card_smallGroup_32_35, card_generatedGroup35])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
