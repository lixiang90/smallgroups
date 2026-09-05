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

def gapExponents10 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 1, 0, 1], [1, 1, 1, 0, 0], [0, 1, 1, 1, 0], [0, 1, 1, 1, 1], [0, 0, 1, 0, 1], [0, 0, 1, 0, 0], [0, 0, 1, 1, 1], [0, 0, 1, 1, 0], [1, 0, 0, 1, 1], [1, 0, 0, 1, 0], [1, 1, 0, 0, 1], [1, 1, 0, 0, 0], [1, 1, 0, 1, 1], [1, 1, 0, 1, 0], [0, 1, 0, 1, 0], [0, 1, 0, 1, 1], [0, 1, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 0, 1, 0], [0, 0, 0, 1, 1], [1, 0, 1, 1, 0], [1, 0, 1, 1, 1], [1, 0, 1, 0, 0], [1, 0, 1, 0, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 0], [0, 1, 1, 0, 0], [0, 1, 1, 0, 1], [1, 0, 0, 0, 1], [1, 0, 0, 0, 0]]
def generatedToGap10 (x : generatedGroup10) :
    PCGroup smallGroup_32_10 :=
  evalVec (gapExponents10 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_10.layers)

-- The per-layer relation certificates require a larger kernel-reduction budget.
set_option maxHeartbeats 8000000

def generatedRelation10FromIndex (i : Fin 32) : generatedGroup10 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation10Map0 : pcTower [] →* generatedGroup10 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

def generatedRelation10Map5 : pcTower [sg32_10_L5] →* generatedGroup10 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_10_L5 [])
    generatedRelation10Map0 (generatedRelation10FromIndex 1)
    (by decide +kernel)

def generatedRelation10Map4 : pcTower [sg32_10_L4, sg32_10_L5] →* generatedGroup10 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_10_L4 [sg32_10_L5])
    generatedRelation10Map5 (generatedRelation10FromIndex 20)
    (by decide +kernel)

def generatedRelation10Map3 : pcTower [sg32_10_L3, sg32_10_L4, sg32_10_L5] →* generatedGroup10 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_10_L3 [sg32_10_L4, sg32_10_L5])
    generatedRelation10Map4 (generatedRelation10FromIndex 7)
    (by decide +kernel)

def generatedRelation10Map2 : pcTower [sg32_10_L2, sg32_10_L3, sg32_10_L4, sg32_10_L5] →* generatedGroup10 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_10_L2 [sg32_10_L3, sg32_10_L4, sg32_10_L5])
    generatedRelation10Map3 (generatedRelation10FromIndex 18)
    (by decide +kernel)

def generatedRelation10ToSource : PCGroup smallGroup_32_10 →* generatedGroup10 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_10_L1 [sg32_10_L2, sg32_10_L3, sg32_10_L4, sg32_10_L5])
    generatedRelation10Map2 (generatedRelation10FromIndex 31) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv10 :
    generatedGroup10 ≃* PCGroup smallGroup_32_10 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation10ToSource generatedToGap10
    (by decide +kernel) (by rw [card_smallGroup_32_10, card_generatedGroup10])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
