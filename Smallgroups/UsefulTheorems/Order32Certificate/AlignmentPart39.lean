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

def gapExponents39 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 1, 0, 0], [1, 0, 1, 1, 1], [1, 0, 0, 1, 1], [0, 1, 1, 1, 1], [0, 1, 0, 1, 1], [0, 0, 0, 1, 0], [0, 0, 1, 1, 0], [0, 0, 0, 0, 1], [0, 0, 1, 0, 1], [1, 1, 0, 0, 0], [1, 1, 1, 0, 0], [1, 0, 1, 0, 0], [1, 0, 0, 0, 0], [1, 0, 1, 1, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [0, 1, 0, 0, 0], [0, 1, 1, 1, 0], [0, 1, 0, 1, 0], [0, 0, 0, 1, 1], [0, 0, 1, 1, 1], [1, 1, 0, 1, 0], [1, 1, 1, 1, 0], [1, 1, 0, 0, 1], [1, 1, 1, 0, 1], [1, 0, 1, 0, 1], [1, 0, 0, 0, 1], [0, 1, 1, 0, 1], [0, 1, 0, 0, 1], [1, 1, 0, 1, 1], [1, 1, 1, 1, 1]]
def generatedToGap39 (x : generatedGroup39) :
    PCGroup smallGroup_32_39 :=
  evalVec (gapExponents39 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_39.layers)

-- The per-layer relation certificates require a larger kernel-reduction budget.
set_option maxHeartbeats 8000000

def generatedRelation39FromIndex (i : Fin 32) : generatedGroup39 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation39Map0 : pcTower [] →* generatedGroup39 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

def generatedRelation39Map5 : pcTower [sg32_39_L5] →* generatedGroup39 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_39_L5 [])
    generatedRelation39Map0 (generatedRelation39FromIndex 8)
    (by decide +kernel)

def generatedRelation39Map4 : pcTower [sg32_39_L4, sg32_39_L5] →* generatedGroup39 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_39_L4 [sg32_39_L5])
    generatedRelation39Map5 (generatedRelation39FromIndex 6)
    (by decide +kernel)

def generatedRelation39Map3 : pcTower [sg32_39_L3, sg32_39_L4, sg32_39_L5] →* generatedGroup39 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_39_L3 [sg32_39_L4, sg32_39_L5])
    generatedRelation39Map4 (generatedRelation39FromIndex 1)
    (by decide +kernel)

def generatedRelation39Map2 : pcTower [sg32_39_L2, sg32_39_L3, sg32_39_L4, sg32_39_L5] →* generatedGroup39 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_39_L2 [sg32_39_L3, sg32_39_L4, sg32_39_L5])
    generatedRelation39Map3 (generatedRelation39FromIndex 17)
    (by decide +kernel)

def generatedRelation39ToSource : PCGroup smallGroup_32_39 →* generatedGroup39 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_39_L1 [sg32_39_L2, sg32_39_L3, sg32_39_L4, sg32_39_L5])
    generatedRelation39Map2 (generatedRelation39FromIndex 13) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv39 :
    generatedGroup39 ≃* PCGroup smallGroup_32_39 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation39ToSource generatedToGap39
    (by decide +kernel) (by rw [card_smallGroup_32_39, card_generatedGroup39])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
