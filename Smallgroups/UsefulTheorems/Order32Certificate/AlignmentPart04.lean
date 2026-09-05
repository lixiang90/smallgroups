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

def gapExponents4 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 1, 0, 1], [1, 1, 1, 0, 0], [1, 0, 0, 0, 0], [1, 0, 0, 0, 1], [0, 0, 1, 1, 0], [0, 0, 1, 1, 1], [0, 0, 1, 0, 0], [0, 0, 1, 0, 1], [0, 1, 0, 0, 0], [0, 1, 0, 0, 1], [1, 1, 0, 1, 1], [1, 1, 0, 1, 0], [1, 1, 0, 0, 1], [1, 1, 0, 0, 0], [1, 0, 1, 1, 0], [1, 0, 1, 1, 1], [1, 0, 1, 0, 0], [1, 0, 1, 0, 1], [0, 0, 0, 1, 0], [0, 0, 0, 1, 1], [0, 1, 1, 1, 0], [0, 1, 1, 1, 1], [0, 1, 1, 0, 0], [0, 1, 1, 0, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 0], [1, 0, 0, 1, 0], [1, 0, 0, 1, 1], [0, 1, 0, 1, 0], [0, 1, 0, 1, 1]]
def generatedToGap4 (x : generatedGroup4) :
    PCGroup smallGroup_32_4 :=
  evalVec (gapExponents4 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_4.layers)

-- The per-layer relation certificates require a larger kernel-reduction budget.
set_option maxHeartbeats 8000000

def generatedRelation4FromIndex (i : Fin 32) : generatedGroup4 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation4Map0 : pcTower [] →* generatedGroup4 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

def generatedRelation4Map5 : pcTower [sg32_4_L5] →* generatedGroup4 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_4_L5 [])
    generatedRelation4Map0 (generatedRelation4FromIndex 1)
    (by decide +kernel)

def generatedRelation4Map4 : pcTower [sg32_4_L4, sg32_4_L5] →* generatedGroup4 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_4_L4 [sg32_4_L5])
    generatedRelation4Map5 (generatedRelation4FromIndex 20)
    (by decide +kernel)

def generatedRelation4Map3 : pcTower [sg32_4_L3, sg32_4_L4, sg32_4_L5] →* generatedGroup4 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_4_L3 [sg32_4_L4, sg32_4_L5])
    generatedRelation4Map4 (generatedRelation4FromIndex 8)
    (by decide +kernel)

def generatedRelation4Map2 : pcTower [sg32_4_L2, sg32_4_L3, sg32_4_L4, sg32_4_L5] →* generatedGroup4 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_4_L2 [sg32_4_L3, sg32_4_L4, sg32_4_L5])
    generatedRelation4Map3 (generatedRelation4FromIndex 10)
    (by decide +kernel)

def generatedRelation4ToSource : PCGroup smallGroup_32_4 →* generatedGroup4 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_4_L1 [sg32_4_L2, sg32_4_L3, sg32_4_L4, sg32_4_L5])
    generatedRelation4Map2 (generatedRelation4FromIndex 4) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv4 :
    generatedGroup4 ≃* PCGroup smallGroup_32_4 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation4ToSource generatedToGap4
    (by decide +kernel) (by rw [card_smallGroup_32_4, card_generatedGroup4])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
