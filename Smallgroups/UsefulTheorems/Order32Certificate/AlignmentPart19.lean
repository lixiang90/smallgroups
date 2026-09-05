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

def gapExponents19 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [1, 0, 1, 0, 1], [1, 0, 1, 0, 0], [0, 1, 1, 1, 1], [0, 1, 1, 1, 0], [0, 0, 1, 0, 1], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 1], [1, 1, 0, 1, 1], [1, 1, 0, 1, 0], [1, 0, 0, 1, 1], [1, 0, 0, 1, 0], [1, 0, 1, 1, 0], [1, 0, 1, 1, 1], [0, 1, 0, 0, 0], [0, 1, 0, 0, 1], [0, 1, 1, 0, 1], [0, 1, 1, 0, 0], [0, 0, 1, 1, 1], [0, 0, 1, 1, 0], [1, 1, 1, 1, 0], [1, 1, 1, 1, 1], [1, 1, 0, 0, 1], [1, 1, 0, 0, 0], [1, 0, 0, 0, 1], [1, 0, 0, 0, 0], [0, 1, 0, 1, 0], [0, 1, 0, 1, 1], [1, 1, 1, 0, 0], [1, 1, 1, 0, 1]]
def generatedToGap19 (x : generatedGroup19) :
    PCGroup smallGroup_32_19 :=
  evalVec (gapExponents19 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_19.layers)

-- The per-layer relation certificates require a larger kernel-reduction budget.
set_option maxHeartbeats 8000000

def generatedRelation19FromIndex (i : Fin 32) : generatedGroup19 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation19Map0 : pcTower [] →* generatedGroup19 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

def generatedRelation19Map5 : pcTower [sg32_19_L5] →* generatedGroup19 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_19_L5 [])
    generatedRelation19Map0 (generatedRelation19FromIndex 1)
    (by decide +kernel)

def generatedRelation19Map4 : pcTower [sg32_19_L4, sg32_19_L5] →* generatedGroup19 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_19_L4 [sg32_19_L5])
    generatedRelation19Map5 (generatedRelation19FromIndex 8)
    (by decide +kernel)

def generatedRelation19Map3 : pcTower [sg32_19_L3, sg32_19_L4, sg32_19_L5] →* generatedGroup19 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_19_L3 [sg32_19_L4, sg32_19_L5])
    generatedRelation19Map4 (generatedRelation19FromIndex 7)
    (by decide +kernel)

def generatedRelation19Map2 : pcTower [sg32_19_L2, sg32_19_L3, sg32_19_L4, sg32_19_L5] →* generatedGroup19 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_19_L2 [sg32_19_L3, sg32_19_L4, sg32_19_L5])
    generatedRelation19Map3 (generatedRelation19FromIndex 16)
    (by decide +kernel)

def generatedRelation19ToSource : PCGroup smallGroup_32_19 →* generatedGroup19 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_19_L1 [sg32_19_L2, sg32_19_L3, sg32_19_L4, sg32_19_L5])
    generatedRelation19Map2 (generatedRelation19FromIndex 27) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv19 :
    generatedGroup19 ≃* PCGroup smallGroup_32_19 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation19ToSource generatedToGap19
    (by decide +kernel) (by rw [card_smallGroup_32_19, card_generatedGroup19])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
