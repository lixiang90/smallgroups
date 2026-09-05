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

def gapExponents37 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 1, 0, 0], [1, 1, 0, 0, 1], [1, 1, 1, 0, 1], [0, 1, 0, 0, 1], [0, 1, 1, 0, 1], [0, 0, 0, 1, 1], [0, 0, 1, 1, 1], [0, 0, 0, 0, 1], [0, 0, 1, 0, 1], [1, 0, 0, 0, 0], [1, 0, 1, 0, 0], [1, 1, 0, 1, 0], [1, 1, 1, 1, 0], [1, 1, 0, 0, 0], [1, 1, 1, 0, 0], [0, 1, 0, 1, 0], [0, 1, 1, 1, 0], [0, 1, 0, 0, 0], [0, 1, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 1, 0], [1, 0, 0, 1, 1], [1, 0, 1, 1, 1], [1, 0, 0, 0, 1], [1, 0, 1, 0, 1], [1, 1, 0, 1, 1], [1, 1, 1, 1, 1], [0, 1, 0, 1, 1], [0, 1, 1, 1, 1], [1, 0, 0, 1, 0], [1, 0, 1, 1, 0]]
def generatedToGap37 (x : generatedGroup37) :
    PCGroup smallGroup_32_37 :=
  evalVec (gapExponents37 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_37.layers)

-- The per-layer relation certificates require a larger kernel-reduction budget.
set_option maxHeartbeats 8000000

def generatedRelation37FromIndex (i : Fin 32) : generatedGroup37 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation37Map0 : pcTower [] →* generatedGroup37 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

def generatedRelation37Map5 : pcTower [sg32_37_L5] →* generatedGroup37 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_37_L5 [])
    generatedRelation37Map0 (generatedRelation37FromIndex 8)
    (by decide +kernel)

def generatedRelation37Map4 : pcTower [sg32_37_L4, sg32_37_L5] →* generatedGroup37 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_37_L4 [sg32_37_L5])
    generatedRelation37Map5 (generatedRelation37FromIndex 20)
    (by decide +kernel)

def generatedRelation37Map3 : pcTower [sg32_37_L3, sg32_37_L4, sg32_37_L5] →* generatedGroup37 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_37_L3 [sg32_37_L4, sg32_37_L5])
    generatedRelation37Map4 (generatedRelation37FromIndex 1)
    (by decide +kernel)

def generatedRelation37Map2 : pcTower [sg32_37_L2, sg32_37_L3, sg32_37_L4, sg32_37_L5] →* generatedGroup37 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_37_L2 [sg32_37_L3, sg32_37_L4, sg32_37_L5])
    generatedRelation37Map3 (generatedRelation37FromIndex 18)
    (by decide +kernel)

def generatedRelation37ToSource : PCGroup smallGroup_32_37 →* generatedGroup37 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_37_L1 [sg32_37_L2, sg32_37_L3, sg32_37_L4, sg32_37_L5])
    generatedRelation37Map2 (generatedRelation37FromIndex 10) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv37 :
    generatedGroup37 ≃* PCGroup smallGroup_32_37 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation37ToSource generatedToGap37
    (by decide +kernel) (by rw [card_smallGroup_32_37, card_generatedGroup37])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
