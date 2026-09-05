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

def gapExponents33 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 1, 0], [1, 1, 1, 0, 0], [1, 1, 1, 1, 0], [0, 1, 0, 1, 0], [0, 1, 0, 0, 0], [0, 0, 0, 1, 1], [0, 0, 0, 0, 1], [1, 1, 0, 1, 1], [1, 1, 0, 0, 1], [0, 1, 1, 0, 0], [0, 1, 1, 1, 0], [0, 0, 1, 0, 1], [0, 0, 1, 1, 1], [1, 0, 1, 0, 1], [1, 0, 1, 1, 1], [1, 1, 1, 0, 1], [1, 1, 1, 1, 1], [0, 1, 0, 0, 1], [0, 1, 0, 1, 1], [1, 0, 0, 1, 0], [1, 0, 0, 0, 0], [1, 1, 0, 0, 0], [1, 1, 0, 1, 0], [0, 1, 1, 0, 1], [0, 1, 1, 1, 1], [1, 0, 1, 0, 0], [1, 0, 1, 1, 0], [1, 0, 0, 0, 1], [1, 0, 0, 1, 1]]
def generatedToGap33 (x : generatedGroup33) :
    PCGroup smallGroup_32_33 :=
  evalVec (gapExponents33 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_33.layers)

def generatedRelation33FromIndex (i : Fin 32) : generatedGroup33 where
  fst := ((i.val % 2 : ℕ) : ZMod 2)
  snd := ⟨⟨i.val / 2, by omega⟩⟩

def generatedRelation33Map0 : pcTower [] →* generatedGroup33 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation33Map5 : pcTower [sg32_33_L5] →* generatedGroup33 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_33_L5 [])
    generatedRelation33Map0 (generatedRelation33FromIndex 9)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation33Map4 : pcTower [sg32_33_L4, sg32_33_L5] →* generatedGroup33 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_33_L4 [sg32_33_L5])
    generatedRelation33Map5 (generatedRelation33FromIndex 1)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation33Map3 : pcTower [sg32_33_L3, sg32_33_L4, sg32_33_L5] →* generatedGroup33 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_33_L3 [sg32_33_L4, sg32_33_L5])
    generatedRelation33Map4 (generatedRelation33FromIndex 2)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def generatedRelation33Map2 : pcTower [sg32_33_L2, sg32_33_L3, sg32_33_L4, sg32_33_L5] →* generatedGroup33 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_33_L2 [sg32_33_L3, sg32_33_L4, sg32_33_L5])
    generatedRelation33Map3 (generatedRelation33FromIndex 7)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks the outer generator power and conjugation relations.
def generatedRelation33ToSource : PCGroup smallGroup_32_33 →* generatedGroup33 :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg32_33_L1 [sg32_33_L2, sg32_33_L3, sg32_33_L4, sg32_33_L5])
    generatedRelation33Map2 (generatedRelation33FromIndex 23) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def generatedGapEquiv33 :
    generatedGroup33 ≃* PCGroup smallGroup_32_33 :=
  (CycExt.mulEquivOfRightInverseCardEq generatedRelation33ToSource generatedToGap33
    (by decide +kernel) (by rw [card_smallGroup_32_33, card_generatedGroup33])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
