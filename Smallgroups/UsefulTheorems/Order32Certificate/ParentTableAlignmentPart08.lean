/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.Tables
import Smallgroups.GAP.Polycyclic.Imported.Order16
import Smallgroups.GAP.Polycyclic.PresentationHom

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked table-to-PC alignment for `SmallGroup(16,8)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def parent8GapExponents : Fin 16 → List ℕ := ![[0, 0, 0, 0], [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [1, 1, 0, 0], [1, 0, 1, 0], [1, 0, 0, 1], [0, 1, 1, 0], [0, 1, 0, 1], [0, 0, 1, 1], [1, 1, 1, 0], [1, 1, 0, 1], [1, 0, 1, 1], [0, 1, 1, 1], [1, 1, 1, 1]]
def parent8TableToGap (x : CertifiedTableGroup parent8Table) :
    PCGroup smallGroup_16_8 :=
  evalVec (parent8GapExponents x.val) (pcGens smallGroup_16_8.layers)

def parent8RelationFromIndex (i : Fin 16) : CertifiedTableGroup parent8Table := ⟨i⟩

def parent8RelationMap0 : pcTower [] →* CertifiedTableGroup parent8Table where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def parent8RelationMap4 : pcTower [sg16_8_L4] →* CertifiedTableGroup parent8Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_8_L4 [])
    parent8RelationMap0 (parent8RelationFromIndex 4)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def parent8RelationMap3 : pcTower [sg16_8_L3, sg16_8_L4] →* CertifiedTableGroup parent8Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_8_L3 [sg16_8_L4])
    parent8RelationMap4 (parent8RelationFromIndex 3)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def parent8RelationMap2 : pcTower [sg16_8_L2, sg16_8_L3, sg16_8_L4] →* CertifiedTableGroup parent8Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_8_L2 [sg16_8_L3, sg16_8_L4])
    parent8RelationMap3 (parent8RelationFromIndex 2)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks the outer generator power and conjugation relations.
def parent8RelationToSource : PCGroup smallGroup_16_8 →* CertifiedTableGroup parent8Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_8_L1 [sg16_8_L2, sg16_8_L3, sg16_8_L4])
    parent8RelationMap2 (parent8RelationFromIndex 1) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def parent8TableGapEquiv :
    CertifiedTableGroup parent8Table ≃* PCGroup smallGroup_16_8 :=
  (CycExt.mulEquivOfRightInverseCardEq parent8RelationToSource parent8TableToGap
    (by decide +kernel) (by
      rw [card_smallGroup_16_8, Nat.card_eq_fintype_card,
        CertifiedTableGroup.fintype_card])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
