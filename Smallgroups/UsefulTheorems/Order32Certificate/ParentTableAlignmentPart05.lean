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

/-! Checked table-to-PC alignment for `SmallGroup(16,5)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def parent5GapExponents : Fin 16 → List ℕ := ![[0, 0, 0, 0], [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [1, 1, 0, 0], [1, 0, 1, 0], [1, 0, 0, 1], [0, 1, 1, 0], [0, 1, 0, 1], [0, 0, 1, 1], [1, 1, 1, 0], [1, 1, 0, 1], [1, 0, 1, 1], [0, 1, 1, 1], [1, 1, 1, 1]]
def parent5TableToGap (x : CertifiedTableGroup parent5Table) :
    PCGroup smallGroup_16_5 :=
  evalVec (parent5GapExponents x.val) (pcGens smallGroup_16_5.layers)

def parent5RelationFromIndex (i : Fin 16) : CertifiedTableGroup parent5Table := ⟨i⟩

def parent5RelationMap0 : pcTower [] →* CertifiedTableGroup parent5Table where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def parent5RelationMap4 : pcTower [sg16_5_L4] →* CertifiedTableGroup parent5Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_5_L4 [])
    parent5RelationMap0 (parent5RelationFromIndex 4)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def parent5RelationMap3 : pcTower [sg16_5_L3, sg16_5_L4] →* CertifiedTableGroup parent5Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_5_L3 [sg16_5_L4])
    parent5RelationMap4 (parent5RelationFromIndex 3)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def parent5RelationMap2 : pcTower [sg16_5_L2, sg16_5_L3, sg16_5_L4] →* CertifiedTableGroup parent5Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_5_L2 [sg16_5_L3, sg16_5_L4])
    parent5RelationMap3 (parent5RelationFromIndex 2)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks the outer generator power and conjugation relations.
def parent5RelationToSource : PCGroup smallGroup_16_5 →* CertifiedTableGroup parent5Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_5_L1 [sg16_5_L2, sg16_5_L3, sg16_5_L4])
    parent5RelationMap2 (parent5RelationFromIndex 1) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def parent5TableGapEquiv :
    CertifiedTableGroup parent5Table ≃* PCGroup smallGroup_16_5 :=
  (CycExt.mulEquivOfRightInverseCardEq parent5RelationToSource parent5TableToGap
    (by decide +kernel) (by
      rw [card_smallGroup_16_5, Nat.card_eq_fintype_card,
        CertifiedTableGroup.fintype_card])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
