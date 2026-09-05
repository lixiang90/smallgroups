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

/-! Checked table-to-PC alignment for `SmallGroup(16,4)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def parent4GapExponents : Fin 16 → List ℕ := ![[0, 0, 0, 0], [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [1, 1, 0, 0], [1, 0, 1, 0], [1, 0, 0, 1], [0, 1, 1, 0], [0, 1, 0, 1], [0, 0, 1, 1], [1, 1, 1, 0], [1, 1, 0, 1], [1, 0, 1, 1], [0, 1, 1, 1], [1, 1, 1, 1]]
def parent4TableToGap (x : CertifiedTableGroup parent4Table) :
    PCGroup smallGroup_16_4 :=
  evalVec (parent4GapExponents x.val) (pcGens smallGroup_16_4.layers)

def parent4RelationFromIndex (i : Fin 16) : CertifiedTableGroup parent4Table := ⟨i⟩

def parent4RelationMap0 : pcTower [] →* CertifiedTableGroup parent4Table where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def parent4RelationMap4 : pcTower [sg16_4_L4] →* CertifiedTableGroup parent4Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_4_L4 [])
    parent4RelationMap0 (parent4RelationFromIndex 4)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def parent4RelationMap3 : pcTower [sg16_4_L3, sg16_4_L4] →* CertifiedTableGroup parent4Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_4_L3 [sg16_4_L4])
    parent4RelationMap4 (parent4RelationFromIndex 3)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def parent4RelationMap2 : pcTower [sg16_4_L2, sg16_4_L3, sg16_4_L4] →* CertifiedTableGroup parent4Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_4_L2 [sg16_4_L3, sg16_4_L4])
    parent4RelationMap3 (parent4RelationFromIndex 2)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks the outer generator power and conjugation relations.
def parent4RelationToSource : PCGroup smallGroup_16_4 →* CertifiedTableGroup parent4Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_4_L1 [sg16_4_L2, sg16_4_L3, sg16_4_L4])
    parent4RelationMap2 (parent4RelationFromIndex 1) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def parent4TableGapEquiv :
    CertifiedTableGroup parent4Table ≃* PCGroup smallGroup_16_4 :=
  (CycExt.mulEquivOfRightInverseCardEq parent4RelationToSource parent4TableToGap
    (by decide +kernel) (by
      rw [card_smallGroup_16_4, Nat.card_eq_fintype_card,
        CertifiedTableGroup.fintype_card])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
