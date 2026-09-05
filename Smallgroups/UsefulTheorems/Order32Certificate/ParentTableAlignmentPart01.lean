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

/-! Checked table-to-PC alignment for `SmallGroup(16,1)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def parent1GapExponents : Fin 16 → List ℕ := ![[0, 0, 0, 0], [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [1, 1, 0, 0], [1, 0, 1, 0], [1, 0, 0, 1], [0, 1, 1, 0], [0, 1, 0, 1], [0, 0, 1, 1], [1, 1, 1, 0], [1, 1, 0, 1], [1, 0, 1, 1], [0, 1, 1, 1], [1, 1, 1, 1]]
def parent1TableToGap (x : CertifiedTableGroup parent1Table) :
    PCGroup smallGroup_16_1 :=
  evalVec (parent1GapExponents x.val) (pcGens smallGroup_16_1.layers)

def parent1RelationFromIndex (i : Fin 16) : CertifiedTableGroup parent1Table := ⟨i⟩

def parent1RelationMap0 : pcTower [] →* CertifiedTableGroup parent1Table where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def parent1RelationMap4 : pcTower [sg16_1_L4] →* CertifiedTableGroup parent1Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_1_L4 [])
    parent1RelationMap0 (parent1RelationFromIndex 4)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def parent1RelationMap3 : pcTower [sg16_1_L3, sg16_1_L4] →* CertifiedTableGroup parent1Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_1_L3 [sg16_1_L4])
    parent1RelationMap4 (parent1RelationFromIndex 3)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def parent1RelationMap2 : pcTower [sg16_1_L2, sg16_1_L3, sg16_1_L4] →* CertifiedTableGroup parent1Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_1_L2 [sg16_1_L3, sg16_1_L4])
    parent1RelationMap3 (parent1RelationFromIndex 2)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks the outer generator power and conjugation relations.
def parent1RelationToSource : PCGroup smallGroup_16_1 →* CertifiedTableGroup parent1Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_1_L1 [sg16_1_L2, sg16_1_L3, sg16_1_L4])
    parent1RelationMap2 (parent1RelationFromIndex 1) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def parent1TableGapEquiv :
    CertifiedTableGroup parent1Table ≃* PCGroup smallGroup_16_1 :=
  (CycExt.mulEquivOfRightInverseCardEq parent1RelationToSource parent1TableToGap
    (by decide +kernel) (by
      rw [card_smallGroup_16_1, Nat.card_eq_fintype_card,
        CertifiedTableGroup.fintype_card])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
