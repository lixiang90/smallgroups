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

/-! Checked table-to-PC alignment for `SmallGroup(16,13)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def parent13GapExponents : Fin 16 → List ℕ := ![[0, 0, 0, 0], [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [1, 1, 0, 0], [1, 0, 1, 0], [1, 0, 0, 1], [0, 1, 1, 0], [0, 1, 0, 1], [0, 0, 1, 1], [1, 1, 1, 0], [1, 1, 0, 1], [1, 0, 1, 1], [0, 1, 1, 1], [1, 1, 1, 1]]
def parent13TableToGap (x : CertifiedTableGroup parent13Table) :
    PCGroup smallGroup_16_13 :=
  evalVec (parent13GapExponents x.val) (pcGens smallGroup_16_13.layers)

def parent13RelationFromIndex (i : Fin 16) : CertifiedTableGroup parent13Table := ⟨i⟩

def parent13RelationMap0 : pcTower [] →* CertifiedTableGroup parent13Table where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def parent13RelationMap4 : pcTower [sg16_13_L4] →* CertifiedTableGroup parent13Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_13_L4 [])
    parent13RelationMap0 (parent13RelationFromIndex 4)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def parent13RelationMap3 : pcTower [sg16_13_L3, sg16_13_L4] →* CertifiedTableGroup parent13Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_13_L3 [sg16_13_L4])
    parent13RelationMap4 (parent13RelationFromIndex 3)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def parent13RelationMap2 : pcTower [sg16_13_L2, sg16_13_L3, sg16_13_L4] →* CertifiedTableGroup parent13Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_13_L2 [sg16_13_L3, sg16_13_L4])
    parent13RelationMap3 (parent13RelationFromIndex 2)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks the outer generator power and conjugation relations.
def parent13RelationToSource : PCGroup smallGroup_16_13 →* CertifiedTableGroup parent13Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_13_L1 [sg16_13_L2, sg16_13_L3, sg16_13_L4])
    parent13RelationMap2 (parent13RelationFromIndex 1) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def parent13TableGapEquiv :
    CertifiedTableGroup parent13Table ≃* PCGroup smallGroup_16_13 :=
  (CycExt.mulEquivOfRightInverseCardEq parent13RelationToSource parent13TableToGap
    (by decide +kernel) (by
      rw [card_smallGroup_16_13, Nat.card_eq_fintype_card,
        CertifiedTableGroup.fintype_card])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
