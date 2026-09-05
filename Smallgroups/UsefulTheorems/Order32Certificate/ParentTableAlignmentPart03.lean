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

/-! Checked table-to-PC alignment for `SmallGroup(16,3)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def parent3GapExponents : Fin 16 → List ℕ := ![[0, 0, 0, 0], [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [1, 1, 0, 0], [1, 0, 1, 0], [1, 0, 0, 1], [0, 1, 1, 0], [0, 1, 0, 1], [0, 0, 1, 1], [1, 1, 1, 0], [1, 1, 0, 1], [1, 0, 1, 1], [0, 1, 1, 1], [1, 1, 1, 1]]
def parent3TableToGap (x : CertifiedTableGroup parent3Table) :
    PCGroup smallGroup_16_3 :=
  evalVec (parent3GapExponents x.val) (pcGens smallGroup_16_3.layers)

def parent3RelationFromIndex (i : Fin 16) : CertifiedTableGroup parent3Table := ⟨i⟩

def parent3RelationMap0 : pcTower [] →* CertifiedTableGroup parent3Table where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def parent3RelationMap4 : pcTower [sg16_3_L4] →* CertifiedTableGroup parent3Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_3_L4 [])
    parent3RelationMap0 (parent3RelationFromIndex 4)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def parent3RelationMap3 : pcTower [sg16_3_L3, sg16_3_L4] →* CertifiedTableGroup parent3Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_3_L3 [sg16_3_L4])
    parent3RelationMap4 (parent3RelationFromIndex 3)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def parent3RelationMap2 : pcTower [sg16_3_L2, sg16_3_L3, sg16_3_L4] →* CertifiedTableGroup parent3Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_3_L2 [sg16_3_L3, sg16_3_L4])
    parent3RelationMap3 (parent3RelationFromIndex 2)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks the outer generator power and conjugation relations.
def parent3RelationToSource : PCGroup smallGroup_16_3 →* CertifiedTableGroup parent3Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_3_L1 [sg16_3_L2, sg16_3_L3, sg16_3_L4])
    parent3RelationMap2 (parent3RelationFromIndex 1) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def parent3TableGapEquiv :
    CertifiedTableGroup parent3Table ≃* PCGroup smallGroup_16_3 :=
  (CycExt.mulEquivOfRightInverseCardEq parent3RelationToSource parent3TableToGap
    (by decide +kernel) (by
      rw [card_smallGroup_16_3, Nat.card_eq_fintype_card,
        CertifiedTableGroup.fintype_card])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
