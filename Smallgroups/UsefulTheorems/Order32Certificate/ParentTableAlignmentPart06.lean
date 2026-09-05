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

/-! Checked table-to-PC alignment for `SmallGroup(16,6)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def parent6GapExponents : Fin 16 → List ℕ := ![[0, 0, 0, 0], [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [1, 1, 0, 0], [1, 0, 1, 0], [1, 0, 0, 1], [0, 1, 1, 0], [0, 1, 0, 1], [0, 0, 1, 1], [1, 1, 1, 0], [1, 1, 0, 1], [1, 0, 1, 1], [0, 1, 1, 1], [1, 1, 1, 1]]
def parent6TableToGap (x : CertifiedTableGroup parent6Table) :
    PCGroup smallGroup_16_6 :=
  evalVec (parent6GapExponents x.val) (pcGens smallGroup_16_6.layers)

def parent6RelationFromIndex (i : Fin 16) : CertifiedTableGroup parent6Table := ⟨i⟩

def parent6RelationMap0 : pcTower [] →* CertifiedTableGroup parent6Table where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def parent6RelationMap4 : pcTower [sg16_6_L4] →* CertifiedTableGroup parent6Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_6_L4 [])
    parent6RelationMap0 (parent6RelationFromIndex 4)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def parent6RelationMap3 : pcTower [sg16_6_L3, sg16_6_L4] →* CertifiedTableGroup parent6Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_6_L3 [sg16_6_L4])
    parent6RelationMap4 (parent6RelationFromIndex 3)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def parent6RelationMap2 : pcTower [sg16_6_L2, sg16_6_L3, sg16_6_L4] →* CertifiedTableGroup parent6Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_6_L2 [sg16_6_L3, sg16_6_L4])
    parent6RelationMap3 (parent6RelationFromIndex 2)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks the outer generator power and conjugation relations.
def parent6RelationToSource : PCGroup smallGroup_16_6 →* CertifiedTableGroup parent6Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_6_L1 [sg16_6_L2, sg16_6_L3, sg16_6_L4])
    parent6RelationMap2 (parent6RelationFromIndex 1) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def parent6TableGapEquiv :
    CertifiedTableGroup parent6Table ≃* PCGroup smallGroup_16_6 :=
  (CycExt.mulEquivOfRightInverseCardEq parent6RelationToSource parent6TableToGap
    (by decide +kernel) (by
      rw [card_smallGroup_16_6, Nat.card_eq_fintype_card,
        CertifiedTableGroup.fintype_card])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
