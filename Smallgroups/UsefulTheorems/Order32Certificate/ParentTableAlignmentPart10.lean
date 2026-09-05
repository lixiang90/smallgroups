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

/-! Checked table-to-PC alignment for `SmallGroup(16,10)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def parent10GapExponents : Fin 16 → List ℕ := ![[0, 0, 0, 0], [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [1, 1, 0, 0], [1, 0, 1, 0], [1, 0, 0, 1], [0, 1, 1, 0], [0, 1, 0, 1], [0, 0, 1, 1], [1, 1, 1, 0], [1, 1, 0, 1], [1, 0, 1, 1], [0, 1, 1, 1], [1, 1, 1, 1]]
def parent10TableToGap (x : CertifiedTableGroup parent10Table) :
    PCGroup smallGroup_16_10 :=
  evalVec (parent10GapExponents x.val) (pcGens smallGroup_16_10.layers)

def parent10RelationFromIndex (i : Fin 16) : CertifiedTableGroup parent10Table := ⟨i⟩

def parent10RelationMap0 : pcTower [] →* CertifiedTableGroup parent10Table where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def parent10RelationMap4 : pcTower [sg16_10_L4] →* CertifiedTableGroup parent10Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_10_L4 [])
    parent10RelationMap0 (parent10RelationFromIndex 4)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def parent10RelationMap3 : pcTower [sg16_10_L3, sg16_10_L4] →* CertifiedTableGroup parent10Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_10_L3 [sg16_10_L4])
    parent10RelationMap4 (parent10RelationFromIndex 3)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def parent10RelationMap2 : pcTower [sg16_10_L2, sg16_10_L3, sg16_10_L4] →* CertifiedTableGroup parent10Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_10_L2 [sg16_10_L3, sg16_10_L4])
    parent10RelationMap3 (parent10RelationFromIndex 2)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks the outer generator power and conjugation relations.
def parent10RelationToSource : PCGroup smallGroup_16_10 →* CertifiedTableGroup parent10Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_10_L1 [sg16_10_L2, sg16_10_L3, sg16_10_L4])
    parent10RelationMap2 (parent10RelationFromIndex 1) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def parent10TableGapEquiv :
    CertifiedTableGroup parent10Table ≃* PCGroup smallGroup_16_10 :=
  (CycExt.mulEquivOfRightInverseCardEq parent10RelationToSource parent10TableToGap
    (by decide +kernel) (by
      rw [card_smallGroup_16_10, Nat.card_eq_fintype_card,
        CertifiedTableGroup.fintype_card])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
