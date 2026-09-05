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

/-! Checked table-to-PC alignment for `SmallGroup(16,7)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def parent7GapExponents : Fin 16 → List ℕ := ![[0, 0, 0, 0], [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [1, 1, 0, 0], [1, 0, 1, 0], [1, 0, 0, 1], [0, 1, 1, 0], [0, 1, 0, 1], [0, 0, 1, 1], [1, 1, 1, 0], [1, 1, 0, 1], [1, 0, 1, 1], [0, 1, 1, 1], [1, 1, 1, 1]]
def parent7TableToGap (x : CertifiedTableGroup parent7Table) :
    PCGroup smallGroup_16_7 :=
  evalVec (parent7GapExponents x.val) (pcGens smallGroup_16_7.layers)

def parent7RelationFromIndex (i : Fin 16) : CertifiedTableGroup parent7Table := ⟨i⟩

def parent7RelationMap0 : pcTower [] →* CertifiedTableGroup parent7Table where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def parent7RelationMap4 : pcTower [sg16_7_L4] →* CertifiedTableGroup parent7Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_7_L4 [])
    parent7RelationMap0 (parent7RelationFromIndex 4)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def parent7RelationMap3 : pcTower [sg16_7_L3, sg16_7_L4] →* CertifiedTableGroup parent7Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_7_L3 [sg16_7_L4])
    parent7RelationMap4 (parent7RelationFromIndex 3)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def parent7RelationMap2 : pcTower [sg16_7_L2, sg16_7_L3, sg16_7_L4] →* CertifiedTableGroup parent7Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_7_L2 [sg16_7_L3, sg16_7_L4])
    parent7RelationMap3 (parent7RelationFromIndex 2)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks the outer generator power and conjugation relations.
def parent7RelationToSource : PCGroup smallGroup_16_7 →* CertifiedTableGroup parent7Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_7_L1 [sg16_7_L2, sg16_7_L3, sg16_7_L4])
    parent7RelationMap2 (parent7RelationFromIndex 1) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def parent7TableGapEquiv :
    CertifiedTableGroup parent7Table ≃* PCGroup smallGroup_16_7 :=
  (CycExt.mulEquivOfRightInverseCardEq parent7RelationToSource parent7TableToGap
    (by decide +kernel) (by
      rw [card_smallGroup_16_7, Nat.card_eq_fintype_card,
        CertifiedTableGroup.fintype_card])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
