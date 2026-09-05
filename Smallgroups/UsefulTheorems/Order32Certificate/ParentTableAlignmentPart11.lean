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

/-! Checked table-to-PC alignment for `SmallGroup(16,11)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def parent11GapExponents : Fin 16 → List ℕ := ![[0, 0, 0, 0], [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [1, 1, 0, 0], [1, 0, 1, 0], [1, 0, 0, 1], [0, 1, 1, 0], [0, 1, 0, 1], [0, 0, 1, 1], [1, 1, 1, 0], [1, 1, 0, 1], [1, 0, 1, 1], [0, 1, 1, 1], [1, 1, 1, 1]]
def parent11TableToGap (x : CertifiedTableGroup parent11Table) :
    PCGroup smallGroup_16_11 :=
  evalVec (parent11GapExponents x.val) (pcGens smallGroup_16_11.layers)

def parent11RelationFromIndex (i : Fin 16) : CertifiedTableGroup parent11Table := ⟨i⟩

def parent11RelationMap0 : pcTower [] →* CertifiedTableGroup parent11Table where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def parent11RelationMap4 : pcTower [sg16_11_L4] →* CertifiedTableGroup parent11Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_11_L4 [])
    parent11RelationMap0 (parent11RelationFromIndex 4)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def parent11RelationMap3 : pcTower [sg16_11_L3, sg16_11_L4] →* CertifiedTableGroup parent11Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_11_L3 [sg16_11_L4])
    parent11RelationMap4 (parent11RelationFromIndex 3)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks this layer's generator power and conjugation relations.
def parent11RelationMap2 : pcTower [sg16_11_L2, sg16_11_L3, sg16_11_L4] →* CertifiedTableGroup parent11Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_11_L2 [sg16_11_L3, sg16_11_L4])
    parent11RelationMap3 (parent11RelationFromIndex 2)
    (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel checks the outer generator power and conjugation relations.
def parent11RelationToSource : PCGroup smallGroup_16_11 →* CertifiedTableGroup parent11Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_11_L1 [sg16_11_L2, sg16_11_L3, sg16_11_L4])
    parent11RelationMap2 (parent11RelationFromIndex 1) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def parent11TableGapEquiv :
    CertifiedTableGroup parent11Table ≃* PCGroup smallGroup_16_11 :=
  (CycExt.mulEquivOfRightInverseCardEq parent11RelationToSource parent11TableToGap
    (by decide +kernel) (by
      rw [card_smallGroup_16_11, Nat.card_eq_fintype_card,
        CertifiedTableGroup.fintype_card])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
