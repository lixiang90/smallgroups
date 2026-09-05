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

/-! Checked table-to-PC alignment for `SmallGroup(16,14)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def parent14GapExponents : Fin 16 → List ℕ := ![[0, 0, 0, 0], [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [1, 1, 0, 0], [1, 0, 1, 0], [1, 0, 0, 1], [0, 1, 1, 0], [0, 1, 0, 1], [0, 0, 1, 1], [1, 1, 1, 0], [1, 1, 0, 1], [1, 0, 1, 1], [0, 1, 1, 1], [1, 1, 1, 1]]
def parent14TableToGap (x : CertifiedTableGroup parent14Table) :
    PCGroup smallGroup_16_14 :=
  evalVec (parent14GapExponents x.val) (pcGens smallGroup_16_14.layers)

-- The per-layer relation certificates require a larger kernel-reduction budget.
set_option maxHeartbeats 8000000

def parent14RelationFromIndex (i : Fin 16) : CertifiedTableGroup parent14Table := ⟨i⟩

def parent14RelationMap0 : pcTower [] →* CertifiedTableGroup parent14Table where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

def parent14RelationMap4 : pcTower [sg16_14_L4] →* CertifiedTableGroup parent14Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_14_L4 [])
    parent14RelationMap0 (parent14RelationFromIndex 4)
    (by decide +kernel)

def parent14RelationMap3 : pcTower [sg16_14_L3, sg16_14_L4] →* CertifiedTableGroup parent14Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_14_L3 [sg16_14_L4])
    parent14RelationMap4 (parent14RelationFromIndex 3)
    (by decide +kernel)

def parent14RelationMap2 : pcTower [sg16_14_L2, sg16_14_L3, sg16_14_L4] →* CertifiedTableGroup parent14Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_14_L2 [sg16_14_L3, sg16_14_L4])
    parent14RelationMap3 (parent14RelationFromIndex 2)
    (by decide +kernel)

def parent14RelationToSource : PCGroup smallGroup_16_14 →* CertifiedTableGroup parent14Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_14_L1 [sg16_14_L2, sg16_14_L3, sg16_14_L4])
    parent14RelationMap2 (parent14RelationFromIndex 1) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def parent14TableGapEquiv :
    CertifiedTableGroup parent14Table ≃* PCGroup smallGroup_16_14 :=
  (CycExt.mulEquivOfRightInverseCardEq parent14RelationToSource parent14TableToGap
    (by decide +kernel) (by
      rw [card_smallGroup_16_14, Nat.card_eq_fintype_card,
        CertifiedTableGroup.fintype_card])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
