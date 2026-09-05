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

/-! Checked table-to-PC alignment for `SmallGroup(16,2)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def parent2GapExponents : Fin 16 → List ℕ := ![[0, 0, 0, 0], [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [1, 1, 0, 0], [1, 0, 1, 0], [1, 0, 0, 1], [0, 1, 1, 0], [0, 1, 0, 1], [0, 0, 1, 1], [1, 1, 1, 0], [1, 1, 0, 1], [1, 0, 1, 1], [0, 1, 1, 1], [1, 1, 1, 1]]
def parent2TableToGap (x : CertifiedTableGroup parent2Table) :
    PCGroup smallGroup_16_2 :=
  evalVec (parent2GapExponents x.val) (pcGens smallGroup_16_2.layers)

-- The per-layer relation certificates require a larger kernel-reduction budget.
set_option maxHeartbeats 8000000

def parent2RelationFromIndex (i : Fin 16) : CertifiedTableGroup parent2Table := ⟨i⟩

def parent2RelationMap0 : pcTower [] →* CertifiedTableGroup parent2Table where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

def parent2RelationMap4 : pcTower [sg16_2_L4] →* CertifiedTableGroup parent2Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_2_L4 [])
    parent2RelationMap0 (parent2RelationFromIndex 4)
    (by decide +kernel)

def parent2RelationMap3 : pcTower [sg16_2_L3, sg16_2_L4] →* CertifiedTableGroup parent2Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_2_L3 [sg16_2_L4])
    parent2RelationMap4 (parent2RelationFromIndex 3)
    (by decide +kernel)

def parent2RelationMap2 : pcTower [sg16_2_L2, sg16_2_L3, sg16_2_L4] →* CertifiedTableGroup parent2Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_2_L2 [sg16_2_L3, sg16_2_L4])
    parent2RelationMap3 (parent2RelationFromIndex 2)
    (by decide +kernel)

def parent2RelationToSource : PCGroup smallGroup_16_2 →* CertifiedTableGroup parent2Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_2_L1 [sg16_2_L2, sg16_2_L3, sg16_2_L4])
    parent2RelationMap2 (parent2RelationFromIndex 1) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def parent2TableGapEquiv :
    CertifiedTableGroup parent2Table ≃* PCGroup smallGroup_16_2 :=
  (CycExt.mulEquivOfRightInverseCardEq parent2RelationToSource parent2TableToGap
    (by decide +kernel) (by
      rw [card_smallGroup_16_2, Nat.card_eq_fintype_card,
        CertifiedTableGroup.fintype_card])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
