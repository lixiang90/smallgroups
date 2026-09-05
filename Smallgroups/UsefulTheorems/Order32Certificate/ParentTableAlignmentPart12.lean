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

/-! Checked table-to-PC alignment for `SmallGroup(16,12)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def parent12GapExponents : Fin 16 → List ℕ := ![[0, 0, 0, 0], [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [1, 1, 0, 0], [1, 0, 1, 0], [1, 0, 0, 1], [0, 1, 1, 0], [0, 1, 0, 1], [0, 0, 1, 1], [1, 1, 1, 0], [1, 1, 0, 1], [1, 0, 1, 1], [0, 1, 1, 1], [1, 1, 1, 1]]
def parent12TableToGap (x : CertifiedTableGroup parent12Table) :
    PCGroup smallGroup_16_12 :=
  evalVec (parent12GapExponents x.val) (pcGens smallGroup_16_12.layers)

-- The per-layer relation certificates require a larger kernel-reduction budget.
set_option maxHeartbeats 8000000

def parent12RelationFromIndex (i : Fin 16) : CertifiedTableGroup parent12Table := ⟨i⟩

def parent12RelationMap0 : pcTower [] →* CertifiedTableGroup parent12Table where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

def parent12RelationMap4 : pcTower [sg16_12_L4] →* CertifiedTableGroup parent12Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_12_L4 [])
    parent12RelationMap0 (parent12RelationFromIndex 4)
    (by decide +kernel)

def parent12RelationMap3 : pcTower [sg16_12_L3, sg16_12_L4] →* CertifiedTableGroup parent12Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_12_L3 [sg16_12_L4])
    parent12RelationMap4 (parent12RelationFromIndex 3)
    (by decide +kernel)

def parent12RelationMap2 : pcTower [sg16_12_L2, sg16_12_L3, sg16_12_L4] →* CertifiedTableGroup parent12Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_12_L2 [sg16_12_L3, sg16_12_L4])
    parent12RelationMap3 (parent12RelationFromIndex 2)
    (by decide +kernel)

def parent12RelationToSource : PCGroup smallGroup_16_12 →* CertifiedTableGroup parent12Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_12_L1 [sg16_12_L2, sg16_12_L3, sg16_12_L4])
    parent12RelationMap2 (parent12RelationFromIndex 1) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def parent12TableGapEquiv :
    CertifiedTableGroup parent12Table ≃* PCGroup smallGroup_16_12 :=
  (CycExt.mulEquivOfRightInverseCardEq parent12RelationToSource parent12TableToGap
    (by decide +kernel) (by
      rw [card_smallGroup_16_12, Nat.card_eq_fintype_card,
        CertifiedTableGroup.fintype_card])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
