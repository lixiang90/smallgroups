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

/-! Checked table-to-PC alignment for `SmallGroup(16,9)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def parent9GapExponents : Fin 16 → List ℕ := ![[0, 0, 0, 0], [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [1, 1, 0, 0], [1, 0, 1, 0], [1, 0, 0, 1], [0, 1, 1, 0], [0, 1, 0, 1], [0, 0, 1, 1], [1, 1, 1, 0], [1, 1, 0, 1], [1, 0, 1, 1], [0, 1, 1, 1], [1, 1, 1, 1]]
def parent9TableToGap (x : CertifiedTableGroup parent9Table) :
    PCGroup smallGroup_16_9 :=
  evalVec (parent9GapExponents x.val) (pcGens smallGroup_16_9.layers)

-- The per-layer relation certificates require a larger kernel-reduction budget.
set_option maxHeartbeats 8000000

def parent9RelationFromIndex (i : Fin 16) : CertifiedTableGroup parent9Table := ⟨i⟩

def parent9RelationMap0 : pcTower [] →* CertifiedTableGroup parent9Table where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

def parent9RelationMap4 : pcTower [sg16_9_L4] →* CertifiedTableGroup parent9Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_9_L4 [])
    parent9RelationMap0 (parent9RelationFromIndex 4)
    (by decide +kernel)

def parent9RelationMap3 : pcTower [sg16_9_L3, sg16_9_L4] →* CertifiedTableGroup parent9Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_9_L3 [sg16_9_L4])
    parent9RelationMap4 (parent9RelationFromIndex 3)
    (by decide +kernel)

def parent9RelationMap2 : pcTower [sg16_9_L2, sg16_9_L3, sg16_9_L4] →* CertifiedTableGroup parent9Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_9_L2 [sg16_9_L3, sg16_9_L4])
    parent9RelationMap3 (parent9RelationFromIndex 2)
    (by decide +kernel)

def parent9RelationToSource : PCGroup smallGroup_16_9 →* CertifiedTableGroup parent9Table :=
  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData sg16_9_L1 [sg16_9_L2, sg16_9_L3, sg16_9_L4])
    parent9RelationMap2 (parent9RelationFromIndex 1) (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite pc relations and explicit right inverse.
noncomputable def parent9TableGapEquiv :
    CertifiedTableGroup parent9Table ≃* PCGroup smallGroup_16_9 :=
  (CycExt.mulEquivOfRightInverseCardEq parent9RelationToSource parent9TableToGap
    (by decide +kernel) (by
      rw [card_smallGroup_16_9, Nat.card_eq_fintype_card,
        CertifiedTableGroup.fintype_card])).symm

end Smallgroups.UsefulTheorems.Order32Certificate
