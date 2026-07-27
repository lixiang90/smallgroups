/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order25
import Smallgroups.Classifications.Classifications_21_to_30.Order25

/-!
# Verification: order `25` — the imported pc groups match the existing representatives

`SmallGroup(25, 1) = ℤ/25` and `SmallGroup(25, 2) = ℤ/5 × ℤ/5`,
proved isomorphic to the existing representatives of the project's order-`25`
classification by `decide` (`mulEquivOfDecide`).
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

/-- `SmallGroup(25, 1) = ℤ/25`, mapping `g₁ ↦ 1`, `g₂ ↦ 5`. -/
noncomputable def order25_1_equiv : PCGroup smallGroup_25_1 ≃* CyclicRep 25 :=
  mulEquivOfDecide (pcEval [sg25_1_L1, sg25_1_L2]
    [Multiplicative.ofAdd 1, Multiplicative.ofAdd 5])

/-- `SmallGroup(25, 2) = ℤ/5 × ℤ/5`, mapping `g₁ ↦ (1, 0)`, `g₂ ↦ (0, 1)`. -/
noncomputable def order25_2_equiv : PCGroup smallGroup_25_2 ≃* ElemAbelianRep 5 :=
  mulEquivOfDecide (pcEval [sg25_2_L1, sg25_2_L2]
    [(Multiplicative.ofAdd 1, Multiplicative.ofAdd 0),
      (Multiplicative.ofAdd 0, Multiplicative.ofAdd 1)])

end Smallgroups.GAP
