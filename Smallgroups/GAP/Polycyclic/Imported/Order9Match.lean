/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order9
import Smallgroups.Classifications.Classifications_1_to_10.Order9

/-!
# Verification: order `9` — the imported pc groups match the existing representatives

`SmallGroup(9, 1) = ℤ/9` and `SmallGroup(9, 2) = ℤ/3 × ℤ/3`,
proved isomorphic to the existing representatives of the project's order-`9`
classification by `decide` (`mulEquivOfDecide`).
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

/-- `SmallGroup(9, 1) = ℤ/9`, mapping `g₁ ↦ 1`, `g₂ ↦ 3`. -/
noncomputable def order9_1_equiv : PCGroup smallGroup_9_1 ≃* CyclicRep 9 :=
  mulEquivOfDecide (pcEval [sg9_1_L1, sg9_1_L2]
    [Multiplicative.ofAdd 1, Multiplicative.ofAdd 3])

/-- `SmallGroup(9, 2) = ℤ/3 × ℤ/3`, mapping `g₁ ↦ (1, 0)`, `g₂ ↦ (0, 1)`. -/
noncomputable def order9_2_equiv : PCGroup smallGroup_9_2 ≃* ElemAbelianRep 3 :=
  mulEquivOfDecide (pcEval [sg9_2_L1, sg9_2_L2]
    [(Multiplicative.ofAdd 1, Multiplicative.ofAdd 0),
      (Multiplicative.ofAdd 0, Multiplicative.ofAdd 1)])

end Smallgroups.GAP
