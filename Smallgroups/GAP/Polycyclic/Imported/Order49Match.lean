/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order49
import Smallgroups.Classifications.Classifications_41_to_50.Order49

/-!
# Verification: order `49` — the imported pc groups match the existing representatives

`SmallGroup(49, 1) = ℤ/49` and `SmallGroup(49, 2) = ℤ/7 × ℤ/7`,
proved isomorphic to the existing representatives of the project's order-`49`
classification by `decide` (`mulEquivOfDecide`).
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

/-- `SmallGroup(49, 1) = ℤ/49`, mapping `g₁ ↦ 1`, `g₂ ↦ 7`. -/
noncomputable def order49_1_equiv : PCGroup smallGroup_49_1 ≃* CyclicRep 49 :=
  mulEquivOfDecide (pcEval [sg49_1_L1, sg49_1_L2]
    [Multiplicative.ofAdd 1, Multiplicative.ofAdd 7])

/-- `SmallGroup(49, 2) = ℤ/7 × ℤ/7`, mapping `g₁ ↦ (1, 0)`, `g₂ ↦ (0, 1)`. -/
noncomputable def order49_2_equiv : PCGroup smallGroup_49_2 ≃* ElemAbelianRep 7 :=
  mulEquivOfDecide (pcEval [sg49_2_L1, sg49_2_L2]
    [(Multiplicative.ofAdd 1, Multiplicative.ofAdd 0),
      (Multiplicative.ofAdd 0, Multiplicative.ofAdd 1)])

end Smallgroups.GAP
