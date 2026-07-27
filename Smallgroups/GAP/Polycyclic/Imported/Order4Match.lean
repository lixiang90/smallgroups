/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order4
import Smallgroups.Classifications.Classifications_1_to_10.Order4

/-!
# Verification: order `4` — the imported pc groups match the existing representatives

`SmallGroup(4, 1) = ℤ/4` and `SmallGroup(4, 2) = ℤ/2 × ℤ/2`,
proved isomorphic to the existing representatives of the project's order-`4`
classification by `decide` (`mulEquivOfDecide`).
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

/-- `SmallGroup(4, 1) = ℤ/4`, mapping `g₁ ↦ 1`, `g₂ ↦ 2`. -/
noncomputable def order4_1_equiv : PCGroup smallGroup_4_1 ≃* CyclicRep 4 :=
  mulEquivOfDecide (pcEval [sg4_1_L1, sg4_1_L2]
    [Multiplicative.ofAdd 1, Multiplicative.ofAdd 2])

/-- `SmallGroup(4, 2) = ℤ/2 × ℤ/2`, mapping `g₁ ↦ (1, 0)`, `g₂ ↦ (0, 1)`. -/
noncomputable def order4_2_equiv : PCGroup smallGroup_4_2 ≃* ElemAbelianRep 2 :=
  mulEquivOfDecide (pcEval [sg4_2_L1, sg4_2_L2]
    [(Multiplicative.ofAdd 1, Multiplicative.ofAdd 0),
      (Multiplicative.ofAdd 0, Multiplicative.ofAdd 1)])

end Smallgroups.GAP
