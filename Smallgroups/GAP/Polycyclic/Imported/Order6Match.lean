/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order6
import Smallgroups.Classifications.Classifications_1_to_10.Order6

/-!
# Verification: order `6` — the imported pc groups match the existing representatives

The two groups of order `6` in the GAP SmallGroups library are

* `SmallGroup(6, 1) = DihedralGroup 3`;
* `SmallGroup(6, 2) = ℤ/6`.

This is the reverse of the project's existing representative-list order.  Each
isomorphism is certified by mapping the pc generators to explicit elements and
discharging homomorphism and bijectivity by `decide` (`mulEquivOfDecide`).
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

/-- `SmallGroup(6, 1) = DihedralGroup 3`, mapping the order-two generator to a
reflection and the order-three generator to a rotation. -/
noncomputable def order6_1_equiv :
    PCGroup smallGroup_6_1 ≃* DihedralGroup 3 :=
  mulEquivOfDecide
    (pcEval [sg6_1_L1, sg6_1_L2]
      [DihedralGroup.sr 0, DihedralGroup.r 1])

/-- `SmallGroup(6, 2) = ℤ/6`, mapping the order-two generator to `3` and the
order-three generator to `2`. -/
noncomputable def order6_2_equiv :
    PCGroup smallGroup_6_2 ≃* CyclicRep 6 :=
  mulEquivOfDecide
    (pcEval [sg6_2_L1, sg6_2_L2]
      [Multiplicative.ofAdd 3, Multiplicative.ofAdd 2])

end Smallgroups.GAP
