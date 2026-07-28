/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order10
import Smallgroups.Classifications.Classifications_1_to_10.Order10

/-!
# Verification: order `10` — the imported pc groups match the existing representatives

The two groups of order `10` in the GAP SmallGroups library are

* `SmallGroup(10, 1) = DihedralGroup 5`;
* `SmallGroup(10, 2) = ℤ/10`.

This is the reverse of the project's existing representative-list order.  Each
isomorphism is certified by mapping the pc generators to explicit elements and
discharging homomorphism and bijectivity by `decide` (`mulEquivOfDecide`).
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

/-- `SmallGroup(10, 1) = DihedralGroup 5`, mapping the order-two generator to a
reflection and the order-five generator to a rotation. -/
noncomputable def order10_1_equiv :
    PCGroup smallGroup_10_1 ≃* DihedralGroup 5 :=
  mulEquivOfDecide
    (pcEval [sg10_1_L1, sg10_1_L2]
      [DihedralGroup.sr 0, DihedralGroup.r 1])

/-- `SmallGroup(10, 2) = ℤ/10`, mapping the order-two generator to `5` and the
order-five generator to `2`. -/
noncomputable def order10_2_equiv :
    PCGroup smallGroup_10_2 ≃* CyclicRep 10 :=
  mulEquivOfDecide
    (pcEval [sg10_2_L1, sg10_2_L2]
      [Multiplicative.ofAdd 5, Multiplicative.ofAdd 2])

end Smallgroups.GAP
