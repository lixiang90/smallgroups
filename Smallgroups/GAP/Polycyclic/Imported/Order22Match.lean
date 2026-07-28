/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order22
import Smallgroups.Classifications.Classifications_21_to_30.Order22

/-!
# Verification: order `22` — GAP pc groups match the existing representatives

`SmallGroup(22, 1) = DihedralGroup 11` and `SmallGroup(22, 2) = ℤ/22`.
This reverses the project's existing cyclic/dihedral representative order.
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- `SmallGroup(22, 1) = DihedralGroup 11`, mapping the order-two generator
to a reflection and the order-`11` generator to a rotation. -/
noncomputable def order22_1_equiv :
    PCGroup smallGroup_22_1 ≃* DihedralGroup 11 :=
  mulEquivOfDecide
    (pcEval [sg22_1_L1, sg22_1_L2]
      [DihedralGroup.sr 0, DihedralGroup.r 1])

/-- `SmallGroup(22, 2) = ℤ/22`, mapping the order-two generator to `11` and
the order-`11` generator to `2`. -/
noncomputable def order22_2_equiv :
    PCGroup smallGroup_22_2 ≃* CyclicRep 22 :=
  mulEquivOfDecide
    (pcEval [sg22_2_L1, sg22_2_L2]
      [Multiplicative.ofAdd 11, Multiplicative.ofAdd 2])

end Smallgroups.GAP
