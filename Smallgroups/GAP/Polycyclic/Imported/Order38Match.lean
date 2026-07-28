/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order38
import Smallgroups.Classifications.Classifications_31_to_40.Order38

/-!
# Verification: order `38` — GAP pc groups match the existing representatives

`SmallGroup(38, 1) = DihedralGroup 19` and `SmallGroup(38, 2) = ℤ/38`.
This reverses the project's existing cyclic/dihedral representative order.
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- `SmallGroup(38, 1) = DihedralGroup 19`, mapping the order-two generator
to a reflection and the order-`19` generator to a rotation. -/
noncomputable def order38_1_equiv :
    PCGroup smallGroup_38_1 ≃* DihedralGroup 19 :=
  mulEquivOfDecide
    (pcEval [sg38_1_L1, sg38_1_L2]
      [DihedralGroup.sr 0, DihedralGroup.r 1])

/-- `SmallGroup(38, 2) = ℤ/38`, mapping the order-two generator to `19` and
the order-`19` generator to `2`. -/
noncomputable def order38_2_equiv :
    PCGroup smallGroup_38_2 ≃* CyclicRep 38 :=
  mulEquivOfDecide
    (pcEval [sg38_2_L1, sg38_2_L2]
      [Multiplicative.ofAdd 19, Multiplicative.ofAdd 2])

end Smallgroups.GAP
