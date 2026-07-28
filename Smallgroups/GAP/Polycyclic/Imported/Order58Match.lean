/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order58
import Smallgroups.Classifications.Classifications_51_to_60.Order58

/-!
# Verification: order `58` — GAP pc groups match the existing representatives

`SmallGroup(58, 1) = DihedralGroup 29` and `SmallGroup(58, 2) = ℤ/58`.
This reverses the project's existing cyclic/dihedral representative order.
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- `SmallGroup(58, 1) = DihedralGroup 29`, mapping the order-two generator
to a reflection and the order-`29` generator to a rotation. -/
noncomputable def order58_1_equiv :
    PCGroup smallGroup_58_1 ≃* DihedralGroup 29 :=
  mulEquivOfDecide
    (pcEval [sg58_1_L1, sg58_1_L2]
      [DihedralGroup.sr 0, DihedralGroup.r 1])

/-- `SmallGroup(58, 2) = ℤ/58`, mapping the order-two generator to `29` and
the order-`29` generator to `2`. -/
noncomputable def order58_2_equiv :
    PCGroup smallGroup_58_2 ≃* CyclicRep 58 :=
  mulEquivOfDecide
    (pcEval [sg58_2_L1, sg58_2_L2]
      [Multiplicative.ofAdd 29, Multiplicative.ofAdd 2])

end Smallgroups.GAP
