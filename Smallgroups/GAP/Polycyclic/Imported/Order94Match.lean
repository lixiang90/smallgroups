/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order94
import Smallgroups.Classifications.Classifications_91_to_100.Order94

/-!
# Verification: order `94` — GAP pc groups match the existing representatives

`SmallGroup(94, 1) = DihedralGroup 47` and `SmallGroup(94, 2) = ℤ/94`.
This reverses the project's existing cyclic/dihedral representative order.
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- `SmallGroup(94, 1) = DihedralGroup 47`, mapping the order-two generator
to a reflection and the order-`47` generator to a rotation. -/
noncomputable def order94_1_equiv :
    PCGroup smallGroup_94_1 ≃* DihedralGroup 47 :=
  mulEquivOfDecide
    (pcEval [sg94_1_L1, sg94_1_L2]
      [DihedralGroup.sr 0, DihedralGroup.r 1])

/-- `SmallGroup(94, 2) = ℤ/94`, mapping the order-two generator to `47` and
the order-`47` generator to `2`. -/
noncomputable def order94_2_equiv :
    PCGroup smallGroup_94_2 ≃* CyclicRep 94 :=
  mulEquivOfDecide
    (pcEval [sg94_2_L1, sg94_2_L2]
      [Multiplicative.ofAdd 47, Multiplicative.ofAdd 2])

end Smallgroups.GAP
