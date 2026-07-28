/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order86
import Smallgroups.Classifications.Classifications_81_to_90.Order86

/-!
# Verification: order `86` — GAP pc groups match the existing representatives

`SmallGroup(86, 1) = DihedralGroup 43` and `SmallGroup(86, 2) = ℤ/86`.
This reverses the project's existing cyclic/dihedral representative order.
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- `SmallGroup(86, 1) = DihedralGroup 43`, mapping the order-two generator
to a reflection and the order-`43` generator to a rotation. -/
noncomputable def order86_1_equiv :
    PCGroup smallGroup_86_1 ≃* DihedralGroup 43 :=
  mulEquivOfDecide
    (pcEval [sg86_1_L1, sg86_1_L2]
      [DihedralGroup.sr 0, DihedralGroup.r 1])

/-- `SmallGroup(86, 2) = ℤ/86`, mapping the order-two generator to `43` and
the order-`43` generator to `2`. -/
noncomputable def order86_2_equiv :
    PCGroup smallGroup_86_2 ≃* CyclicRep 86 :=
  mulEquivOfDecide
    (pcEval [sg86_2_L1, sg86_2_L2]
      [Multiplicative.ofAdd 43, Multiplicative.ofAdd 2])

end Smallgroups.GAP
