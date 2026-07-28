/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order14
import Smallgroups.Classifications.Classifications_11_to_20.Order14

/-!
# Verification: order `14` — GAP pc groups match the existing representatives

`SmallGroup(14, 1) = DihedralGroup 7` and `SmallGroup(14, 2) = ℤ/14`.
This reverses the project's existing cyclic/dihedral representative order.
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The finite homomorphism and bijectivity checks need larger reduction limits.
/-- `SmallGroup(14, 1) = DihedralGroup 7`, mapping the order-two generator
to a reflection and the order-`7` generator to a rotation. -/
noncomputable def order14_1_equiv :
    PCGroup smallGroup_14_1 ≃* DihedralGroup 7 :=
  mulEquivOfDecide
    (pcEval [sg14_1_L1, sg14_1_L2]
      [DihedralGroup.sr 0, DihedralGroup.r 1])

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The finite homomorphism and bijectivity checks need larger reduction limits.
/-- `SmallGroup(14, 2) = ℤ/14`, mapping the order-two generator to `7` and
the order-`7` generator to `2`. -/
noncomputable def order14_2_equiv :
    PCGroup smallGroup_14_2 ≃* CyclicRep 14 :=
  mulEquivOfDecide
    (pcEval [sg14_2_L1, sg14_2_L2]
      [Multiplicative.ofAdd 7, Multiplicative.ofAdd 2])

end Smallgroups.GAP
