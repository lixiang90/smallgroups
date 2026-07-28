/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order46
import Smallgroups.Classifications.Classifications_41_to_50.Order46

/-!
# Verification: order `46` — GAP pc groups match the existing representatives

`SmallGroup(46, 1) = DihedralGroup 23` and `SmallGroup(46, 2) = ℤ/46`.
This reverses the project's existing cyclic/dihedral representative order.
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The finite homomorphism and bijectivity checks need larger reduction limits.
/-- `SmallGroup(46, 1) = DihedralGroup 23`, mapping the order-two generator
to a reflection and the order-`23` generator to a rotation. -/
noncomputable def order46_1_equiv :
    PCGroup smallGroup_46_1 ≃* DihedralGroup 23 :=
  mulEquivOfDecide
    (pcEval [sg46_1_L1, sg46_1_L2]
      [DihedralGroup.sr 0, DihedralGroup.r 1])

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The finite homomorphism and bijectivity checks need larger reduction limits.
/-- `SmallGroup(46, 2) = ℤ/46`, mapping the order-two generator to `23` and
the order-`23` generator to `2`. -/
noncomputable def order46_2_equiv :
    PCGroup smallGroup_46_2 ≃* CyclicRep 46 :=
  mulEquivOfDecide
    (pcEval [sg46_2_L1, sg46_2_L2]
      [Multiplicative.ofAdd 23, Multiplicative.ofAdd 2])

end Smallgroups.GAP
