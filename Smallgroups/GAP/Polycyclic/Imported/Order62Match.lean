/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order62
import Smallgroups.Classifications.Classifications_61_to_70.Order62

/-!
# Verification: order `62` — GAP pc groups match the existing representatives

`SmallGroup(62, 1) = DihedralGroup 31` and `SmallGroup(62, 2) = ℤ/62`.
This reverses the project's existing cyclic/dihedral representative order.
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The finite homomorphism and bijectivity checks need larger reduction limits.
/-- `SmallGroup(62, 1) = DihedralGroup 31`, mapping the order-two generator
to a reflection and the order-`31` generator to a rotation. -/
noncomputable def order62_1_equiv :
    PCGroup smallGroup_62_1 ≃* DihedralGroup 31 :=
  mulEquivOfDecide
    (pcEval [sg62_1_L1, sg62_1_L2]
      [DihedralGroup.sr 0, DihedralGroup.r 1])

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The finite homomorphism and bijectivity checks need larger reduction limits.
/-- `SmallGroup(62, 2) = ℤ/62`, mapping the order-two generator to `31` and
the order-`31` generator to `2`. -/
noncomputable def order62_2_equiv :
    PCGroup smallGroup_62_2 ≃* CyclicRep 62 :=
  mulEquivOfDecide
    (pcEval [sg62_2_L1, sg62_2_L2]
      [Multiplicative.ofAdd 31, Multiplicative.ofAdd 2])

end Smallgroups.GAP
