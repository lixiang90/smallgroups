/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order82
import Smallgroups.Classifications.Classifications_81_to_90.Order82

/-!
# Verification: order `82` — GAP pc groups match the existing representatives

`SmallGroup(82, 1) = DihedralGroup 41` and `SmallGroup(82, 2) = ℤ/82`.
This reverses the project's existing cyclic/dihedral representative order.
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The finite homomorphism and bijectivity checks need larger reduction limits.
/-- `SmallGroup(82, 1) = DihedralGroup 41`, mapping the order-two generator
to a reflection and the order-`41` generator to a rotation. -/
noncomputable def order82_1_equiv :
    PCGroup smallGroup_82_1 ≃* DihedralGroup 41 :=
  mulEquivOfDecide
    (pcEval [sg82_1_L1, sg82_1_L2]
      [DihedralGroup.sr 0, DihedralGroup.r 1])

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The finite homomorphism and bijectivity checks need larger reduction limits.
/-- `SmallGroup(82, 2) = ℤ/82`, mapping the order-two generator to `41` and
the order-`41` generator to `2`. -/
noncomputable def order82_2_equiv :
    PCGroup smallGroup_82_2 ≃* CyclicRep 82 :=
  mulEquivOfDecide
    (pcEval [sg82_2_L1, sg82_2_L2]
      [Multiplicative.ofAdd 41, Multiplicative.ofAdd 2])

end Smallgroups.GAP
