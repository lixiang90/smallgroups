/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order34
import Smallgroups.Classifications.Classifications_31_to_40.Order34

/-!
# Verification: order `34` — GAP pc groups match the existing representatives

`SmallGroup(34, 1) = DihedralGroup 17` and `SmallGroup(34, 2) = ℤ/34`.
This reverses the project's existing cyclic/dihedral representative order.
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The finite homomorphism and bijectivity checks need larger reduction limits.
/-- `SmallGroup(34, 1) = DihedralGroup 17`, mapping the order-two generator
to a reflection and the order-`17` generator to a rotation. -/
noncomputable def order34_1_equiv :
    PCGroup smallGroup_34_1 ≃* DihedralGroup 17 :=
  mulEquivOfDecide
    (pcEval [sg34_1_L1, sg34_1_L2]
      [DihedralGroup.sr 0, DihedralGroup.r 1])

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The finite homomorphism and bijectivity checks need larger reduction limits.
/-- `SmallGroup(34, 2) = ℤ/34`, mapping the order-two generator to `17` and
the order-`17` generator to `2`. -/
noncomputable def order34_2_equiv :
    PCGroup smallGroup_34_2 ≃* CyclicRep 34 :=
  mulEquivOfDecide
    (pcEval [sg34_2_L1, sg34_2_L2]
      [Multiplicative.ofAdd 17, Multiplicative.ofAdd 2])

end Smallgroups.GAP
