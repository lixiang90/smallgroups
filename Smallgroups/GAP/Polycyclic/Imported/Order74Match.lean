/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order74
import Smallgroups.Classifications.Classifications_71_to_80.Order74

/-!
# Verification: order `74` — GAP pc groups match the existing representatives

`SmallGroup(74, 1) = DihedralGroup 37` and `SmallGroup(74, 2) = ℤ/74`.
This reverses the project's existing cyclic/dihedral representative order.
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The finite homomorphism and bijectivity checks need larger reduction limits.
/-- `SmallGroup(74, 1) = DihedralGroup 37`, mapping the order-two generator
to a reflection and the order-`37` generator to a rotation. -/
noncomputable def order74_1_equiv :
    PCGroup smallGroup_74_1 ≃* DihedralGroup 37 :=
  mulEquivOfDecide
    (pcEval [sg74_1_L1, sg74_1_L2]
      [DihedralGroup.sr 0, DihedralGroup.r 1])

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The finite homomorphism and bijectivity checks need larger reduction limits.
/-- `SmallGroup(74, 2) = ℤ/74`, mapping the order-two generator to `37` and
the order-`37` generator to `2`. -/
noncomputable def order74_2_equiv :
    PCGroup smallGroup_74_2 ≃* CyclicRep 74 :=
  mulEquivOfDecide
    (pcEval [sg74_2_L1, sg74_2_L2]
      [Multiplicative.ofAdd 37, Multiplicative.ofAdd 2])

end Smallgroups.GAP
