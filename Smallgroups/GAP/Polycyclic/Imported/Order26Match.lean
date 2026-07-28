/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order26
import Smallgroups.Classifications.Classifications_21_to_30.Order26

/-!
# Verification: order `26` — GAP pc groups match the existing representatives

`SmallGroup(26, 1) = DihedralGroup 13` and `SmallGroup(26, 2) = ℤ/26`.
This reverses the project's existing cyclic/dihedral representative order.
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The finite homomorphism and bijectivity checks need larger reduction limits.
/-- `SmallGroup(26, 1) = DihedralGroup 13`, mapping the order-two generator
to a reflection and the order-`13` generator to a rotation. -/
noncomputable def order26_1_equiv :
    PCGroup smallGroup_26_1 ≃* DihedralGroup 13 :=
  mulEquivOfDecide
    (pcEval [sg26_1_L1, sg26_1_L2]
      [DihedralGroup.sr 0, DihedralGroup.r 1])

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The finite homomorphism and bijectivity checks need larger reduction limits.
/-- `SmallGroup(26, 2) = ℤ/26`, mapping the order-two generator to `13` and
the order-`13` generator to `2`. -/
noncomputable def order26_2_equiv :
    PCGroup smallGroup_26_2 ≃* CyclicRep 26 :=
  mulEquivOfDecide
    (pcEval [sg26_2_L1, sg26_2_L2]
      [Multiplicative.ofAdd 13, Multiplicative.ofAdd 2])

end Smallgroups.GAP
