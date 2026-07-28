/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order51
import Smallgroups.Classifications.Classifications_51_to_60.Order51

/-!
# Verification: order `51` — GAP pc groups match the existing representatives

The unique group `SmallGroup(51, 1)` is cyclic.  Its isomorphism
to the existing representative is certified by an explicit pc-generator map.
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The finite homomorphism and bijectivity checks need larger reduction limits.
/-- `SmallGroup(51, 1) = ℤ/51`, mapping the order-`3` generator to `17`
and the order-`17` generator to `3`. -/
noncomputable def order51_1_equiv :
    PCGroup smallGroup_51_1 ≃* CyclicRep 51 :=
  mulEquivOfDecide
    (pcEval [sg51_1_L1, sg51_1_L2]
      [Multiplicative.ofAdd 17, Multiplicative.ofAdd 3])

end Smallgroups.GAP
