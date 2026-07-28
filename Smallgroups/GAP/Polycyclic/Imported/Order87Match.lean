/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order87
import Smallgroups.Classifications.Classifications_81_to_90.Order87

/-!
# Verification: order `87` — GAP pc groups match the existing representatives

The unique group `SmallGroup(87, 1)` is cyclic.  Its isomorphism
to the existing representative is certified by an explicit pc-generator map.
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The finite homomorphism and bijectivity checks need larger reduction limits.
/-- `SmallGroup(87, 1) = ℤ/87`, mapping the order-`3` generator to `29`
and the order-`29` generator to `3`. -/
noncomputable def order87_1_equiv :
    PCGroup smallGroup_87_1 ≃* CyclicRep 87 :=
  mulEquivOfDecide
    (pcEval [sg87_1_L1, sg87_1_L2]
      [Multiplicative.ofAdd 29, Multiplicative.ofAdd 3])

end Smallgroups.GAP
