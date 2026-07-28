/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order15
import Smallgroups.Classifications.Classifications_11_to_20.Order15

/-!
# Verification: order `15` — GAP pc groups match the existing representatives

The unique group `SmallGroup(15, 1)` is cyclic.  Its isomorphism
to the existing representative is certified by an explicit pc-generator map.
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The finite homomorphism and bijectivity checks need larger reduction limits.
/-- `SmallGroup(15, 1) = ℤ/15`, mapping the order-`3` generator to `5`
and the order-`5` generator to `3`. -/
noncomputable def order15_1_equiv :
    PCGroup smallGroup_15_1 ≃* CyclicRep 15 :=
  mulEquivOfDecide
    (pcEval [sg15_1_L1, sg15_1_L2]
      [Multiplicative.ofAdd 5, Multiplicative.ofAdd 3])

end Smallgroups.GAP
