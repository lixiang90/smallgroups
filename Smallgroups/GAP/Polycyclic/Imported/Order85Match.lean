/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order85
import Smallgroups.Classifications.Classifications_81_to_90.Order85

/-!
# Verification: order `85` — GAP pc groups match the existing representatives

The unique group `SmallGroup(85, 1)` is cyclic.  Its isomorphism
to the existing representative is certified by an explicit pc-generator map.
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The finite homomorphism and bijectivity checks need larger reduction limits.
/-- `SmallGroup(85, 1) = ℤ/85`, mapping the order-`5` generator to `17`
and the order-`17` generator to `5`. -/
noncomputable def order85_1_equiv :
    PCGroup smallGroup_85_1 ≃* CyclicRep 85 :=
  mulEquivOfDecide
    (pcEval [sg85_1_L1, sg85_1_L2]
      [Multiplicative.ofAdd 17, Multiplicative.ofAdd 5])

end Smallgroups.GAP
