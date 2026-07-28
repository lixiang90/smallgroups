/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order33
import Smallgroups.Classifications.Classifications_31_to_40.Order33

/-!
# Verification: order `33` — GAP pc groups match the existing representatives

The unique group `SmallGroup(33, 1)` is cyclic.  Its isomorphism
to the existing representative is certified by an explicit pc-generator map.
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The finite homomorphism and bijectivity checks need larger reduction limits.
/-- `SmallGroup(33, 1) = ℤ/33`, mapping the order-`3` generator to `11`
and the order-`11` generator to `3`. -/
noncomputable def order33_1_equiv :
    PCGroup smallGroup_33_1 ≃* CyclicRep 33 :=
  mulEquivOfDecide
    (pcEval [sg33_1_L1, sg33_1_L2]
      [Multiplicative.ofAdd 11, Multiplicative.ofAdd 3])

end Smallgroups.GAP
