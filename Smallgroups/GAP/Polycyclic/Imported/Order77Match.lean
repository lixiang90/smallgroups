/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order77
import Smallgroups.Classifications.Classifications_71_to_80.Order77

/-!
# Verification: order `77` — GAP pc groups match the existing representatives

The unique group `SmallGroup(77, 1)` is cyclic.  Its isomorphism
to the existing representative is certified by an explicit pc-generator map.
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The finite homomorphism and bijectivity checks need larger reduction limits.
/-- `SmallGroup(77, 1) = ℤ/77`, mapping the order-`7` generator to `11`
and the order-`11` generator to `7`. -/
noncomputable def order77_1_equiv :
    PCGroup smallGroup_77_1 ≃* CyclicRep 77 :=
  mulEquivOfDecide
    (pcEval [sg77_1_L1, sg77_1_L2]
      [Multiplicative.ofAdd 11, Multiplicative.ofAdd 7])

end Smallgroups.GAP
