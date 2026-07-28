/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order35
import Smallgroups.Classifications.Classifications_31_to_40.Order35

/-!
# Verification: order `35` — GAP pc groups match the existing representatives

The unique group `SmallGroup(35, 1)` is cyclic.  Its isomorphism
to the existing representative is certified by an explicit pc-generator map.
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The finite homomorphism and bijectivity checks need larger reduction limits.
/-- `SmallGroup(35, 1) = ℤ/35`, mapping the order-`5` generator to `7`
and the order-`7` generator to `5`. -/
noncomputable def order35_1_equiv :
    PCGroup smallGroup_35_1 ≃* CyclicRep 35 :=
  mulEquivOfDecide
    (pcEval [sg35_1_L1, sg35_1_L2]
      [Multiplicative.ofAdd 7, Multiplicative.ofAdd 5])

end Smallgroups.GAP
