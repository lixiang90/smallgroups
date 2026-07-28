/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order91
import Smallgroups.Classifications.Classifications_91_to_100.Order91

/-!
# Verification: order `91` — GAP pc groups match the existing representatives

The unique group `SmallGroup(91, 1)` is cyclic.  Its isomorphism
to the existing representative is certified by an explicit pc-generator map.
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The finite homomorphism and bijectivity checks need larger reduction limits.
/-- `SmallGroup(91, 1) = ℤ/91`, mapping the order-`7` generator to `13`
and the order-`13` generator to `7`. -/
noncomputable def order91_1_equiv :
    PCGroup smallGroup_91_1 ≃* CyclicRep 91 :=
  mulEquivOfDecide
    (pcEval [sg91_1_L1, sg91_1_L2]
      [Multiplicative.ofAdd 13, Multiplicative.ofAdd 7])

end Smallgroups.GAP
