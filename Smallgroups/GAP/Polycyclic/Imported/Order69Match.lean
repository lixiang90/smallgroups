/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order69
import Smallgroups.Classifications.Classifications_61_to_70.Order69

/-!
# Verification: order `69` — GAP pc groups match the existing representatives

The unique group `SmallGroup(69, 1)` is cyclic.  Its isomorphism
to the existing representative is certified by an explicit pc-generator map.
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- `SmallGroup(69, 1) = ℤ/69`, mapping the order-`3` generator to `23`
and the order-`23` generator to `3`. -/
noncomputable def order69_1_equiv :
    PCGroup smallGroup_69_1 ≃* CyclicRep 69 :=
  mulEquivOfDecide
    (pcEval [sg69_1_L1, sg69_1_L2]
      [Multiplicative.ofAdd 23, Multiplicative.ofAdd 3])

end Smallgroups.GAP
