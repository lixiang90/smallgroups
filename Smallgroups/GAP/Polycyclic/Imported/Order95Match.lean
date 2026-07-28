/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order95
import Smallgroups.Classifications.Classifications_91_to_100.Order95

/-!
# Verification: order `95` — GAP pc groups match the existing representatives

The unique group `SmallGroup(95, 1)` is cyclic.  Its isomorphism
to the existing representative is certified by an explicit pc-generator map.
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The finite homomorphism and bijectivity checks need larger reduction limits.
/-- `SmallGroup(95, 1) = ℤ/95`, mapping the order-`5` generator to `19`
and the order-`19` generator to `5`. -/
noncomputable def order95_1_equiv :
    PCGroup smallGroup_95_1 ≃* CyclicRep 95 :=
  mulEquivOfDecide
    (pcEval [sg95_1_L1, sg95_1_L2]
      [Multiplicative.ofAdd 19, Multiplicative.ofAdd 5])

end Smallgroups.GAP
