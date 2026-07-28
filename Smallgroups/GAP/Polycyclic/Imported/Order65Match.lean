/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order65
import Smallgroups.Classifications.Classifications_61_to_70.Order65

/-!
# Verification: order `65` — GAP pc groups match the existing representatives

The unique group `SmallGroup(65, 1)` is cyclic.  Its isomorphism
to the existing representative is certified by an explicit pc-generator map.
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The finite homomorphism and bijectivity checks need larger reduction limits.
/-- `SmallGroup(65, 1) = ℤ/65`, mapping the order-`5` generator to `13`
and the order-`13` generator to `5`. -/
noncomputable def order65_1_equiv :
    PCGroup smallGroup_65_1 ≃* CyclicRep 65 :=
  mulEquivOfDecide
    (pcEval [sg65_1_L1, sg65_1_L2]
      [Multiplicative.ofAdd 13, Multiplicative.ofAdd 5])

end Smallgroups.GAP
