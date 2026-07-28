/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order93
import Smallgroups.Classifications.Classifications_91_to_100.Order93

/-!
# Verification: order `93` — GAP pc groups match the existing representatives

`SmallGroup(93, 1)` is nonabelian and `SmallGroup(93, 2)` is cyclic.
Noncommutativity of the first pc group is checked on its two generators; the existing
complete classification supplies its isomorphism to the project's noncomputably
chosen semidirect-product representative.
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

/-- The first GAP group of order `93` is noncommutative. -/
theorem order93_1_not_comm :
    ¬ ∀ a b : PCGroup smallGroup_93_1, a * b = b * a := by
  intro h
  have hne :
      (pcGens [sg93_1_L1, sg93_1_L2])[0] *
          (pcGens [sg93_1_L1, sg93_1_L2])[1] ≠
        (pcGens [sg93_1_L1, sg93_1_L2])[1] *
          (pcGens [sg93_1_L1, sg93_1_L2])[0] := by decide
  exact hne (h _ _)

/-- `SmallGroup(93, 1)` is the nonabelian representative from the existing
order-`93` classification. -/
noncomputable def order93_1_equiv :
    PCGroup smallGroup_93_1 ≃*
      Smallgroups.Classifications.Order93.NonabRep93 :=
  Classical.choice (by
    rcases Smallgroups.Classifications.Order93.classification
        card_smallGroup_93_1 with hcyc | hnonab
    · exfalso
      apply order93_1_not_comm
      intro a b
      apply hcyc.some.injective
      simpa only [map_mul] using mul_comm (hcyc.some a) (hcyc.some b)
    · exact hnonab)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The finite homomorphism and bijectivity checks need larger reduction limits.
/-- `SmallGroup(93, 2) = ℤ/93`, mapping the order-`3` generator to `31`
and the order-`31` generator to `3`. -/
noncomputable def order93_2_equiv :
    PCGroup smallGroup_93_2 ≃* CyclicRep 93 :=
  mulEquivOfDecide
    (pcEval [sg93_2_L1, sg93_2_L2]
      [Multiplicative.ofAdd 31, Multiplicative.ofAdd 3])

end Smallgroups.GAP
