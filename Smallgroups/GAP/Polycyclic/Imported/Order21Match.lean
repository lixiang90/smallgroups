/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order21
import Smallgroups.Classifications.Classifications_21_to_30.Order21

/-!
# Verification: order `21` — GAP pc groups match the existing representatives

`SmallGroup(21, 1)` is nonabelian and `SmallGroup(21, 2)` is cyclic.
Noncommutativity of the first pc group is checked on its two generators; the existing
complete classification supplies its isomorphism to the project's noncomputably
chosen semidirect-product representative.
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- The first GAP group of order `21` is noncommutative. -/
theorem order21_1_not_comm :
    ¬ ∀ a b : PCGroup smallGroup_21_1, a * b = b * a := by
  intro h
  have hne :
      (pcGens [sg21_1_L1, sg21_1_L2])[0] *
          (pcGens [sg21_1_L1, sg21_1_L2])[1] ≠
        (pcGens [sg21_1_L1, sg21_1_L2])[1] *
          (pcGens [sg21_1_L1, sg21_1_L2])[0] := by decide
  exact hne (h _ _)

/-- `SmallGroup(21, 1)` is the nonabelian representative from the existing
order-`21` classification. -/
noncomputable def order21_1_equiv :
    PCGroup smallGroup_21_1 ≃*
      Smallgroups.Classifications.Order21.NonabRep21 :=
  Classical.choice (by
    rcases Smallgroups.Classifications.Order21.classification
        card_smallGroup_21_1 with hcyc | hnonab
    · exfalso
      apply order21_1_not_comm
      intro a b
      apply hcyc.some.injective
      simpa only [map_mul] using mul_comm (hcyc.some a) (hcyc.some b)
    · exact hnonab)

/-- `SmallGroup(21, 2) = ℤ/21`, mapping the order-`3` generator to `7`
and the order-`7` generator to `3`. -/
noncomputable def order21_2_equiv :
    PCGroup smallGroup_21_2 ≃* CyclicRep 21 :=
  mulEquivOfDecide
    (pcEval [sg21_2_L1, sg21_2_L2]
      [Multiplicative.ofAdd 7, Multiplicative.ofAdd 3])

end Smallgroups.GAP
