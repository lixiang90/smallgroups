/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order55
import Smallgroups.Classifications.Classifications_51_to_60.Order55

/-!
# Verification: order `55` — GAP pc groups match the existing representatives

`SmallGroup(55, 1)` is nonabelian and `SmallGroup(55, 2)` is cyclic.
Noncommutativity of the first pc group is checked on its two generators; the existing
complete classification supplies its isomorphism to the project's noncomputably
chosen semidirect-product representative.
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- The first GAP group of order `55` is noncommutative. -/
theorem order55_1_not_comm :
    ¬ ∀ a b : PCGroup smallGroup_55_1, a * b = b * a := by
  intro h
  have hne :
      (pcGens [sg55_1_L1, sg55_1_L2])[0] *
          (pcGens [sg55_1_L1, sg55_1_L2])[1] ≠
        (pcGens [sg55_1_L1, sg55_1_L2])[1] *
          (pcGens [sg55_1_L1, sg55_1_L2])[0] := by decide
  exact hne (h _ _)

/-- `SmallGroup(55, 1)` is the nonabelian representative from the existing
order-`55` classification. -/
noncomputable def order55_1_equiv :
    PCGroup smallGroup_55_1 ≃*
      Smallgroups.Classifications.Order55.NonabRep55 :=
  Classical.choice (by
    rcases Smallgroups.Classifications.Order55.classification
        card_smallGroup_55_1 with hcyc | hnonab
    · exfalso
      apply order55_1_not_comm
      intro a b
      apply hcyc.some.injective
      simpa only [map_mul] using mul_comm (hcyc.some a) (hcyc.some b)
    · exact hnonab)

/-- `SmallGroup(55, 2) = ℤ/55`, mapping the order-`5` generator to `11`
and the order-`11` generator to `5`. -/
noncomputable def order55_2_equiv :
    PCGroup smallGroup_55_2 ≃* CyclicRep 55 :=
  mulEquivOfDecide
    (pcEval [sg55_2_L1, sg55_2_L2]
      [Multiplicative.ofAdd 11, Multiplicative.ofAdd 5])

end Smallgroups.GAP
