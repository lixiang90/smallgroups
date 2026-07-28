/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order57
import Smallgroups.Classifications.Classifications_51_to_60.Order57

/-!
# Verification: order `57` — GAP pc groups match the existing representatives

`SmallGroup(57, 1)` is nonabelian and `SmallGroup(57, 2)` is cyclic.
Noncommutativity of the first pc group is checked on its two generators; the existing
complete classification supplies its isomorphism to the project's noncomputably
chosen semidirect-product representative.
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

/-- The first GAP group of order `57` is noncommutative. -/
theorem order57_1_not_comm :
    ¬ ∀ a b : PCGroup smallGroup_57_1, a * b = b * a := by
  intro h
  have hne :
      (pcGens [sg57_1_L1, sg57_1_L2])[0] *
          (pcGens [sg57_1_L1, sg57_1_L2])[1] ≠
        (pcGens [sg57_1_L1, sg57_1_L2])[1] *
          (pcGens [sg57_1_L1, sg57_1_L2])[0] := by decide
  exact hne (h _ _)

/-- `SmallGroup(57, 1)` is the nonabelian representative from the existing
order-`57` classification. -/
noncomputable def order57_1_equiv :
    PCGroup smallGroup_57_1 ≃*
      Smallgroups.Classifications.Order57.NonabRep57 :=
  Classical.choice (by
    rcases Smallgroups.Classifications.Order57.classification
        card_smallGroup_57_1 with hcyc | hnonab
    · exfalso
      apply order57_1_not_comm
      intro a b
      apply hcyc.some.injective
      simpa only [map_mul] using mul_comm (hcyc.some a) (hcyc.some b)
    · exact hnonab)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The finite homomorphism and bijectivity checks need larger reduction limits.
/-- `SmallGroup(57, 2) = ℤ/57`, mapping the order-`3` generator to `19`
and the order-`19` generator to `3`. -/
noncomputable def order57_2_equiv :
    PCGroup smallGroup_57_2 ≃* CyclicRep 57 :=
  mulEquivOfDecide
    (pcEval [sg57_2_L1, sg57_2_L2]
      [Multiplicative.ofAdd 19, Multiplicative.ofAdd 3])

end Smallgroups.GAP
