/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order39
import Smallgroups.Classifications.Classifications_31_to_40.Order39

/-!
# Verification: order `39` — GAP pc groups match the existing representatives

`SmallGroup(39, 1)` is nonabelian and `SmallGroup(39, 2)` is cyclic.
Noncommutativity of the first pc group is checked on its two generators; the existing
complete classification supplies its isomorphism to the project's noncomputably
chosen semidirect-product representative.
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

/-- The first GAP group of order `39` is noncommutative. -/
theorem order39_1_not_comm :
    ¬ ∀ a b : PCGroup smallGroup_39_1, a * b = b * a := by
  intro h
  have hne :
      (pcGens [sg39_1_L1, sg39_1_L2])[0] *
          (pcGens [sg39_1_L1, sg39_1_L2])[1] ≠
        (pcGens [sg39_1_L1, sg39_1_L2])[1] *
          (pcGens [sg39_1_L1, sg39_1_L2])[0] := by decide
  exact hne (h _ _)

/-- `SmallGroup(39, 1)` is the nonabelian representative from the existing
order-`39` classification. -/
noncomputable def order39_1_equiv :
    PCGroup smallGroup_39_1 ≃*
      Smallgroups.Classifications.Order39.NonabRep39 :=
  Classical.choice (by
    rcases Smallgroups.Classifications.Order39.classification
        card_smallGroup_39_1 with hcyc | hnonab
    · exfalso
      apply order39_1_not_comm
      intro a b
      apply hcyc.some.injective
      simpa only [map_mul] using mul_comm (hcyc.some a) (hcyc.some b)
    · exact hnonab)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The finite homomorphism and bijectivity checks need larger reduction limits.
/-- `SmallGroup(39, 2) = ℤ/39`, mapping the order-`3` generator to `13`
and the order-`13` generator to `3`. -/
noncomputable def order39_2_equiv :
    PCGroup smallGroup_39_2 ≃* CyclicRep 39 :=
  mulEquivOfDecide
    (pcEval [sg39_2_L1, sg39_2_L2]
      [Multiplicative.ofAdd 13, Multiplicative.ofAdd 3])

end Smallgroups.GAP
