/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeActionOrbits
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeRNKernelTypes

/-!
# Interfaces from Wild action orbits to cocycle exhaustiveness

The RM and RN reductions expose a transported action
`C3 -> Aut(P)` on a Wild order-`16` kernel. The remaining finite calculations
are stated here as action-classifier predicates. The bridge theorems below
show that proving those predicates is exactly sufficient for the corresponding
`Order48FourCocycleExhaustive` statement.

The action produced by the RM/RN reductions is not arbitrary: its semidirect
product is still in the four-Sylow-`3` branch. We express this compatibility
intrinsically by requiring four Sylow-`3` subgroups. This avoids including the
trivial action, whose semidirect product has a unique Sylow `3`-subgroup.
-/

namespace Smallgroups.UsefulTheorems

def Order48RMWildActionComplete : Prop :=
  ∀ (i : Fin 14),
    (i = 0 ∨ i = 7 ∨ i = 8 ∨ i = 10 ∨ i = 11) →
    ∀ phi : Multiplicative (ZMod 3) →* MulAut (order16_wild_reps i),
      Nat.card {x : SemidirectProduct (order16_wild_reps i)
        (Multiplicative (ZMod 3)) phi // x ^ 3 = 1} = 9 →
      ∃ j : Fin 8,
        Nonempty (SemidirectProduct (order16_wild_reps i)
          (Multiplicative (ZMod 3)) phi ≃*
          order48_four_residualKnownReps j)

def Order48RNWildActionComplete : Prop :=
  ∀ (i : Fin 14),
    (i = 11 ∨ i = 12) →
    ∀ phi : Multiplicative (ZMod 3) →* MulAut (order16_wild_reps i),
      Nat.card {x : SemidirectProduct (order16_wild_reps i)
        (Multiplicative (ZMod 3)) phi // x ^ 3 = 1} = 9 →
      ∃ j : Fin 8,
        Nonempty (SemidirectProduct (order16_wild_reps i)
          (Multiplicative (ZMod 3)) phi ≃*
          order48_four_residualKnownReps j)

/-- The residual action problem restricted to one fixed Wild kernel.  Keeping
these predicates separate lets the five RM kernel calculations live in small,
independently compiled modules. -/
def Order48WildKernelActionComplete (i : Fin 14) : Prop :=
  ∀ phi : Multiplicative (ZMod 3) →* MulAut (order16_wild_reps i),
    Nat.card {x : SemidirectProduct (order16_wild_reps i)
      (Multiplicative (ZMod 3)) phi // x ^ 3 = 1} = 9 →
    ∃ j : Fin 8,
      Nonempty (SemidirectProduct (order16_wild_reps i)
        (Multiplicative (ZMod 3)) phi ≃*
        order48_four_residualKnownReps j)

/-- Assemble the five square-image-compatible RM kernel classifiers. -/
theorem order48_RM_wild_action_complete_of_kernel_cases
    (h0 : Order48WildKernelActionComplete 0)
    (h7 : Order48WildKernelActionComplete 7)
    (h8 : Order48WildKernelActionComplete 8)
    (h10 : Order48WildKernelActionComplete 10)
    (h11 : Order48WildKernelActionComplete 11) :
    Order48RMWildActionComplete := by
  intro i hi φ hRoots
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · exact h0 φ hRoots
  · exact h7 φ hRoots
  · exact h8 φ hRoots
  · exact h10 φ hRoots
  · exact h11 φ hRoots

/-- Assemble the two central-double-cover kernel classifiers in the RN branch. -/
theorem order48_RN_wild_action_complete_of_kernel_cases
    (h11 : Order48WildKernelActionComplete 11)
    (h12 : Order48WildKernelActionComplete 12) :
    Order48RNWildActionComplete := by
  intro i hi φ hRoots
  rcases hi with rfl | rfl
  · exact h11 φ hRoots
  · exact h12 φ hRoots

theorem order48_RM_cocycle_exhaustive_of_wild_action_complete
    (hOrbit : Order48RMWildActionComplete) :
    Order48FourCocycleExhaustive order24_RM := by
  intro f hf
  obtain ⟨i, K, eP, eK, hi, _, _, _, eG⟩ :=
    order48_RM_cocycle_reduction_to_wild_action f hf
  have hSylC : Nat.card (Sylow 3 (CocycleGroup f hf)) = 4 :=
    (order48_RM_cocycle_card_and_sylow_three f hf).2
  have hSylA : Nat.card (Sylow 3
      (SemidirectProduct (order16_wild_reps i)
        (Multiplicative (ZMod 3)) (order48_RM_wildAction f hf i eP K eK))) = 4 := by
    rw [← hSylC]
    exact (order48_card_sylow_of_mulEquiv 3 eG.some).symm
  letI : Finite (order16_wild_reps i) := Nat.finite_of_card_ne_zero (by
    rw [card_order16_wild_reps i]
    norm_num)
  have hRootsA := (order48_c3_action_card_sylow_three_eq_four_iff
    (card_order16_wild_reps i)
    (order48_RM_wildAction f hf i eP K eK)).mp hSylA
  obtain ⟨j, eA⟩ := hOrbit i hi
    (order48_RM_wildAction f hf i eP K eK) hRootsA
  exact ⟨j, ⟨eG.some.trans eA.some⟩⟩

theorem order48_RN_cocycle_exhaustive_of_wild_action_complete
    (hOrbit : Order48RNWildActionComplete) :
    Order48FourCocycleExhaustive order24_RN := by
  intro f hf
  obtain ⟨i, K, eP, eK, _, _, _, eG⟩ :=
    order48_RN_cocycle_reduction_to_wild_action f hf
  have hSylC : Nat.card (Sylow 3 (CocycleGroup f hf)) = 4 :=
    (order48_RN_cocycle_card_and_sylow_three f hf).2
  have hSylA : Nat.card (Sylow 3
      (SemidirectProduct (order16_wild_reps i)
        (Multiplicative (ZMod 3)) (order48_RN_wildAction f hf i eP K eK))) = 4 := by
    rw [← hSylC]
    exact (order48_card_sylow_of_mulEquiv 3 eG.some).symm
  letI : Finite (order16_wild_reps i) := Nat.finite_of_card_ne_zero (by
    rw [card_order16_wild_reps i]
    norm_num)
  have hRootsA := (order48_c3_action_card_sylow_three_eq_four_iff
    (card_order16_wild_reps i)
    (order48_RN_wildAction f hf i eP K eK)).mp hSylA
  have hi := order48_RN_cocycle_kernel_index_restriction f hf i eP
  obtain ⟨j, eA⟩ := hOrbit i hi
    (order48_RN_wildAction f hf i eP K eK) hRootsA
  exact ⟨j, ⟨eG.some.trans eA.some⟩⟩

end Smallgroups.UsefulTheorems
