/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeKernelTypes
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeCocycleBranch
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeActionCore

/-!
# The remaining RM reduction

The existing order-`48` action classifications concern actions of an order-`16`
group on `C₃` (the unique-Sylow-`3` branch).  The RM cocycle branch has the
opposite orientation: `C₃` acts on the normal order-`16` preimage.  This file
records the fully formal reduction to that missing action problem.
-/

namespace Smallgroups.UsefulTheorems

open SemidirectProduct

noncomputable def order48_RM_wildAction
    (f : order24_RM → order24_RM → ZMod 2) (hf : IsCentralCocycle f)
    (i : Fin 14) (eP :
      order48CocycleTwoPreimage order24_c3ActionC2C2C2 f hf ≃*
        order16_wild_reps i)
    (K : Subgroup (CocycleGroup f hf))
    (eK : K ≃* Multiplicative (ZMod 3)) :
    Multiplicative (ZMod 3) →* MulAut (order16_wild_reps i) :=
  (MulAut.congr eP).toMonoidHom.comp
    ((order48CocycleComplementAction order24_c3ActionC2C2C2 f hf K).comp
      eK.symm.toMonoidHom)

/-- Every RM cocycle group is a semidirect product with one of the five Wild
order-`16` kernels allowed by the square-image obstruction.  The action is
transported to the standard `C₃` and Wild kernel models, so the only remaining
part of the RM proof is classification of these transported actions. -/
theorem order48_RM_cocycle_reduction_to_wild_action
    (f : order24_RM → order24_RM → ZMod 2) (hf : IsCentralCocycle f) :
    ∃ (i : Fin 14) (K : Subgroup (CocycleGroup f hf))
      (eP : order48CocycleTwoPreimage order24_c3ActionC2C2C2 f hf ≃*
        order16_wild_reps i)
      (eK : K ≃* Multiplicative (ZMod 3)),
      (i = 0 ∨ i = 7 ∨ i = 8 ∨ i = 10 ∨ i = 11) ∧
      Nat.card K = 3 ∧
      (∀ k : K,
        order48CocycleComplementAction
          order24_c3ActionC2C2C2 f hf K k
            (order48CocycleTwoPreimageKernelGenerator
              order24_c3ActionC2C2C2 f hf) =
          order48CocycleTwoPreimageKernelGenerator
            order24_c3ActionC2C2C2 f hf) ∧
      (∀ k : K, ∀ p : order48CocycleTwoPreimage
          order24_c3ActionC2C2C2 f hf,
        order48CocycleTwoPreimageToN
            order24_c3ActionC2C2C2 f hf
          (order48CocycleComplementAction
            order24_c3ActionC2C2C2 f hf K k p) =
        order24_c3ActionC2C2C2
          (order48CocycleComplementToC3
            order24_c3ActionC2C2C2 f hf K k)
          (order48CocycleTwoPreimageToN
            order24_c3ActionC2C2C2 f hf p)) ∧
      Nonempty (CocycleGroup f hf ≃*
        SemidirectProduct (order16_wild_reps i)
          (Multiplicative (ZMod 3))
          (order48_RM_wildAction f hf i eP K eK)) := by
  obtain ⟨K, hK, hbij, hfix, eG⟩ :=
    order48_RM_cocycle_semidirect_reduction_fixed_kernel f hf
  obtain ⟨i, hi, ⟨eP⟩⟩ := order48_RM_cocycle_kernel_type_restriction f hf
  let eK : K ≃* Multiplicative (ZMod 3) :=
    MulEquiv.ofBijective
      (order48CocycleComplementToC3 order24_c3ActionC2C2C2 f hf K) hbij
  refine ⟨i, K, eP, eK, hi, hK, hfix, ?_, ?_⟩
  · intro k p
    exact order48_RM_CocycleComplementAction_toN f hf K k p
  · exact ⟨eG.some.trans (SemidirectProduct.congr' eP eK)⟩

/-- The transported RM action is nontrivial whenever its semidirect product
has four Sylow `3`-subgroups.  Thus the RM orbit table only has to classify
nonidentity order-three automorphisms of the five allowed Wild kernels. -/
theorem order48_RM_wildAction_generator_ne_one
    {f : order24_RM → order24_RM → ZMod 2} {hf : IsCentralCocycle f}
    {i : Fin 14}
    {eP : order48CocycleTwoPreimage order24_c3ActionC2C2C2 f hf ≃*
      order16_wild_reps i}
    {K : Subgroup (CocycleGroup f hf)}
    {eK : K ≃* Multiplicative (ZMod 3)}
    (hSyl : Nat.card (Sylow 3
      (SemidirectProduct (order16_wild_reps i)
        (Multiplicative (ZMod 3)) (order48_RM_wildAction f hf i eP K eK))) = 4) :
    order48_RM_wildAction f hf i eP K eK
        (Multiplicative.ofAdd (1 : ZMod 3)) ≠ 1 := by
  letI : Finite (order16_wild_reps i) := Nat.finite_of_card_ne_zero (by
    rw [card_order16_wild_reps i]
    norm_num)
  exact order48_c3_action_generator_ne_one_of_card_sylow_four
    (card_order16_wild_reps i)
    (order48_RM_wildAction f hf i eP K eK) hSyl

theorem order48_RM_wildAction_generator_order_three
    {f : order24_RM → order24_RM → ZMod 2} {hf : IsCentralCocycle f}
    {i : Fin 14}
    {eP : order48CocycleTwoPreimage order24_c3ActionC2C2C2 f hf ≃*
      order16_wild_reps i}
    {K : Subgroup (CocycleGroup f hf)}
    {eK : K ≃* Multiplicative (ZMod 3)}
    (hSyl : Nat.card (Sylow 3
      (SemidirectProduct (order16_wild_reps i)
        (Multiplicative (ZMod 3)) (order48_RM_wildAction f hf i eP K eK))) = 4) :
    orderOf (order48_RM_wildAction f hf i eP K eK
      (Multiplicative.ofAdd (1 : ZMod 3))) = 3 := by
  apply orderOf_eq_prime
  · exact order48_c3_action_generator_pow_three
      (order48_RM_wildAction f hf i eP K eK)
  · exact order48_RM_wildAction_generator_ne_one hSyl

end Smallgroups.UsefulTheorems
