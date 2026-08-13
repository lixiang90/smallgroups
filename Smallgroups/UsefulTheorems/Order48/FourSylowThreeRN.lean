/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeRM

/-!
# The remaining RN reduction

The RN quotient is `Q₈ ⋊ C₃`.  As in the RM branch, Schur--Zassenhaus
produces a normal order-`16` preimage and an order-`3` complement.  Unlike RM,
the order-`8` quotient is nonabelian, so the transported action is determined
only up to conjugation by the `Q₈` component of a chosen complement.  We keep
that inner-conjugacy term explicit; removing it is the next RN orbit problem.
-/

namespace Smallgroups.UsefulTheorems

/-! ### The first concrete RN Wild action: `G₁₁` -/

/-- Extend the standard order-three automorphism of `Q₈` by fixing the
additional central involution of `G₁₁ = Q₈ × C₂`. -/
noncomputable def order48_RN_G11_tau3 : MulAut order16_wild_G11 :=
  MulEquiv.prodCongr order24_tau3Q8 (MulEquiv.refl _)

theorem order48_RN_G11_tau3_pow_three :
    order48_RN_G11_tau3 ^ 3 = 1 := by
  apply MulEquiv.ext
  rintro ⟨a, b⟩
  ext
  · change (order24_tau3Q8 ^ 3) a = a
    rw [order24_tau3Q8_pow_three]
    rfl
  · rfl

noncomputable def order48_RN_G11_action :
    Multiplicative (ZMod 3) →* MulAut order16_wild_G11 :=
  MonoidHom.mk' (fun x => order48_RN_G11_tau3 ^
    (Multiplicative.toAdd x).val)
    (fun a b => pow_val_add order48_RN_G11_tau3_pow_three a.toAdd b.toAdd)

noncomputable instance order48_RN_G11_action_fintype :
    Fintype (SemidirectProduct order16_wild_G11
      (Multiplicative (ZMod 3)) order48_RN_G11_action) :=
  Fintype.ofEquiv (order16_wild_G11 × Multiplicative (ZMod 3))
    SemidirectProduct.equivProd.symm

theorem order48_RN_G11_action_card_cube_roots :
    Nat.card {x : SemidirectProduct order16_wild_G11
      (Multiplicative (ZMod 3)) order48_RN_G11_action // x ^ 3 = 1} = 9 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem order48_RN_G11_action_card_sylow_three :
    Nat.card (Sylow 3 (SemidirectProduct order16_wild_G11
      (Multiplicative (ZMod 3)) order48_RN_G11_action)) = 4 :=
  (order48_c3_action_card_sylow_three_eq_four_iff
    (card_order16_wild_G11) order48_RN_G11_action).mpr
    order48_RN_G11_action_card_cube_roots

noncomputable def order48_RN_G11_splitEquiv :
    SemidirectProduct order16_wild_G11
        (Multiplicative (ZMod 3)) order48_RN_G11_action ≃*
      Multiplicative (ZMod 2) × order24_RN where
  toFun x := (x.left.2, ⟨x.left.1, x.right⟩)
  invFun x := ⟨(x.2.left, x.1), x.2.right⟩
  left_inv := by
    rintro ⟨⟨a, b⟩, c⟩
    rfl
  right_inv := by
    rintro ⟨a, ⟨b, c⟩⟩
    rfl
  map_mul' := by
    rintro ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩
    ext <;> revert a b c a' b' c' <;> decide

theorem order48_RN_G11_action_mulEquiv_C2xRN :
    Nonempty (SemidirectProduct order16_wild_G11
      (Multiplicative (ZMod 3)) order48_RN_G11_action ≃*
      Multiplicative (ZMod 2) × order24_RN) :=
  ⟨order48_RN_G11_splitEquiv⟩

theorem order48_RN_G11_action_mem_residualKnownReps :
    Nonempty (SemidirectProduct order16_wild_G11
      (Multiplicative (ZMod 3)) order48_RN_G11_action ≃*
      order48_four_residualKnownReps 6) := by
  obtain ⟨eSL⟩ := order24_SL23_mulEquiv_RN
  exact ⟨order48_RN_G11_splitEquiv.trans
    (MulEquiv.prodCongr (MulEquiv.refl _) eSL.symm)⟩

noncomputable def order48_RN_wildAction
    (f : order24_RN → order24_RN → ZMod 2) (hf : IsCentralCocycle f)
    (i : Fin 14) (eP :
      order48CocycleTwoPreimage order24_c3ActionQ8 f hf ≃*
        order16_wild_reps i)
    (K : Subgroup (CocycleGroup f hf))
    (eK : K ≃* Multiplicative (ZMod 3)) :
    Multiplicative (ZMod 3) →* MulAut (order16_wild_reps i) :=
  (MulAut.congr eP).toMonoidHom.comp
    ((order48CocycleComplementAction order24_c3ActionQ8 f hf K).comp
      eK.symm.toMonoidHom)

/-- Every RN cocycle group is reduced to an order-`16` Wild kernel and a
standard `C₃` complement.  The induced action on the `Q₈` quotient is recorded
by the explicit inner-conjugacy formula supplied by the general reduction. -/
theorem order48_RN_cocycle_reduction_to_wild_action
    (f : order24_RN → order24_RN → ZMod 2) (hf : IsCentralCocycle f) :
    ∃ (i : Fin 14) (K : Subgroup (CocycleGroup f hf))
      (eP : order48CocycleTwoPreimage order24_c3ActionQ8 f hf ≃*
        order16_wild_reps i)
      (eK : K ≃* Multiplicative (ZMod 3)),
      Nat.card K = 3 ∧
      (∀ k : K,
        order48CocycleComplementAction
          order24_c3ActionQ8 f hf K k
            (order48CocycleTwoPreimageKernelGenerator
              order24_c3ActionQ8 f hf) =
          order48CocycleTwoPreimageKernelGenerator
            order24_c3ActionQ8 f hf) ∧
      (∀ k : K, ∀ p : order48CocycleTwoPreimage
          order24_c3ActionQ8 f hf,
        order48CocycleTwoPreimageToN
            order24_c3ActionQ8 f hf
          (order48CocycleComplementAction
            order24_c3ActionQ8 f hf K k p) =
        (k : K).1.snd.left *
          order24_c3ActionQ8
            (order48CocycleComplementToC3
              order24_c3ActionQ8 f hf K k)
            (order48CocycleTwoPreimageToN
              order24_c3ActionQ8 f hf p) *
          (k : K).1.snd.left⁻¹) ∧
      Nonempty (CocycleGroup f hf ≃*
        SemidirectProduct (order16_wild_reps i)
          (Multiplicative (ZMod 3))
          (order48_RN_wildAction f hf i eP K eK)) := by
  obtain ⟨K, hK, hbij, hfix, eG⟩ :=
    order48_RN_cocycle_semidirect_reduction_fixed_kernel f hf
  obtain ⟨i, ⟨eP⟩⟩ := order48CocycleTwoPreimage_order16_classification
    order24_c3ActionQ8 f hf card_order24_Q8
  let eK : K ≃* Multiplicative (ZMod 3) :=
    MulEquiv.ofBijective
      (order48CocycleComplementToC3 order24_c3ActionQ8 f hf K) hbij
  refine ⟨i, K, eP, eK, hK, hfix, ?_, ?_⟩
  · intro k p
    exact order48CocycleComplementAction_toN
      order24_c3ActionQ8 f hf K k p
  · exact ⟨eG.some.trans (SemidirectProduct.congr' eP eK)⟩

/-- The transported RN action is nontrivial whenever its semidirect product
has four Sylow `3`-subgroups.  The remaining RN orbit calculation therefore
concerns only nonidentity order-three automorphisms of the nonabelian Wild
kernels. -/
theorem order48_RN_wildAction_generator_ne_one
    {f : order24_RN → order24_RN → ZMod 2} {hf : IsCentralCocycle f}
    {i : Fin 14}
    {eP : order48CocycleTwoPreimage order24_c3ActionQ8 f hf ≃*
      order16_wild_reps i}
    {K : Subgroup (CocycleGroup f hf)}
    {eK : K ≃* Multiplicative (ZMod 3)}
    (hSyl : Nat.card (Sylow 3
      (SemidirectProduct (order16_wild_reps i)
        (Multiplicative (ZMod 3)) (order48_RN_wildAction f hf i eP K eK))) = 4) :
    order48_RN_wildAction f hf i eP K eK
        (Multiplicative.ofAdd (1 : ZMod 3)) ≠ 1 := by
  letI : Finite (order16_wild_reps i) := Nat.finite_of_card_ne_zero (by
    rw [card_order16_wild_reps i]
    norm_num)
  exact order48_c3_action_generator_ne_one_of_card_sylow_four
    (card_order16_wild_reps i)
    (order48_RN_wildAction f hf i eP K eK) hSyl

theorem order48_RN_wildAction_generator_order_three
    {f : order24_RN → order24_RN → ZMod 2} {hf : IsCentralCocycle f}
    {i : Fin 14}
    {eP : order48CocycleTwoPreimage order24_c3ActionQ8 f hf ≃*
      order16_wild_reps i}
    {K : Subgroup (CocycleGroup f hf)}
    {eK : K ≃* Multiplicative (ZMod 3)}
    (hSyl : Nat.card (Sylow 3
      (SemidirectProduct (order16_wild_reps i)
        (Multiplicative (ZMod 3)) (order48_RN_wildAction f hf i eP K eK))) = 4) :
    orderOf (order48_RN_wildAction f hf i eP K eK
      (Multiplicative.ofAdd (1 : ZMod 3))) = 3 := by
  apply orderOf_eq_prime
  · exact order48_c3_action_generator_pow_three
      (order48_RN_wildAction f hf i eP K eK)
  · exact order48_RN_wildAction_generator_ne_one hSyl

/-- The normal order-`16` kernel in the RN branch is noncommutative: its
quotient by the canonical central involution is `Q₈`. -/
theorem order48_RN_cocycle_wild_kernel_noncommutative
    (f : order24_RN → order24_RN → ZMod 2) (hf : IsCentralCocycle f) :
    ∃ (i : Fin 14) (_ :
      order48CocycleTwoPreimage order24_c3ActionQ8 f hf ≃*
        order16_wild_reps i),
      ¬ ∀ a b : order16_wild_reps i, a * b = b * a := by
  obtain ⟨i, _, eP, _, _, _, _, _, _⟩ :=
    order48_RN_cocycle_reduction_to_wild_action f hf
  refine ⟨i, eP, ?_⟩
  intro hcomm
  let P := order48CocycleTwoPreimage order24_c3ActionQ8 f hf
  let z := order48CocycleTwoPreimageKernelGenerator
    order24_c3ActionQ8 f hf
  let Q := P ⧸ Subgroup.zpowers z
  let eQ := order48CocycleTwoPreimageQuotientEquiv
    order24_c3ActionQ8 f hf card_order24_Q8
  have hPcomm : ∀ a b : P, a * b = b * a := by
    intro a b
    apply eP.injective
    rw [map_mul, map_mul]
    exact hcomm (eP a) (eP b)
  letI : CommGroup P := { (inferInstance : Group P) with mul_comm := hPcomm }
  have hQcomm : ∀ a b : QuaternionGroup 2, a * b = b * a := by
    intro a b
    obtain ⟨a, rfl⟩ := eQ.surjective a
    obtain ⟨b, rfl⟩ := eQ.surjective b
    rw [← map_mul, ← map_mul, mul_comm]
  have hQnoncomm : ¬ (∀ a b : QuaternionGroup 2, a * b = b * a) := by
    decide
  exact hQnoncomm hQcomm

/-- The RN Wild kernel is one of the nine nonabelian order-`16` types.  This
is the first intrinsic restriction on the Wild index before classifying the
order-three actions. -/
theorem order48_RN_cocycle_wild_kernel_type_restriction
    (f : order24_RN → order24_RN → ZMod 2) (hf : IsCentralCocycle f) :
    ∃ (i : Fin 14) (_ :
      order48CocycleTwoPreimage order24_c3ActionQ8 f hf ≃*
        order16_wild_reps i),
      (i ≠ 0 ∧ i ≠ 1 ∧ i ≠ 6 ∧ i ≠ 7 ∧ i ≠ 13) ∧
        ¬ ∀ a b : order16_wild_reps i, a * b = b * a := by
  obtain ⟨i, eP, hnoncomm⟩ :=
    order48_RN_cocycle_wild_kernel_noncommutative f hf
  refine ⟨i, eP, ?_, hnoncomm⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hi
    subst i
    apply hnoncomm
    intro a b
    exact mul_comm a b
  · intro hi
    subst i
    apply hnoncomm
    intro a b
    exact mul_comm a b
  · intro hi
    subst i
    apply hnoncomm
    intro a b
    exact mul_comm a b
  · intro hi
    subst i
    apply hnoncomm
    intro a b
    exact mul_comm a b
  · intro hi
    subst i
    apply hnoncomm
    intro a b
    exact mul_comm a b

end Smallgroups.UsefulTheorems
