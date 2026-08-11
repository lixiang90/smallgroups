/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeCocycles
import Smallgroups.UsefulTheorems.SchurZassenhaus

/-!
# Semidirect reduction for two order-48 residual cocycle branches

For a central `C₂`-extension of an order-24 group `N ⋊ C₃`, the preimage
of `N` is a normal subgroup of order `16`.  Schur–Zassenhaus then writes the
extension as `P ⋊ C₃`.  This applies directly to the `RM` and `RN` quotient
branches and reduces their remaining classification to order-`16` groups and
order-three automorphisms.
-/

namespace Smallgroups.UsefulTheorems

variable {N : Type*} [Group N]
  (φ : Multiplicative (ZMod 3) →* MulAut N)
  (f : SemidirectProduct N (Multiplicative (ZMod 3)) φ →
    SemidirectProduct N (Multiplicative (ZMod 3)) φ → ZMod 2)
  (hf : IsCentralCocycle f)

/-- The preimage of the normal `N` factor in a central cocycle extension of
`N ⋊ C₃`. -/
noncomputable def order48CocycleTwoPreimage :
    Subgroup (CocycleGroup f hf) :=
  (SemidirectProduct.inl :
    N →* SemidirectProduct N (Multiplicative (ZMod 3)) φ).range.comap
      (CocycleGroup.rightHom (hf := hf))

noncomputable instance instNormalOrder48CocycleTwoPreimage :
    (order48CocycleTwoPreimage φ f hf).Normal := by
  haveI : (SemidirectProduct.inl :
      N →* SemidirectProduct N (Multiplicative (ZMod 3)) φ).range.Normal := by
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  change ((SemidirectProduct.inl :
      N →* SemidirectProduct N (Multiplicative (ZMod 3)) φ).range.comap
        (CocycleGroup.rightHom (hf := hf))).Normal
  infer_instance

/-- As a finite type, the preimage is just `ZMod 2 × N`. -/
noncomputable def order48CocycleTwoPreimageEquiv :
    order48CocycleTwoPreimage φ f hf ≃ ZMod 2 × N where
  toFun x := (x.1.fst, x.1.snd.left)
  invFun x := ⟨⟨x.1, SemidirectProduct.inl x.2⟩, ⟨x.2, rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    apply CocycleGroup.ext
    · rfl
    · apply SemidirectProduct.ext
      · rfl
      · rcases x.2 with ⟨n, hn⟩
        simpa using congrArg SemidirectProduct.right hn
  right_inv x := by ext <;> rfl

theorem card_order48CocycleTwoPreimage [Finite N] (hN : Nat.card N = 8) :
    Nat.card (order48CocycleTwoPreimage φ f hf) = 16 := by
  rw [Nat.card_congr (order48CocycleTwoPreimageEquiv φ f hf), Nat.card_prod,
    Nat.card_eq_fintype_card, hN]
  decide

private theorem order48CocycleTwoPreimage_right_eq_one
    (x : order48CocycleTwoPreimage φ f hf) : x.1.snd.right = 1 := by
  rcases x.2 with ⟨n, hn⟩
  simpa using congrArg SemidirectProduct.right hn.symm

/-- Projection of the normal order-`16` preimage back onto its order-`8`
factor. -/
def order48CocycleTwoPreimageToN :
    order48CocycleTwoPreimage φ f hf →* N where
  toFun x := x.1.snd.left
  map_one' := rfl
  map_mul' x y := by
    change (x.1.snd * y.1.snd).left = x.1.snd.left * y.1.snd.left
    rw [SemidirectProduct.mul_left]
    rw [order48CocycleTwoPreimage_right_eq_one φ f hf x, map_one]
    rfl

@[simp] theorem order48CocycleTwoPreimageToN_apply
    (x : order48CocycleTwoPreimage φ f hf) :
    order48CocycleTwoPreimageToN φ f hf x = x.1.snd.left := rfl

theorem order48CocycleTwoPreimageToN_surjective :
    Function.Surjective (order48CocycleTwoPreimageToN φ f hf) := by
  intro n
  refine ⟨⟨⟨0, SemidirectProduct.inl n⟩, ?_⟩, rfl⟩
  exact ⟨n, rfl⟩

/-- The canonical central involution inside the order-`16` preimage. -/
def order48CocycleTwoPreimageKernelGenerator :
    order48CocycleTwoPreimage φ f hf :=
  ⟨CocycleGroup.inl (hf := hf) (Multiplicative.ofAdd (1 : ZMod 2)),
    by
      change (1 : SemidirectProduct N (Multiplicative (ZMod 3)) φ) ∈
        (SemidirectProduct.inl : N →*
          SemidirectProduct N (Multiplicative (ZMod 3)) φ).range
      exact Subgroup.one_mem _⟩

theorem order_order48CocycleTwoPreimageKernelGenerator :
    orderOf (order48CocycleTwoPreimageKernelGenerator φ f hf) = 2 := by
  calc
    orderOf (order48CocycleTwoPreimageKernelGenerator φ f hf) =
        orderOf (CocycleGroup.inl (hf := hf)
          (Multiplicative.ofAdd (1 : ZMod 2))) :=
      (orderOf_injective
        (order48CocycleTwoPreimage φ f hf).subtype Subtype.coe_injective
        (order48CocycleTwoPreimageKernelGenerator φ f hf)).symm
    _ = orderOf (Multiplicative.ofAdd (1 : ZMod 2)) :=
      orderOf_injective (CocycleGroup.inl (hf := hf))
        CocycleGroup.inl_injective _
    _ = 2 := by
      rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

theorem order48CocycleTwoPreimageKernelGenerator_mem_center :
    order48CocycleTwoPreimageKernelGenerator φ f hf ∈
      Subgroup.center (order48CocycleTwoPreimage φ f hf) := by
  rw [Subgroup.mem_center_iff]
  intro x
  apply Subtype.ext
  exact (Subgroup.mem_center_iff.mp
    (CocycleGroup.inl_mem_center
      (hf := hf) (Multiplicative.ofAdd (1 : ZMod 2)))) x.1

instance order48CocycleTwoPreimageKernelNormal :
    (Subgroup.zpowers
      (order48CocycleTwoPreimageKernelGenerator φ f hf)).Normal :=
  normal_of_le_center (Subgroup.zpowers_le.mpr
    (order48CocycleTwoPreimageKernelGenerator_mem_center φ f hf))

theorem order48CocycleTwoPreimage_kernel_eq_zpowers [Finite N]
    (hN : Nat.card N = 8) :
    (order48CocycleTwoPreimageToN φ f hf).ker =
      Subgroup.zpowers (order48CocycleTwoPreimageKernelGenerator φ f hf) := by
  let P := order48CocycleTwoPreimage φ f hf
  let π := order48CocycleTwoPreimageToN φ f hf
  let z := order48CocycleTwoPreimageKernelGenerator φ f hf
  have hzker : z ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    change (1 : N) = 1
    rfl
  have hle : Subgroup.zpowers z ≤ π.ker := Subgroup.zpowers_le.mpr hzker
  have hP : Nat.card P = 16 := card_order48CocycleTwoPreimage φ f hf hN
  have hquot : Nat.card (P ⧸ π.ker) = 8 := by
    rw [Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective π
        (order48CocycleTwoPreimageToN_surjective φ f hf)).toEquiv,
      hN]
  have hker : Nat.card π.ker = 2 := by
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
    rw [hP, hquot] at hcard
    omega
  symm
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [Nat.card_zpowers,
    order_order48CocycleTwoPreimageKernelGenerator φ f hf, hker]

/-- Quotienting the normal order-`16` preimage by its canonical central
involution recovers the original order-`8` factor. -/
noncomputable def order48CocycleTwoPreimageQuotientEquiv [Finite N]
    (hN : Nat.card N = 8) :
    order48CocycleTwoPreimage φ f hf ⧸
        Subgroup.zpowers (order48CocycleTwoPreimageKernelGenerator φ f hf) ≃* N := by
  exact
    (QuotientGroup.quotientMulEquivOfEq
        (order48CocycleTwoPreimage_kernel_eq_zpowers φ f hf hN).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (order48CocycleTwoPreimageToN φ f hf)
        (order48CocycleTwoPreimageToN_surjective φ f hf))

/-- The conjugation action of an ambient subgroup on the normal order-`16`
preimage. -/
noncomputable def order48CocycleComplementAction
    (K : Subgroup (CocycleGroup f hf)) :
    K →* MulAut (order48CocycleTwoPreimage φ f hf) :=
  (order48CocycleTwoPreimage φ f hf).normalizerMonoidHom.comp
    (Subgroup.inclusion (by
      rw [(order48CocycleTwoPreimage φ f hf).normalizer_eq_top]
      exact le_top))

/-- Conjugation by every ambient element fixes the canonical kernel
involution.  In particular, every complement action supplied by
Schur–Zassenhaus descends through the central quotient. -/
theorem order48CocycleComplementAction_fixes_kernel
    (K : Subgroup (CocycleGroup f hf)) (k : K) :
    order48CocycleComplementAction φ f hf K k
        (order48CocycleTwoPreimageKernelGenerator φ f hf) =
      order48CocycleTwoPreimageKernelGenerator φ f hf := by
  apply Subtype.ext
  change k.1 * CocycleGroup.inl (hf := hf)
      (Multiplicative.ofAdd (1 : ZMod 2)) * k.1⁻¹ =
    CocycleGroup.inl (hf := hf) (Multiplicative.ofAdd (1 : ZMod 2))
  have hcomm := Subgroup.mem_center_iff.mp
    (CocycleGroup.inl_mem_center
      (hf := hf) (Multiplicative.ofAdd (1 : ZMod 2))) k.1
  rw [hcomm]
  group

/-- Strong form of the semidirect reduction: the action is explicitly the
ambient conjugation action, and it fixes the canonical central involution. -/
theorem order48_cocycle_over_semidirect_reduction_fixed_kernel [Finite N]
    (hN : Nat.card N = 8) :
    ∃ K : Subgroup (CocycleGroup f hf),
      Nat.card K = 3 ∧
      (∀ k : K, order48CocycleComplementAction φ f hf K k
          (order48CocycleTwoPreimageKernelGenerator φ f hf) =
        order48CocycleTwoPreimageKernelGenerator φ f hf) ∧
      Nonempty (CocycleGroup f hf ≃*
        SemidirectProduct (order48CocycleTwoPreimage φ f hf) K
          (order48CocycleComplementAction φ f hf K)) := by
  let P : Subgroup (CocycleGroup f hf) :=
    order48CocycleTwoPreimage φ f hf
  have hP : Nat.card P = 16 :=
    card_order48CocycleTwoPreimage φ f hf hN
  have hQ : Nat.card
      (SemidirectProduct N (Multiplicative (ZMod 3)) φ) = 24 := by
    rw [SemidirectProduct.card, hN, Nat.card_eq_fintype_card]
    decide
  have hE : Nat.card (CocycleGroup f hf) = 48 := by
    rw [CocycleGroup.card_eq, hQ, Nat.card_eq_fintype_card]
    decide
  have hindex : P.index = 3 := by
    have hmul := P.card_mul_index
    rw [hP, hE] at hmul
    omega
  have hcop : Nat.Coprime (Nat.card P) P.index := by
    rw [hP, hindex]
    norm_num
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hcardK : Nat.card K = 3 := by
    have hcard : Nat.card (SemidirectProduct P K
        (order48CocycleComplementAction φ f hf K)) = Nat.card (CocycleGroup f hf) :=
      Nat.card_congr (SemidirectProduct.mulEquivSubgroup hK).toEquiv
    rw [SemidirectProduct.card, hP, hE] at hcard
    omega
  refine ⟨K, hcardK, ?_, ?_⟩
  · exact order48CocycleComplementAction_fixes_kernel φ f hf K
  · exact ⟨(SemidirectProduct.mulEquivSubgroup hK).symm⟩

/-- The normal preimage is one of the fourteen classified groups of order
`16`.  The quotient and fixed-kernel results above retain the extra data
needed to eliminate incompatible representatives and actions. -/
theorem order48CocycleTwoPreimage_order16_classification [Finite N]
    (hN : Nat.card N = 8) :
    ∃ i : Fin 14, Nonempty
      (order48CocycleTwoPreimage φ f hf ≃* order16_wild_reps i) :=
  order16_wild_classification (card_order48CocycleTwoPreimage φ f hf hN)

/-- Every central `C₂`-extension of `N ⋊ C₃`, with `|N| = 8`, splits
over its normal order-`16` preimage as a semidirect product by a group of
order `3`. -/
theorem order48_cocycle_over_semidirect_reduction [Finite N]
    (hN : Nat.card N = 8) :
    ∃ (K : Subgroup (CocycleGroup f hf))
      (ρ : K →* MulAut (order48CocycleTwoPreimage φ f hf)),
      Nat.card K = 3 ∧
      Nonempty (CocycleGroup f hf ≃*
        SemidirectProduct (order48CocycleTwoPreimage φ f hf) K ρ) := by
  obtain ⟨K, hK, _, e⟩ :=
    order48_cocycle_over_semidirect_reduction_fixed_kernel φ f hf hN
  exact ⟨K, order48CocycleComplementAction φ f hf K, hK, e⟩

/-- The `RM = (C₂)³ ⋊ C₃` cocycle branch has a normal order-`16`
subgroup and a complement of order `3`. -/
theorem order48_RM_cocycle_semidirect_reduction_fixed_kernel
    (f : order24_RM → order24_RM → ZMod 2) (hf : IsCentralCocycle f) :
    ∃ K : Subgroup (CocycleGroup f hf),
      Nat.card K = 3 ∧
      (∀ k : K,
        order48CocycleComplementAction order24_c3ActionC2C2C2 f hf K k
            (order48CocycleTwoPreimageKernelGenerator
              order24_c3ActionC2C2C2 f hf) =
          order48CocycleTwoPreimageKernelGenerator
            order24_c3ActionC2C2C2 f hf) ∧
      Nonempty (CocycleGroup f hf ≃*
        SemidirectProduct
          (order48CocycleTwoPreimage order24_c3ActionC2C2C2 f hf) K
          (order48CocycleComplementAction
            order24_c3ActionC2C2C2 f hf K)) :=
  order48_cocycle_over_semidirect_reduction_fixed_kernel
    order24_c3ActionC2C2C2 f hf card_order24_C2C2C2

theorem order48_RM_cocycle_semidirect_reduction
    (f : order24_RM → order24_RM → ZMod 2) (hf : IsCentralCocycle f) :
    ∃ (K : Subgroup (CocycleGroup f hf))
      (ρ : K →* MulAut
        (order48CocycleTwoPreimage order24_c3ActionC2C2C2 f hf)),
      Nat.card K = 3 ∧
      Nonempty (CocycleGroup f hf ≃*
        SemidirectProduct
          (order48CocycleTwoPreimage order24_c3ActionC2C2C2 f hf) K ρ) :=
  order48_cocycle_over_semidirect_reduction
    order24_c3ActionC2C2C2 f hf card_order24_C2C2C2

/-- The `RN = Q₈ ⋊ C₃` cocycle branch has a normal order-`16`
subgroup and a complement of order `3`. -/
theorem order48_RN_cocycle_semidirect_reduction_fixed_kernel
    (f : order24_RN → order24_RN → ZMod 2) (hf : IsCentralCocycle f) :
    ∃ K : Subgroup (CocycleGroup f hf),
      Nat.card K = 3 ∧
      (∀ k : K,
        order48CocycleComplementAction order24_c3ActionQ8 f hf K k
            (order48CocycleTwoPreimageKernelGenerator
              order24_c3ActionQ8 f hf) =
          order48CocycleTwoPreimageKernelGenerator
            order24_c3ActionQ8 f hf) ∧
      Nonempty (CocycleGroup f hf ≃*
        SemidirectProduct
          (order48CocycleTwoPreimage order24_c3ActionQ8 f hf) K
          (order48CocycleComplementAction order24_c3ActionQ8 f hf K)) :=
  order48_cocycle_over_semidirect_reduction_fixed_kernel
    order24_c3ActionQ8 f hf card_order24_Q8

theorem order48_RN_cocycle_semidirect_reduction
    (f : order24_RN → order24_RN → ZMod 2) (hf : IsCentralCocycle f) :
    ∃ (K : Subgroup (CocycleGroup f hf))
      (ρ : K →* MulAut
        (order48CocycleTwoPreimage order24_c3ActionQ8 f hf)),
      Nat.card K = 3 ∧
      Nonempty (CocycleGroup f hf ≃*
        SemidirectProduct
          (order48CocycleTwoPreimage order24_c3ActionQ8 f hf) K ρ) :=
  order48_cocycle_over_semidirect_reduction
    order24_c3ActionQ8 f hf card_order24_Q8

end Smallgroups.UsefulTheorems
