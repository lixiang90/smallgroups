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
  obtain ⟨K, ρ, e⟩ := schurZassenhaus_semidirectProduct P hcop
  have hK : Nat.card K = 3 := by
    have hcard := Nat.card_congr e.some.toEquiv
    rw [SemidirectProduct.card, hE, hP] at hcard
    omega
  exact ⟨K, ρ, hK, e⟩

/-- The `RM = (C₂)³ ⋊ C₃` cocycle branch has a normal order-`16`
subgroup and a complement of order `3`. -/
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
