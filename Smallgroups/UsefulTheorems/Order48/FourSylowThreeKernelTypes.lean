/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeSemidirect

/-!
# Kernel-type restrictions in the order-48 four-Sylow-three branch

For an elementary-abelian order-eight quotient, every square in the normal
order-`16` preimage lies in its central kernel of order two.  The square-image
invariant from the classification of groups of order `16` then leaves only
five of the fourteen possible kernel types.
-/

namespace Smallgroups.UsefulTheorems

variable {N : Type*} [Group N]
  (φ : Multiplicative (ZMod 3) →* MulAut N)
  (f : SemidirectProduct N (Multiplicative (ZMod 3)) φ →
    SemidirectProduct N (Multiplicative (ZMod 3)) φ → ZMod 2)
  (hf : IsCentralCocycle f)

theorem card_order48CocycleTwoPreimageToN_ker [Finite N]
    (hN : Nat.card N = 8) :
    Nat.card (order48CocycleTwoPreimageToN φ f hf).ker = 2 := by
  rw [order48CocycleTwoPreimage_kernel_eq_zpowers φ f hf hN,
    Nat.card_zpowers, order_order48CocycleTwoPreimageKernelGenerator]

/-- If the order-eight quotient has exponent two, the square image of its
central double cover has at most two elements. -/
theorem order48CocycleTwoPreimage_square_image_card_le_two [Finite N]
    (hN : Nat.card N = 8) (hNexp : ∀ n : N, n ^ 2 = 1) :
    sq_image_card (order48CocycleTwoPreimage φ f hf) ≤ 2 := by
  let P := order48CocycleTwoPreimage φ f hf
  let π := order48CocycleTwoPreimageToN φ f hf
  let ι : {y : P // ∃ x : P, x ^ 2 = y} → π.ker := fun y =>
    ⟨y.1, by
      obtain ⟨x, hx⟩ := y.2
      rw [MonoidHom.mem_ker, ← hx, map_pow, hNexp]⟩
  have hι : Function.Injective ι := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun t : π.ker => (t.1 : P)) hxy
  change Nat.card {y : P // ∃ x : P, x ^ 2 = y} ≤ 2
  calc
    Nat.card {y : P // ∃ x : P, x ^ 2 = y} ≤ Nat.card π.ker :=
      Nat.card_le_card_of_injective ι hι
    _ = 2 := card_order48CocycleTwoPreimageToN_ker φ f hf hN

/-- The same exponent-two quotient forces the whole order-`16` preimage to
have exponent dividing four. -/
theorem order48CocycleTwoPreimage_pow_four [Finite N]
    (hN : Nat.card N = 8) (hNexp : ∀ n : N, n ^ 2 = 1)
    (p : order48CocycleTwoPreimage φ f hf) : p ^ 4 = 1 := by
  let π := order48CocycleTwoPreimageToN φ f hf
  let z := order48CocycleTwoPreimageKernelGenerator φ f hf
  have hpker : p ^ 2 ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, hNexp]
  have hpz : p ^ 2 ∈ Subgroup.zpowers z := by
    rw [← order48CocycleTwoPreimage_kernel_eq_zpowers φ f hf hN]
    exact hpker
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hpz
  have hz2 : z ^ 2 = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [order_order48CocycleTwoPreimageKernelGenerator] at h
  calc
    p ^ 4 = (p ^ 2) ^ 2 := by group
    _ = (z ^ k) ^ 2 := by rw [hk]
    _ = (z ^ 2) ^ k := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    _ = 1 := by rw [hz2, one_zpow]

theorem pow_four_card_order48CocycleTwoPreimage [Finite N]
    (hN : Nat.card N = 8) (hNexp : ∀ n : N, n ^ 2 = 1) :
    pow_eq_one_card (order48CocycleTwoPreimage φ f hf) 4 = 16 := by
  rw [pow_eq_one_card]
  calc
    Nat.card {p : order48CocycleTwoPreimage φ f hf // p ^ 4 = 1} =
        Nat.card (order48CocycleTwoPreimage φ f hf) := by
      apply Nat.card_congr
      exact
        { toFun := fun p => p.1
          invFun := fun p => ⟨p,
            order48CocycleTwoPreimage_pow_four φ f hf hN hNexp p⟩
          left_inv := fun p => Subtype.ext rfl
          right_inv := fun _ => rfl }
    _ = 16 := card_order48CocycleTwoPreimage φ f hf hN

/-- In the `RM = (C₂)³ ⋊ C₃` branch, only five of the fourteen order-`16`
kernel types survive the square-image obstruction. -/
theorem order48_RM_cocycle_kernel_type_restriction
    (f : order24_RM → order24_RM → ZMod 2) (hf : IsCentralCocycle f) :
    ∃ i : Fin 14,
      (i = 0 ∨ i = 7 ∨ i = 8 ∨ i = 10 ∨ i = 11) ∧
      Nonempty (order48CocycleTwoPreimage order24_c3ActionC2C2C2 f hf ≃*
        order16_wild_reps i) := by
  have hNexp : ∀ n : order24_C2C2C2, n ^ 2 = 1 := by
    intro n
    revert n
    decide
  obtain ⟨i, ⟨e⟩⟩ := order48CocycleTwoPreimage_order16_classification
    order24_c3ActionC2C2C2 f hf card_order24_C2C2C2
  have hsquare : sq_image_card (order16_wild_reps i) ≤ 2 := by
    rw [← sq_image_card_eq_of_mulEquiv e]
    exact order48CocycleTwoPreimage_square_image_card_le_two
      order24_c3ActionC2C2C2 f hf card_order24_C2C2C2 hNexp
  rw [square_image_card_order16_wild_reps] at hsquare
  refine ⟨i, ?_, ⟨e⟩⟩
  fin_cases i <;> simp_all [order16_wild_square_image_card]

end Smallgroups.UsefulTheorems
