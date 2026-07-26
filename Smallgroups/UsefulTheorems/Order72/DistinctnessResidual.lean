/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order72.Residual
import Smallgroups.UsefulTheorems.Order72.DistinctnessDirect
import Smallgroups.UsefulTheorems.Counting
import Smallgroups.UsefulTheorems.CenterInvariant

namespace Smallgroups.UsefulTheorems

/-! # Residual branch distinctness for groups of order 72 -/

local instance instFintypeOrder72ResidualSemidirectProduct
    {N H : Type*} [Group N] [Group H] [Fintype N] [Fintype H] (φ : H →* MulAut N) :
    Fintype (SemidirectProduct N H φ) :=
  Fintype.ofEquiv (N × H) SemidirectProduct.equivProd.symm

/-- Decidable equality on semidirect products (via the underlying product). -/
local instance instDecEqOrder72ResidualSemidirectProduct
    {N H : Type*} [Group N] [Group H] [DecidableEq N] [DecidableEq H] (φ : H →* MulAut N) :
    DecidableEq (SemidirectProduct N H φ) :=
  fun a b => decidable_of_iff (SemidirectProduct.equivProd a = SemidirectProduct.equivProd b)
    (Equiv.apply_eq_iff_eq SemidirectProduct.equivProd)

/-- The invariant tuple for the four residual representatives: center cardinality and the
counts of solutions of `x ^ n = 1` for `n ∈ {2, 3, 4, 6, 8, 9, 12, 18, 24}`. -/
noncomputable def order72_residual_invariant (i : Fin 4) :
    Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  (Nat.card (Subgroup.center (order72ResidualRep i)),
    order72_direct_pow_eq_one_card (order72ResidualRep i) 2,
    order72_direct_pow_eq_one_card (order72ResidualRep i) 3,
    order72_direct_pow_eq_one_card (order72ResidualRep i) 4,
    order72_direct_pow_eq_one_card (order72ResidualRep i) 6,
    order72_direct_pow_eq_one_card (order72ResidualRep i) 8,
    order72_direct_pow_eq_one_card (order72ResidualRep i) 9,
    order72_direct_pow_eq_one_card (order72ResidualRep i) 12,
    order72_direct_pow_eq_one_card (order72ResidualRep i) 18,
    order72_direct_pow_eq_one_card (order72ResidualRep i) 24)

theorem order72_residual_invariant_eq_of_mulEquiv {i j : Fin 4}
    (hiso : Nonempty (order72ResidualRep i ≃* order72ResidualRep j)) :
    order72_residual_invariant i = order72_residual_invariant j := by
  obtain ⟨e⟩ := hiso
  simp only [order72_residual_invariant]
  exact Prod.ext (card_center_eq_of_mulEquiv e)
    (Prod.ext (order72_direct_pow_eq_one_card_eq_of_mulEquiv 2 e)
      (Prod.ext (order72_direct_pow_eq_one_card_eq_of_mulEquiv 3 e)
        (Prod.ext (order72_direct_pow_eq_one_card_eq_of_mulEquiv 4 e)
          (Prod.ext (order72_direct_pow_eq_one_card_eq_of_mulEquiv 6 e)
            (Prod.ext (order72_direct_pow_eq_one_card_eq_of_mulEquiv 8 e)
              (Prod.ext (order72_direct_pow_eq_one_card_eq_of_mulEquiv 9 e)
                (Prod.ext (order72_direct_pow_eq_one_card_eq_of_mulEquiv 12 e)
                  (Prod.ext (order72_direct_pow_eq_one_card_eq_of_mulEquiv 18 e)
                    (order72_direct_pow_eq_one_card_eq_of_mulEquiv 24 e)))))))))

/-- The values of `order72_residual_invariant`, computed by kernel reduction. -/
def order72_residual_invariant_table (i : Fin 4) :
    Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  match i with
  | 0 => (1, 22, 3, 40, 30, 40, 27, 48, 54, 48)
  | 1 => (3, 10, 27, 16, 54, 16, 27, 72, 54, 72)
  | 2 => (1, 22, 27, 40, 54, 40, 27, 72, 54, 72)
  | 3 => (1, 16, 27, 16, 72, 16, 27, 72, 72, 72)
  | ⟨n + 4, h⟩ => by omega

set_option maxHeartbeats 8000000 in
-- Finite kernel computation over the residual representative `0`.
theorem order72_residual_invariant_spec_zero :
    order72_residual_invariant 0 = order72_residual_invariant_table 0 := by
  simp only [order72_residual_invariant, order72_residual_invariant_table,
    order72ResidualRep, order72_res_C3S4,
    order72_direct_pow_eq_one_card, Nat.card_eq_fintype_card]
  apply Prod.ext
  · norm_num
    decide +kernel
  · apply Prod.ext
    · norm_num
      decide +kernel
    · apply Prod.ext
      · norm_num
        decide +kernel
      · apply Prod.ext
        · norm_num
          decide +kernel
        · apply Prod.ext
          · norm_num
            decide +kernel
          · apply Prod.ext
            · norm_num
              decide +kernel
            · apply Prod.ext
              · norm_num
                decide +kernel
              · apply Prod.ext
                · norm_num
                  decide +kernel
                · apply Prod.ext
                  · norm_num
                    decide +kernel
                  · norm_num
                    decide +kernel

set_option maxHeartbeats 2000000 in
-- Finite kernel computation over the residual representative `1`.
theorem order72_residual_invariant_spec_one :
    order72_residual_invariant 1 = order72_residual_invariant_table 1 := by
  simp only [order72_residual_invariant, order72_residual_invariant_table,
    order72ResidualRep, order72_res_C3xS4,
    order72_direct_pow_eq_one_card, Nat.card_eq_fintype_card]
  apply Prod.ext
  · norm_num
    decide +kernel
  · apply Prod.ext
    · norm_num
      decide +kernel
    · apply Prod.ext
      · norm_num
        decide +kernel
      · apply Prod.ext
        · norm_num
          decide +kernel
        · apply Prod.ext
          · norm_num
            decide +kernel
          · apply Prod.ext
            · norm_num
              decide +kernel
            · apply Prod.ext
              · norm_num
                decide +kernel
              · apply Prod.ext
                · norm_num
                  decide +kernel
                · apply Prod.ext
                  · norm_num
                    decide +kernel
                  · norm_num
                    decide +kernel

set_option maxHeartbeats 4000000 in
-- Finite kernel computation over the residual representative `2`.
theorem order72_residual_invariant_spec_two :
    order72_residual_invariant 2 = order72_residual_invariant_table 2 := by
  simp only [order72_residual_invariant, order72_residual_invariant_table,
    order72ResidualRep, order72_res_C3sS4,
    order72_direct_pow_eq_one_card, Nat.card_eq_fintype_card]
  apply Prod.ext
  · norm_num
    decide +kernel
  · apply Prod.ext
    · norm_num
      decide +kernel
    · apply Prod.ext
      · norm_num
        decide +kernel
      · apply Prod.ext
        · norm_num
          decide +kernel
        · apply Prod.ext
          · norm_num
            decide +kernel
          · apply Prod.ext
            · norm_num
              decide +kernel
            · apply Prod.ext
              · norm_num
                decide +kernel
              · apply Prod.ext
                · norm_num
                  decide +kernel
                · apply Prod.ext
                  · norm_num
                    decide +kernel
                  · norm_num
                    decide +kernel

set_option maxHeartbeats 2000000 in
-- Finite kernel computation over the residual representative `3`.
theorem order72_residual_invariant_spec_three :
    order72_residual_invariant 3 = order72_residual_invariant_table 3 := by
  simp only [order72_residual_invariant, order72_residual_invariant_table,
    order72ResidualRep, order72_res_S3xA4,
    order72_direct_pow_eq_one_card, Nat.card_eq_fintype_card]
  apply Prod.ext
  · norm_num
    decide +kernel
  · apply Prod.ext
    · norm_num
      decide +kernel
    · apply Prod.ext
      · norm_num
        decide +kernel
      · apply Prod.ext
        · norm_num
          decide +kernel
        · apply Prod.ext
          · norm_num
            decide +kernel
          · apply Prod.ext
            · norm_num
              decide +kernel
            · apply Prod.ext
              · norm_num
                decide +kernel
              · apply Prod.ext
                · norm_num
                  decide +kernel
                · apply Prod.ext
                  · norm_num
                    decide +kernel
                  · norm_num
                    decide +kernel

/-- The invariant values agree with the table at every index. -/
theorem order72_residual_invariant_spec (i : Fin 4) :
    order72_residual_invariant i = order72_residual_invariant_table i := by
  fin_cases i
  · exact order72_residual_invariant_spec_zero
  · exact order72_residual_invariant_spec_one
  · exact order72_residual_invariant_spec_two
  · exact order72_residual_invariant_spec_three

theorem order72_residual_invariant_table_injective :
    Function.Injective order72_residual_invariant_table := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp [order72_residual_invariant_table] at h ⊢

/-- The four residual representatives are pairwise non-isomorphic. -/
theorem order72_residual_reps_pairwise :
    PairwiseNonMulEquiv order72ResidualRep := by
  exact PairwiseNonMulEquiv.of_invariant order72_residual_invariant
    (fun _ _ h => order72_residual_invariant_eq_of_mulEquiv h)
    (fun i j h _ =>
      order72_residual_invariant_table_injective (by
        rw [← order72_residual_invariant_spec i, ← order72_residual_invariant_spec j]
        exact h))

end Smallgroups.UsefulTheorems
