/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order72.H8xP9
import Smallgroups.UsefulTheorems.Order72.P9xH8_H2
import Smallgroups.UsefulTheorems.Order72.P9xH8_E8
import Smallgroups.UsefulTheorems.Order72.P9xH8_Q8
import Smallgroups.UsefulTheorems.Order72.P9xH8_D4
import Smallgroups.UsefulTheorems.Order72.DistinctnessDirect
import Smallgroups.UsefulTheorems.Counting
import Smallgroups.UsefulTheorems.CenterInvariant

namespace Smallgroups.UsefulTheorems

/-! # `E9`-kernel semidirect branch distinctness for groups of order 72 -/

noncomputable local instance instFintypeOrder72E9SemidirectProduct
    {N H : Type*} [Group N] [Group H] [Fintype N] [Fintype H] (φ : H →* MulAut N) :
    Fintype (SemidirectProduct N H φ) :=
  Fintype.ofEquiv (N × H) SemidirectProduct.equivProd.symm

/-- The twenty-five nontrivial `E9 ⋊ H` representatives in the order-72 list. -/
noncomputable abbrev order72_e9_reps : Fin 25 → Type
  | 0 => order72_E9_C8_neg
  | 1 => order72_E9_C8_reflect
  | 2 => order72_E9_C8_order4
  | 3 => order72_E9_C8_order8
  | 4 => order72_E9_H2_fstNeg
  | 5 => order72_E9_H2_sndNeg
  | 6 => order72_E9_H2_fstReflect
  | 7 => order72_E9_H2_sndReflect
  | 8 => order72_E9_H2_v4NegReflect
  | 9 => order72_E9_H2_v4ReflectNeg
  | 10 => order72_E9_H2_order4
  | 11 => order72_E9_E8_neg100
  | 12 => order72_E9_E8_reflect100
  | 13 => order72_E9_E8_v4
  | 14 => order72_E9_Q8_negI
  | 15 => order72_E9_Q8_reflectI
  | 16 => order72_E9_Q8_v4
  | 17 => order72_E9_Q8_faithful
  | 18 => order72_E9_D4_sNeg
  | 19 => order72_E9_D4_sReflect
  | 20 => order72_E9_D4_rNeg
  | 21 => order72_E9_D4_rReflect
  | 22 => order72_E9_D4_v4NegReflect
  | 23 => order72_E9_D4_v4ReflectNeg
  | 24 => order72_E9_D4_faithful
  | ⟨n + 25, h⟩ => by omega

noncomputable instance order72_e9_reps_group :
    (i : Fin 25) → Group (order72_e9_reps i)
  | ⟨0, _⟩ => inferInstance
  | ⟨1, _⟩ => inferInstance
  | ⟨2, _⟩ => inferInstance
  | ⟨3, _⟩ => inferInstance
  | ⟨4, _⟩ => inferInstance
  | ⟨5, _⟩ => inferInstance
  | ⟨6, _⟩ => inferInstance
  | ⟨7, _⟩ => inferInstance
  | ⟨8, _⟩ => inferInstance
  | ⟨9, _⟩ => inferInstance
  | ⟨10, _⟩ => inferInstance
  | ⟨11, _⟩ => inferInstance
  | ⟨12, _⟩ => inferInstance
  | ⟨13, _⟩ => inferInstance
  | ⟨14, _⟩ => inferInstance
  | ⟨15, _⟩ => inferInstance
  | ⟨16, _⟩ => inferInstance
  | ⟨17, _⟩ => inferInstance
  | ⟨18, _⟩ => inferInstance
  | ⟨19, _⟩ => inferInstance
  | ⟨20, _⟩ => inferInstance
  | ⟨21, _⟩ => inferInstance
  | ⟨22, _⟩ => inferInstance
  | ⟨23, _⟩ => inferInstance
  | ⟨24, _⟩ => inferInstance
  | ⟨n + 25, h⟩ => by omega

/-- The invariant tuple for the `E9 ⋊ H` representatives: center cardinality and the
counts of solutions of `x ^ n = 1` for `n ∈ {2, 3, 4, 6, 8, 9, 12, 18, 24}`. -/
noncomputable def order72_e9_invariant (i : Fin 25) :
    Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  (Nat.card (Subgroup.center (order72_e9_reps i)),
    order72_direct_pow_eq_one_card (order72_e9_reps i) 2,
    order72_direct_pow_eq_one_card (order72_e9_reps i) 3,
    order72_direct_pow_eq_one_card (order72_e9_reps i) 4,
    order72_direct_pow_eq_one_card (order72_e9_reps i) 6,
    order72_direct_pow_eq_one_card (order72_e9_reps i) 8,
    order72_direct_pow_eq_one_card (order72_e9_reps i) 9,
    order72_direct_pow_eq_one_card (order72_e9_reps i) 12,
    order72_direct_pow_eq_one_card (order72_e9_reps i) 18,
    order72_direct_pow_eq_one_card (order72_e9_reps i) 24)

theorem order72_e9_invariant_eq_of_mulEquiv {i j : Fin 25}
    (hiso : Nonempty (order72_e9_reps i ≃* order72_e9_reps j)) :
    order72_e9_invariant i = order72_e9_invariant j := by
  obtain ⟨e⟩ := hiso
  simp only [order72_e9_invariant]
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

/-- The values of `order72_e9_invariant`, computed by kernel reduction. -/
def order72_e9_invariant_table (i : Fin 25) :
    Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  match i with
  | 0 => (4, 2, 9, 4, 18, 40, 9, 36, 18, 72)
  | 1 => (12, 2, 9, 4, 18, 16, 9, 36, 18, 72)
  | 2 => (2, 2, 9, 20, 18, 56, 9, 36, 18, 72)
  | 3 => (1, 10, 9, 28, 18, 64, 9, 36, 18, 72)
  | 4 => (4, 4, 9, 40, 36, 40, 9, 72, 36, 72)
  | 5 => (4, 20, 9, 40, 36, 40, 9, 72, 36, 72)
  | 6 => (12, 4, 9, 16, 36, 16, 9, 72, 36, 72)
  | 7 => (12, 8, 9, 16, 36, 16, 9, 72, 36, 72)
  | 8 => (2, 8, 9, 32, 36, 32, 9, 72, 36, 72)
  | 9 => (2, 20, 9, 32, 36, 32, 9, 72, 36, 72)
  | 10 => (2, 20, 9, 56, 36, 56, 9, 72, 36, 72)
  | 11 => (4, 40, 9, 40, 72, 40, 9, 72, 72, 72)
  | 12 => (12, 16, 9, 16, 72, 16, 9, 72, 72, 72)
  | 13 => (2, 32, 9, 32, 72, 32, 9, 72, 72, 72)
  | 14 => (2, 2, 9, 40, 18, 40, 9, 72, 18, 72)
  | 15 => (6, 2, 9, 16, 18, 16, 9, 72, 18, 72)
  | 16 => (2, 2, 9, 32, 18, 32, 9, 72, 18, 72)
  | 17 => (1, 10, 9, 64, 18, 64, 9, 72, 18, 72)
  | 18 => (2, 38, 9, 40, 54, 40, 9, 72, 54, 72)
  | 19 => (6, 14, 9, 16, 54, 16, 9, 72, 54, 72)
  | 20 => (2, 22, 9, 40, 54, 40, 9, 72, 54, 72)
  | 21 => (6, 10, 9, 16, 54, 16, 9, 72, 54, 72)
  | 22 => (2, 14, 9, 32, 54, 32, 9, 72, 54, 72)
  | 23 => (2, 26, 9, 32, 54, 32, 9, 72, 54, 72)
  | 24 => (1, 22, 9, 40, 54, 40, 9, 72, 54, 72)
  | ⟨n + 25, h⟩ => by omega

set_option maxHeartbeats 2000000 in
-- Finite kernel computation over the `c8` cell of the `E9`-kernel semidirect products.
theorem order72_e9_invariant_spec_c8 :
    order72_e9_invariant 0 = order72_e9_invariant_table 0 ∧
      order72_e9_invariant 1 = order72_e9_invariant_table 1 ∧
      order72_e9_invariant 2 = order72_e9_invariant_table 2 ∧
      order72_e9_invariant 3 = order72_e9_invariant_table 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [order72_e9_invariant, order72_e9_invariant_table, order72_e9_reps,
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
-- Finite kernel computation over the `h2` cell of the `E9`-kernel semidirect products.
theorem order72_e9_invariant_spec_h2 :
    order72_e9_invariant 4 = order72_e9_invariant_table 4 ∧
      order72_e9_invariant 5 = order72_e9_invariant_table 5 ∧
      order72_e9_invariant 6 = order72_e9_invariant_table 6 ∧
      order72_e9_invariant 7 = order72_e9_invariant_table 7 ∧
      order72_e9_invariant 8 = order72_e9_invariant_table 8 ∧
      order72_e9_invariant 9 = order72_e9_invariant_table 9 ∧
      order72_e9_invariant 10 = order72_e9_invariant_table 10 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [order72_e9_invariant, order72_e9_invariant_table, order72_e9_reps,
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
-- Finite kernel computation over the `e8` cell of the `E9`-kernel semidirect products.
theorem order72_e9_invariant_spec_e8 :
    order72_e9_invariant 11 = order72_e9_invariant_table 11 ∧
      order72_e9_invariant 12 = order72_e9_invariant_table 12 ∧
      order72_e9_invariant 13 = order72_e9_invariant_table 13 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [order72_e9_invariant, order72_e9_invariant_table, order72_e9_reps,
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
-- Finite kernel computation over the `q8` cell of the `E9`-kernel semidirect products.
theorem order72_e9_invariant_spec_q8 :
    order72_e9_invariant 14 = order72_e9_invariant_table 14 ∧
      order72_e9_invariant 15 = order72_e9_invariant_table 15 ∧
      order72_e9_invariant 16 = order72_e9_invariant_table 16 ∧
      order72_e9_invariant 17 = order72_e9_invariant_table 17 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [order72_e9_invariant, order72_e9_invariant_table, order72_e9_reps,
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
-- Finite kernel computation over the `d4` cell of the `E9`-kernel semidirect products.
theorem order72_e9_invariant_spec_d4 :
    order72_e9_invariant 18 = order72_e9_invariant_table 18 ∧
      order72_e9_invariant 19 = order72_e9_invariant_table 19 ∧
      order72_e9_invariant 20 = order72_e9_invariant_table 20 ∧
      order72_e9_invariant 21 = order72_e9_invariant_table 21 ∧
      order72_e9_invariant 22 = order72_e9_invariant_table 22 ∧
      order72_e9_invariant 23 = order72_e9_invariant_table 23 ∧
      order72_e9_invariant 24 = order72_e9_invariant_table 24 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [order72_e9_invariant, order72_e9_invariant_table, order72_e9_reps,
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
theorem order72_e9_invariant_spec (i : Fin 25) :
    order72_e9_invariant i = order72_e9_invariant_table i := by
  fin_cases i
  · exact order72_e9_invariant_spec_c8.1
  · exact order72_e9_invariant_spec_c8.2.1
  · exact order72_e9_invariant_spec_c8.2.2.1
  · exact order72_e9_invariant_spec_c8.2.2.2
  · exact order72_e9_invariant_spec_h2.1
  · exact order72_e9_invariant_spec_h2.2.1
  · exact order72_e9_invariant_spec_h2.2.2.1
  · exact order72_e9_invariant_spec_h2.2.2.2.1
  · exact order72_e9_invariant_spec_h2.2.2.2.2.1
  · exact order72_e9_invariant_spec_h2.2.2.2.2.2.1
  · exact order72_e9_invariant_spec_h2.2.2.2.2.2.2
  · exact order72_e9_invariant_spec_e8.1
  · exact order72_e9_invariant_spec_e8.2.1
  · exact order72_e9_invariant_spec_e8.2.2
  · exact order72_e9_invariant_spec_q8.1
  · exact order72_e9_invariant_spec_q8.2.1
  · exact order72_e9_invariant_spec_q8.2.2.1
  · exact order72_e9_invariant_spec_q8.2.2.2
  · exact order72_e9_invariant_spec_d4.1
  · exact order72_e9_invariant_spec_d4.2.1
  · exact order72_e9_invariant_spec_d4.2.2.1
  · exact order72_e9_invariant_spec_d4.2.2.2.1
  · exact order72_e9_invariant_spec_d4.2.2.2.2.1
  · exact order72_e9_invariant_spec_d4.2.2.2.2.2.1
  · exact order72_e9_invariant_spec_d4.2.2.2.2.2.2

theorem order72_e9_invariant_table_injective :
    Function.Injective order72_e9_invariant_table := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp [order72_e9_invariant_table] at h ⊢

/-- The twenty-five `E9 ⋊ H` representatives are pairwise non-isomorphic. -/
theorem order72_e9_reps_pairwise :
    PairwiseNonMulEquiv order72_e9_reps := by
  exact PairwiseNonMulEquiv.of_invariant order72_e9_invariant
    (fun _ _ h => order72_e9_invariant_eq_of_mulEquiv h)
    (fun i j h _ =>
      order72_e9_invariant_table_injective (by
        rw [← order72_e9_invariant_spec i, ← order72_e9_invariant_spec j]
        exact h))

end Smallgroups.UsefulTheorems

