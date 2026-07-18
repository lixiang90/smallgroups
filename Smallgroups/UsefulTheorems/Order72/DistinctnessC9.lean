/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order72.H8xP9
import Smallgroups.UsefulTheorems.Order72.DistinctnessDirect
import Smallgroups.UsefulTheorems.Counting
import Smallgroups.UsefulTheorems.CenterInvariant

namespace Smallgroups.UsefulTheorems

/-! # `C9`-kernel semidirect branch distinctness for groups of order 72 -/

noncomputable local instance instFintypeOrder72C9SemidirectProduct
    {N H : Type*} [Group N] [Group H] [Fintype N] [Fintype H] (φ : H →* MulAut N) :
    Fintype (SemidirectProduct N H φ) :=
  Fintype.ofEquiv (N × H) SemidirectProduct.equivProd.symm

/-- The seven nontrivial `C9 ⋊ H` representatives in the order-72 list. -/
noncomputable abbrev order72_c9_reps : Fin 7 → Type
  | 0 => order72_C9_C8_inv
  | 1 => order72_C9_H2_fstInv
  | 2 => order72_C9_H2_sndInv
  | 3 => order72_C9_E8_inv100
  | 4 => order72_C9_Q8_invA
  | 5 => order72_C9_D4_invRot
  | 6 => order72_C9_D4_invRef

noncomputable instance order72_c9_reps_group :
    (i : Fin 7) → Group (order72_c9_reps i)
  | 0 => inferInstance
  | 1 => inferInstance
  | 2 => inferInstance
  | 3 => inferInstance
  | 4 => inferInstance
  | 5 => inferInstance
  | 6 => inferInstance
  | ⟨n + 7, h⟩ => by omega

noncomputable def order72_c9_invariant (i : Fin 7) :
    Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  (Nat.card (Subgroup.center (order72_c9_reps i)),
    order72_direct_pow_eq_one_card (order72_c9_reps i) 2,
    order72_direct_pow_eq_one_card (order72_c9_reps i) 3,
    order72_direct_pow_eq_one_card (order72_c9_reps i) 4,
    order72_direct_pow_eq_one_card (order72_c9_reps i) 6,
    order72_direct_pow_eq_one_card (order72_c9_reps i) 8,
    order72_direct_pow_eq_one_card (order72_c9_reps i) 9,
    order72_direct_pow_eq_one_card (order72_c9_reps i) 12,
    order72_direct_pow_eq_one_card (order72_c9_reps i) 18,
    order72_direct_pow_eq_one_card (order72_c9_reps i) 24)

theorem order72_c9_invariant_eq_of_mulEquiv {i j : Fin 7}
    (hiso : Nonempty (order72_c9_reps i ≃* order72_c9_reps j)) :
    order72_c9_invariant i = order72_c9_invariant j := by
  obtain ⟨e⟩ := hiso
  simp only [order72_c9_invariant]
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

def order72_c9_invariant_table (i : Fin 7) :
    Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  match i with
  | 0 => (4, 2, 3, 4, 6, 40, 9, 12, 18, 48)
  | 1 => (4, 4, 3, 40, 12, 40, 9, 48, 36, 48)
  | 2 => (4, 20, 3, 40, 24, 40, 9, 48, 36, 48)
  | 3 => (4, 40, 3, 40, 48, 40, 9, 48, 72, 48)
  | 4 => (2, 2, 3, 40, 6, 40, 9, 48, 18, 48)
  | 5 => (2, 22, 3, 40, 30, 40, 9, 48, 54, 48)
  | 6 => (2, 38, 3, 40, 42, 40, 9, 48, 54, 48)

set_option maxHeartbeats 2000000 in
-- Finite kernel computation over the seven concrete `C9`-kernel semidirect products.
theorem order72_c9_invariant_spec (i : Fin 7) :
    order72_c9_invariant i = order72_c9_invariant_table i := by
  classical
  fin_cases i <;>
    simp only [order72_c9_invariant, order72_c9_invariant_table, order72_c9_reps,
      order72_direct_pow_eq_one_card, Nat.card_eq_fintype_card]
  all_goals
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

theorem order72_c9_invariant_table_injective :
    Function.Injective order72_c9_invariant_table := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp [order72_c9_invariant_table] at h ⊢

theorem order72_c9_reps_pairwise :
    PairwiseNonMulEquiv order72_c9_reps := by
  exact PairwiseNonMulEquiv.of_invariant order72_c9_invariant
    (fun _ _ h => order72_c9_invariant_eq_of_mulEquiv h)
    (fun i j h _ =>
      order72_c9_invariant_table_injective (by
        rw [← order72_c9_invariant_spec i, ← order72_c9_invariant_spec j]
        exact h))

end Smallgroups.UsefulTheorems
