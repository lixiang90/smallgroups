/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order72.Classification
import Smallgroups.UsefulTheorems.Order72.DistinctnessE9
import Smallgroups.UsefulTheorems.Order72.DistinctnessResidual

namespace Smallgroups.UsefulTheorems

/-!
# Order-72 distinctness assembly

This file finishes the distinctness proof for the fifty representatives of the groups
of order `72`.  The branch-internal proofs are in `DistinctnessDirect`, `DistinctnessC9`,
`DistinctnessE9`, `DistinctnessSylow2` and `DistinctnessResidual`; here we compute the
global invariant table for all fifty representatives, separate the five bookkeeping
branches with it, and concatenate by `PairwiseNonMulEquiv.sigma` (through
`order72_reps_pairwise_of_e9_residual_branch_data`).
-/

local instance instFintypeOrder72AllSemidirectProduct
    {N H : Type*} [Group N] [Group H] [Fintype N] [Fintype H] (φ : H →* MulAut N) :
    Fintype (SemidirectProduct N H φ) :=
  Fintype.ofEquiv (N × H) SemidirectProduct.equivProd.symm

/-- Decidable equality on semidirect products (via the underlying product). -/
local instance instDecEqOrder72AllSemidirectProduct
    {N H : Type*} [Group N] [Group H] [DecidableEq N] [DecidableEq H] (φ : H →* MulAut N) :
    DecidableEq (SemidirectProduct N H φ) :=
  fun a b => decidable_of_iff (SemidirectProduct.equivProd a = SemidirectProduct.equivProd b)
    (Equiv.apply_eq_iff_eq SemidirectProduct.equivProd)

/-- The values of `order72_reps_invariant` for all fifty representatives, computed by
kernel reduction. -/
def order72_global_invariant_table : Fin 50 → Order72Invariant
  | 0 => (72, 2, 3, 4, 6, 8, 9, 12, 18, 24)
  | 1 => (72, 4, 3, 8, 12, 8, 9, 24, 36, 24)
  | 2 => (72, 8, 3, 8, 24, 8, 9, 24, 72, 24)
  | 3 => (18, 6, 3, 8, 18, 8, 9, 24, 54, 24)
  | 4 => (18, 2, 3, 8, 6, 8, 9, 24, 18, 24)
  | 5 => (72, 2, 9, 4, 18, 8, 9, 36, 18, 72)
  | 6 => (72, 4, 9, 8, 36, 8, 9, 72, 36, 72)
  | 7 => (72, 8, 9, 8, 72, 8, 9, 72, 72, 72)
  | 8 => (18, 6, 9, 8, 54, 8, 9, 72, 54, 72)
  | 9 => (18, 2, 9, 8, 18, 8, 9, 72, 18, 72)
  | 10 => (4, 2, 3, 4, 6, 40, 9, 12, 18, 48)
  | 11 => (4, 4, 3, 40, 12, 40, 9, 48, 36, 48)
  | 12 => (4, 20, 3, 40, 24, 40, 9, 48, 36, 48)
  | 13 => (4, 40, 3, 40, 48, 40, 9, 48, 72, 48)
  | 14 => (2, 2, 3, 40, 6, 40, 9, 48, 18, 48)
  | 15 => (2, 22, 3, 40, 30, 40, 9, 48, 54, 48)
  | 16 => (2, 38, 3, 40, 42, 40, 9, 48, 54, 48)
  | 17 => (4, 2, 9, 4, 18, 40, 9, 36, 18, 72)
  | 18 => (12, 2, 9, 4, 18, 16, 9, 36, 18, 72)
  | 19 => (2, 2, 9, 20, 18, 56, 9, 36, 18, 72)
  | 20 => (1, 10, 9, 28, 18, 64, 9, 36, 18, 72)
  | 21 => (4, 4, 9, 40, 36, 40, 9, 72, 36, 72)
  | 22 => (4, 20, 9, 40, 36, 40, 9, 72, 36, 72)
  | 23 => (12, 4, 9, 16, 36, 16, 9, 72, 36, 72)
  | 24 => (12, 8, 9, 16, 36, 16, 9, 72, 36, 72)
  | 25 => (2, 8, 9, 32, 36, 32, 9, 72, 36, 72)
  | 26 => (2, 20, 9, 32, 36, 32, 9, 72, 36, 72)
  | 27 => (2, 20, 9, 56, 36, 56, 9, 72, 36, 72)
  | 28 => (4, 40, 9, 40, 72, 40, 9, 72, 72, 72)
  | 29 => (12, 16, 9, 16, 72, 16, 9, 72, 72, 72)
  | 30 => (2, 32, 9, 32, 72, 32, 9, 72, 72, 72)
  | 31 => (2, 2, 9, 40, 18, 40, 9, 72, 18, 72)
  | 32 => (6, 2, 9, 16, 18, 16, 9, 72, 18, 72)
  | 33 => (2, 2, 9, 32, 18, 32, 9, 72, 18, 72)
  | 34 => (1, 10, 9, 64, 18, 64, 9, 72, 18, 72)
  | 35 => (2, 38, 9, 40, 54, 40, 9, 72, 54, 72)
  | 36 => (6, 14, 9, 16, 54, 16, 9, 72, 54, 72)
  | 37 => (2, 22, 9, 40, 54, 40, 9, 72, 54, 72)
  | 38 => (6, 10, 9, 16, 54, 16, 9, 72, 54, 72)
  | 39 => (2, 14, 9, 32, 54, 32, 9, 72, 54, 72)
  | 40 => (2, 26, 9, 32, 54, 32, 9, 72, 54, 72)
  | 41 => (1, 22, 9, 40, 54, 40, 9, 72, 54, 72)
  | 42 => (6, 2, 3, 8, 6, 8, 27, 24, 54, 24)
  | 43 => (6, 2, 27, 8, 54, 8, 27, 72, 54, 72)
  | 44 => (6, 8, 3, 8, 24, 8, 27, 24, 72, 24)
  | 45 => (6, 8, 27, 8, 72, 8, 27, 72, 72, 72)
  | 46 => (1, 22, 3, 40, 30, 40, 27, 48, 54, 48)
  | 47 => (3, 10, 27, 16, 54, 16, 27, 72, 54, 72)
  | 48 => (1, 22, 27, 40, 54, 40, 27, 72, 54, 72)
  | 49 => (1, 16, 27, 16, 72, 16, 27, 72, 72, 72)
  | ⟨n + 50, h⟩ => by omega

set_option maxHeartbeats 2000000 in
-- Finite kernel computation over representatives 0–9.
theorem order72_direct_invariant_spec10 :
    order72_reps_invariant 0 = order72_global_invariant_table 0 ∧
      order72_reps_invariant 1 = order72_global_invariant_table 1 ∧
      order72_reps_invariant 2 = order72_global_invariant_table 2 ∧
      order72_reps_invariant 3 = order72_global_invariant_table 3 ∧
      order72_reps_invariant 4 = order72_global_invariant_table 4 ∧
      order72_reps_invariant 5 = order72_global_invariant_table 5 ∧
      order72_reps_invariant 6 = order72_global_invariant_table 6 ∧
      order72_reps_invariant 7 = order72_global_invariant_table 7 ∧
      order72_reps_invariant 8 = order72_global_invariant_table 8 ∧
      order72_reps_invariant 9 = order72_global_invariant_table 9 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [order72_reps_invariant, order72_global_invariant_table, order72_reps,
      order72_pow_eq_one_card, Nat.card_eq_fintype_card]
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
-- Finite kernel computation over representatives 42–45.
theorem order72_sylow2_invariant_spec4 :
    order72_reps_invariant 42 = order72_global_invariant_table 42 ∧
      order72_reps_invariant 43 = order72_global_invariant_table 43 ∧
      order72_reps_invariant 44 = order72_global_invariant_table 44 ∧
      order72_reps_invariant 45 = order72_global_invariant_table 45 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [order72_reps_invariant, order72_global_invariant_table, order72_reps,
      order72_pow_eq_one_card, Nat.card_eq_fintype_card]
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

/-- The invariant values agree with the global table at every index. -/
theorem order72_global_invariant_spec (i : Fin 50) :
    order72_reps_invariant i = order72_global_invariant_table i := by
  fin_cases i
  · exact order72_direct_invariant_spec10.1
  · exact order72_direct_invariant_spec10.2.1
  · exact order72_direct_invariant_spec10.2.2.1
  · exact order72_direct_invariant_spec10.2.2.2.1
  · exact order72_direct_invariant_spec10.2.2.2.2.1
  · exact order72_direct_invariant_spec10.2.2.2.2.2.1
  · exact order72_direct_invariant_spec10.2.2.2.2.2.2.1
  · exact order72_direct_invariant_spec10.2.2.2.2.2.2.2.1
  · exact order72_direct_invariant_spec10.2.2.2.2.2.2.2.2.1
  · exact order72_direct_invariant_spec10.2.2.2.2.2.2.2.2.2
  · exact order72_c9_invariant_spec 0
  · exact order72_c9_invariant_spec 1
  · exact order72_c9_invariant_spec 2
  · exact order72_c9_invariant_spec 3
  · exact order72_c9_invariant_spec 4
  · exact order72_c9_invariant_spec 5
  · exact order72_c9_invariant_spec 6
  · exact order72_e9_invariant_spec 0
  · exact order72_e9_invariant_spec 1
  · exact order72_e9_invariant_spec 2
  · exact order72_e9_invariant_spec 3
  · exact order72_e9_invariant_spec 4
  · exact order72_e9_invariant_spec 5
  · exact order72_e9_invariant_spec 6
  · exact order72_e9_invariant_spec 7
  · exact order72_e9_invariant_spec 8
  · exact order72_e9_invariant_spec 9
  · exact order72_e9_invariant_spec 10
  · exact order72_e9_invariant_spec 11
  · exact order72_e9_invariant_spec 12
  · exact order72_e9_invariant_spec 13
  · exact order72_e9_invariant_spec 14
  · exact order72_e9_invariant_spec 15
  · exact order72_e9_invariant_spec 16
  · exact order72_e9_invariant_spec 17
  · exact order72_e9_invariant_spec 18
  · exact order72_e9_invariant_spec 19
  · exact order72_e9_invariant_spec 20
  · exact order72_e9_invariant_spec 21
  · exact order72_e9_invariant_spec 22
  · exact order72_e9_invariant_spec 23
  · exact order72_e9_invariant_spec 24
  · exact order72_sylow2_invariant_spec4.1
  · exact order72_sylow2_invariant_spec4.2.1
  · exact order72_sylow2_invariant_spec4.2.2.1
  · exact order72_sylow2_invariant_spec4.2.2.2
  · exact order72_residual_invariant_spec 0
  · exact order72_residual_invariant_spec 1
  · exact order72_residual_invariant_spec 2
  · exact order72_residual_invariant_spec 3

/-- The branchwise invariant agrees with the global table. -/
theorem order72_branch_invariant_spec (b : Order72Branch) (i : order72_branch_index b) :
    order72_branch_invariant b i = order72_global_invariant_table (order72_branch_to_fin b i) :=
  order72_global_invariant_spec (order72_branch_to_fin b i)

set_option maxHeartbeats 2000000 in
-- The global invariant table is injective (finite check over the `50 × 50` index pairs).
theorem order72_global_invariant_table_injective :
    Function.Injective order72_global_invariant_table := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [order72_global_invariant_table] at h ⊢

/-- Indices from different bookkeeping branches occupy disjoint segments of `Fin 50`. -/
theorem order72_branch_to_fin_ne_of_ne (b₁ b₂ : Order72Branch) (hne : b₁ ≠ b₂)
    (i : order72_branch_index b₁) (j : order72_branch_index b₂) :
    order72_branch_to_fin b₁ i ≠ order72_branch_to_fin b₂ j := by
  intro h
  cases b₁ <;> cases b₂
  all_goals first
    | exact absurd rfl hne
    | (simp only [order72_branch_to_fin] at h
       rw [Fin.mk.injEq] at h
       have := i.isLt
       have := j.isLt
       omega)

/-- Distinct bookkeeping branches have disjoint invariant values. -/
theorem order72_cross_branch_sep (b₁ b₂ : Order72Branch) (hne : b₁ ≠ b₂)
    (i : order72_branch_index b₁) (j : order72_branch_index b₂) :
    order72_branch_invariant b₁ i ≠ order72_branch_invariant b₂ j := by
  intro h
  rw [order72_branch_invariant_spec, order72_branch_invariant_spec] at h
  exact order72_branch_to_fin_ne_of_ne b₁ b₂ hne i j
    (order72_global_invariant_table_injective h)

/-- Cross-branch disjointness from the invariant separation. -/
theorem order72_cross_branch_disjoint (b₁ b₂ : Order72Branch) (hne : b₁ ≠ b₂)
    (i : order72_branch_index b₁) (j : order72_branch_index b₂) :
    ¬ Nonempty (order72_branch_reps b₁ i ≃* order72_branch_reps b₂ j) :=
  order72_cross_branch_disjoint_of_invariant_ne order72_cross_branch_sep b₁ b₂ hne i j

/-- The `E9`-kernel semidirect branch is pairwise non-isomorphic (bridge). -/
theorem order72_e9_branch_pairwise :
    PairwiseNonMulEquiv (order72_branch_reps .e9) := by
  intro i j hiso
  fin_cases i <;> fin_cases j <;>
    exact order72_e9_reps_pairwise _ _ hiso

/-- The residual branch is pairwise non-isomorphic (bridge). -/
theorem order72_residual_branch_pairwise :
    PairwiseNonMulEquiv (order72_branch_reps .residual) := by
  intro i j hiso
  fin_cases i <;> fin_cases j <;>
    exact order72_residual_reps_pairwise _ _ hiso

/-- The fifty representatives of the groups of order `72` are pairwise non-isomorphic. -/
theorem order72_reps_pairwise : PairwiseNonMulEquiv order72_reps :=
  order72_reps_pairwise_of_e9_residual_branch_data
    order72_e9_branch_pairwise order72_residual_branch_pairwise
    (fun b₁ b₂ hne i j => order72_cross_branch_disjoint b₁ b₂ hne i j)

/-- **The classification of groups of order 72**: the fifty representatives have
cardinality `72`, every group of order `72` is isomorphic to one of them, and they are
pairwise non-isomorphic. -/
theorem order72_isClassif : IsClassif 72 order72_reps :=
  order72_isClassif_of_pairwise order72_reps_pairwise

end Smallgroups.UsefulTheorems
