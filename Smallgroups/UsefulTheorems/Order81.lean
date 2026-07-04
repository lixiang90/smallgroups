/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Counting
import Smallgroups.UsefulTheorems.OrderP4_Abel
import Smallgroups.UsefulTheorems.OrderP4_NonAbel
import Mathlib.Tactic.NormNum.Prime

/-!
# First structural facts for groups of order `81`

`81 = 3^4`.  The abelian part is already covered by the general classification of abelian
groups of order `p^4`, giving the five groups corresponding to the partitions of `4`.

For the non-abelian part, this file records the first split supplied by the existing
`OrderP4_NonAbel` development: the center has order `3` or `9`, and hence is one of
`C_3`, `C_9`, or `C_3 × C_3`.

This is intentionally not yet a full classification of groups of order `81`: the ten
non-abelian representatives and their distinctness still need a separate development.
-/

namespace Smallgroups.UsefulTheorems

open Subgroup

/-! ## The five abelian representatives -/

/-- The five abelian representatives of order `81`. -/
noncomputable abbrev order81_abelian_reps : Fin 5 → Type :=
  orderP4Abel_reps 3

noncomputable instance instCommGroupOrder81AbelianReps (i : Fin 5) :
    CommGroup (order81_abelian_reps i) :=
  inferInstance

/-- Every abelian representative has order `81`. -/
theorem card_order81_abelian_reps (i : Fin 5) :
    Nat.card (order81_abelian_reps i) = 81 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  dsimp [order81_abelian_reps]
  rw [card_orderP4Abel_reps 3 i]
  norm_num

/-- Every abelian group of order `81` is isomorphic to one of the five abelian representatives. -/
theorem order81_abelian_complete (G : Type*) [CommGroup G] (hcard : Nat.card G = 81) :
    ∃ i, Nonempty (G ≃* order81_abelian_reps i) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  dsimp [order81_abelian_reps]
  exact orderP4Abel_complete 3 G (by rw [hcard]; norm_num)

/-- The five abelian representatives of order `81` are pairwise non-isomorphic. -/
theorem order81_abelian_distinct : PairwiseNonMulEquiv order81_abelian_reps := by
  intro i j h
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  dsimp [order81_abelian_reps] at h ⊢
  exact orderP4Abel_distinct 3 i j h

/-! ## The first non-abelian split -/

/-- In a non-abelian group of order `81`, the center has order `3` or `9`. -/
theorem order81_center_card_eq_three_or_nine {G : Type*} [Group G]
    (hcard : Nat.card G = 81) (hnonab : ¬ (∀ a b : G, a * b = b * a)) :
    Nat.card (center G) = 3 ∨ Nat.card (center G) = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hcard' : Nat.card G = 3 ^ 4 := by
    rw [hcard]
    norm_num
  rcases center_card_eq_p_or_p_sq_of_nonabelian_p4 (p := 3) hcard' hnonab with hcenter | hcenter
  · exact Or.inl hcenter
  · right
    rw [hcenter]
    norm_num

/-- In a non-abelian group of order `81`, the center is `C_3`, `C_9`, or `C_3 × C_3`. -/
theorem order81_center_classification_of_nonabelian {G : Type*} [Group G]
    (hcard : Nat.card G = 81) (hnonab : ¬ (∀ a b : G, a * b = b * a)) :
    Nonempty (center G ≃* CyclicRep 3) ∨
    Nonempty (center G ≃* CyclicRep 9) ∨
    Nonempty (center G ≃* ElemAbelianRep 3) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hcard' : Nat.card G = 3 ^ 4 := by
    rw [hcard]
    norm_num
  simpa using center_classification_of_nonabelian_p4 (p := 3) hcard' hnonab

end Smallgroups.UsefulTheorems
