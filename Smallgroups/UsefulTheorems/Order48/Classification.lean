/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.DistinctnessNormal
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeDistinctness
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeCocycles
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeActionClassifiers
import Smallgroups.UsefulTheorems.Order48.SixteenSylowThree

/-!
# The completed non-residual branches of order `48`

The Sylow trichotomy leaves three cases.  The `n₃ = 4` case is deliberately
not included here: its eight representatives are constructed in
`FourSylowThreeReps.lean`, while the cocycle exhaustiveness over the three
order-`24` quotients is still a separate problem.

This file packages the two completed branches into one dependent `44`-entry family:
`42` groups with a unique Sylow `3`-subgroup and the two groups with sixteen
Sylow `3`-subgroups.  The indexing is structural and has no GAP-number
interpretation.
-/

namespace Smallgroups.UsefulTheorems

open Sylow

private theorem order48_card_sylow_three_eq_one_of_normal
    {H : Type*} [Group H] [Finite H] (hH : Nat.card H = 48)
    (N : Subgroup H) (hNorm : N.Normal) (hN : Nat.card N = 3) :
    Nat.card (Sylow 3 H) = 1 := by
  letI := hNorm
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hp : IsPGroup 3 N := IsPGroup.of_card (by rw [hN, pow_one])
  obtain ⟨P, hNP⟩ := hp.exists_le_sylow
  have hP : Nat.card (P : Subgroup H) = 3 :=
    card_sylow_three_subgroup_of_card_48 hH P
  have hNP' : N = (P : Subgroup H) :=
    Subgroup.eq_of_le_of_card_ge hNP (by rw [hN, hP])
  have hPnormal : (P : Subgroup H).Normal := by
    rw [← hNP']
    infer_instance
  haveI := Sylow.unique_of_normal P hPnormal
  exact Nat.card_unique

private theorem order48_normal_sigma_reps_sylow_three
    (x : Σ k : Fin 14, Fin (order48_normal_counts k)) :
    Nat.card (Sylow 3 (order48_normal_sigma_reps x)) = 1 := by
  obtain ⟨k, i⟩ := x
  change Nat.card (Sylow 3 (order48_normal_reps k i)) = 1
  letI : Finite (order48_normal_reps k i) :=
    Nat.finite_of_card_ne_zero (by
      rw [order48_normal_reps_card]
      norm_num)
  have hNorm : (SemidirectProduct.inl (φ :=
      order48_action (order48_normal_chi k i))).range.Normal := by
    rw [SemidirectProduct.range_inl_eq_ker_rightHom
      (φ := order48_action (order48_normal_chi k i))]
    exact MonoidHom.normal_ker _
  have hrange : Nat.card (SemidirectProduct.inl (φ :=
      order48_action (order48_normal_chi k i))).range = 3 := by
    rw [← Nat.card_congr
      (MonoidHom.ofInjective SemidirectProduct.inl_injective).toEquiv]
    exact order48_normal_c3_card
  exact order48_card_sylow_three_eq_one_of_normal
    (H := order48_normal_reps k i)
    (N := (SemidirectProduct.inl (φ :=
      order48_action (order48_normal_chi k i))).range)
    (order48_normal_reps_card k i) hNorm hrange

/-! ### The two representatives in the sixteen-Sylow branch -/

abbrev order48_sixteen_reps (i : Fin 1 ⊕ Fin 1) : Type :=
  Sum.elim (fun _ : Fin 1 => order48_c2pow4_semidirect_c3_rep)
    (fun _ : Fin 1 => order48_c4c4_semidirect_c3_rep) i

theorem order48_sixteen_reps_card (i : Fin 1 ⊕ Fin 1) :
    Nat.card (order48_sixteen_reps i) = 48 := by
  cases i with
  | inl i => exact order48_c2pow4_rep_card
  | inr i => exact order48_c4c4_rep_card

theorem order48_sixteen_reps_sylow_three (i : Fin 1 ⊕ Fin 1) :
    Nat.card (Sylow 3 (order48_sixteen_reps i)) = 16 := by
  cases i with
  | inl i => exact order48_c2pow4_rep_sylow_three
  | inr i => exact order48_c4c4_rep_sylow_three

theorem order48_sixteen_reps_pairwise :
    PairwiseNonMulEquiv order48_sixteen_reps := by
  rintro (i | i) (j | j) hiso
  · exact congrArg Sum.inl (Subsingleton.elim i j)
  · let e := hiso.some
    apply (order48_two_reps_not_iso ⟨
      { toFun := e, invFun := e.symm
        left_inv := e.left_inv, right_inv := e.right_inv
        map_mul' := e.map_mul }⟩).elim
  · let e := hiso.some.symm
    apply (order48_two_reps_not_iso ⟨
      { toFun := e, invFun := e.symm
        left_inv := e.left_inv, right_inv := e.right_inv
        map_mul' := e.map_mul }⟩).elim
  · exact congrArg Sum.inr (Subsingleton.elim i j)

private theorem order48_nonfour_normal_disjoint_sixteen
    (x : Σ k : Fin 14, Fin (order48_normal_counts k)) (j : Fin 1 ⊕ Fin 1) :
    ¬ Nonempty (order48_normal_sigma_reps x ≃* order48_sixteen_reps j) := by
  rintro ⟨e⟩
  have h := card_sylow_of_mulEquiv 3 e
  rw [order48_normal_sigma_reps_sylow_three x,
    order48_sixteen_reps_sylow_three j] at h
  norm_num at h

abbrev order48_nonfour_reps :
    ((Σ k : Fin 14, Fin (order48_normal_counts k)) ⊕ (Fin 1 ⊕ Fin 1)) → Type :=
  Sum.elim order48_normal_sigma_reps order48_sixteen_reps

theorem order48_nonfour_reps_card
    (i : (Σ k : Fin 14, Fin (order48_normal_counts k)) ⊕ (Fin 1 ⊕ Fin 1)) :
    Nat.card (order48_nonfour_reps i) = 48 := by
  cases i with
  | inl x => exact order48_normal_sigma_reps_card x
  | inr x => exact order48_sixteen_reps_card x

theorem order48_nonfour_reps_pairwise :
    PairwiseNonMulEquiv order48_nonfour_reps := by
  have hs : PairwiseNonMulEquiv
      (Sum.elim order48_normal_sigma_reps order48_sixteen_reps) :=
    PairwiseNonMulEquiv.sum order48_normal_sigma_reps_pairwise
      order48_sixteen_reps_pairwise order48_nonfour_normal_disjoint_sixteen
  exact hs

/-! ### Exhaustiveness of the two completed branches -/

theorem order48_nonfour_classification {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 48)
    (hSyl : Nat.card (Sylow 3 G) = 1 ∨ Nat.card (Sylow 3 G) = 16) :
    ∃ i, Nonempty (G ≃* order48_nonfour_reps i) := by
  rcases hSyl with h1 | h16
  · obtain ⟨x, e⟩ := order48_normal_sigma_reps_complete hG h1
    exact ⟨Sum.inl x, e⟩
  · rcases order48_sixteen_sylow_classification hG h16 with e | e
    · exact ⟨Sum.inr (Sum.inl 0), e⟩
    · exact ⟨Sum.inr (Sum.inr 0), e⟩

theorem order48_nonfour_classCount :
    Nat.card ((Σ k : Fin 14, Fin (order48_normal_counts k)) ⊕ (Fin 1 ⊕ Fin 1)) = 44 := by
  rw [Nat.card_sum, order48_normal_repCount, Nat.card_sum]
  norm_num

/-- The current order-`48` reduction: every group is either one of the `44`
non-residual representatives above, or belongs to the four-Sylow-`3` residual
branch. -/
theorem order48_classification_reduction {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 48) :
    (∃ i, Nonempty (G ≃* order48_nonfour_reps i)) ∨
      Nat.card (Sylow 3 G) = 4 := by
  rcases order48_sylow_trichotomy hG with h1 | h4 | h16
  · obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow 3 G))
    haveI := Sylow.unique_of_normal P (h1 P)
    exact Or.inl (order48_nonfour_classification hG (Or.inl Nat.card_unique))
  · exact Or.inr h4
  · exact Or.inl (order48_nonfour_classification hG (Or.inr h16.1))

/-! ### Final assembly once the three cocycle problems are discharged -/

abbrev order48_all_index :=
  (((Σ k : Fin 14, Fin (order48_normal_counts k)) ⊕ (Fin 1 ⊕ Fin 1)) ⊕ Fin 8)

abbrev order48_all_reps : order48_all_index → Type :=
  Sum.elim order48_nonfour_reps order48_four_residualKnownReps

theorem order48_all_reps_card (i : order48_all_index) :
    Nat.card (order48_all_reps i) = 48 := by
  cases i with
  | inl i => exact order48_nonfour_reps_card i
  | inr i => exact card_order48_four_residualKnownReps i

private theorem order48_nonfour_residual_disjoint
    (i : (Σ k : Fin 14, Fin (order48_normal_counts k)) ⊕ (Fin 1 ⊕ Fin 1))
    (j : Fin 8) :
    ¬ Nonempty (order48_nonfour_reps i ≃*
      order48_four_residualKnownReps j) := by
  rintro ⟨e⟩
  have h := card_sylow_of_mulEquiv 3 e
  cases i with
  | inl x =>
      change Nat.card (Sylow 3 (order48_normal_sigma_reps x)) = _ at h
      rw [order48_normal_sigma_reps_sylow_three x,
        card_sylow_three_order48_four_residualKnownReps j] at h
      omega
  | inr x =>
      change Nat.card (Sylow 3 (order48_sixteen_reps x)) = _ at h
      rw [order48_sixteen_reps_sylow_three x,
        card_sylow_three_order48_four_residualKnownReps j] at h
      omega

theorem order48_all_reps_pairwise : PairwiseNonMulEquiv order48_all_reps := by
  exact PairwiseNonMulEquiv.sum order48_nonfour_reps_pairwise
    order48_four_residualKnownReps_pairwise order48_nonfour_residual_disjoint

theorem order48_all_classCount :
    Nat.card order48_all_index = 52 := by
  rw [Nat.card_sum, order48_nonfour_classCount, Nat.card_eq_fintype_card]
  decide

theorem order48_complete_of_cocycle_exhaustive
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 48)
    (hRM : Order48FourCocycleExhaustive order24_RM)
    (hRN : Order48FourCocycleExhaustive order24_RN)
    (hRO : Order48FourCocycleExhaustive order24_RO) :
    ∃ i, Nonempty (G ≃* order48_all_reps i) := by
  rcases order48_sylow_trichotomy hG with h1 | h4 | h16
  · obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow 3 G))
    haveI := Sylow.unique_of_normal P (h1 P)
    obtain ⟨i, e⟩ := order48_nonfour_classification hG (Or.inl Nat.card_unique)
    exact ⟨Sum.inl i, e⟩
  · obtain ⟨i, e⟩ := order48_four_sylow_three_classification_of_cocycle_exhaustive
      hG h4 hRM hRN hRO
    exact ⟨Sum.inr i, e⟩
  · obtain ⟨i, e⟩ := order48_nonfour_classification hG (Or.inr h16.1)
    exact ⟨Sum.inl i, e⟩

noncomputable def order48_all_reps_fin
    (i : Fin (Fintype.card order48_all_index)) : Type :=
  order48_all_reps ((Fintype.equivFin _).symm i)

noncomputable instance order48_all_reps_fin_group
    (i : Fin (Fintype.card order48_all_index)) :
    Group (order48_all_reps_fin i) := by
  change Group (order48_all_reps ((Fintype.equivFin _).symm i))
  infer_instance

theorem order48_all_reps_fin_card
    (i : Fin (Fintype.card order48_all_index)) :
    Nat.card (order48_all_reps_fin i) = 48 :=
  order48_all_reps_card _

theorem order48_all_reps_fin_pairwise :
    PairwiseNonMulEquiv order48_all_reps_fin := by
  intro i j h
  apply (Fintype.equivFin order48_all_index).symm.injective
  apply order48_all_reps_pairwise
    ((Fintype.equivFin order48_all_index).symm i)
    ((Fintype.equivFin order48_all_index).symm j)
  change Nonempty (order48_all_reps_fin i ≃* order48_all_reps_fin j) at h
  exact h

theorem order48_isClassif_of_cocycle_exhaustive
    (hRM : Order48FourCocycleExhaustive order24_RM)
    (hRN : Order48FourCocycleExhaustive order24_RN)
    (hRO : Order48FourCocycleExhaustive order24_RO) :
    IsClassif 48 order48_all_reps_fin where
  card := order48_all_reps_fin_card
  complete := by
    intro G _ hG
    letI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
    obtain ⟨i, e⟩ := order48_complete_of_cocycle_exhaustive hG hRM hRN hRO
    exact ⟨Fintype.equivFin _ i, by
      change Nonempty (G ≃* order48_all_reps
        ((Fintype.equivFin order48_all_index).symm
          ((Fintype.equivFin order48_all_index) i)))
      rw [Equiv.symm_apply_apply]
      exact e⟩
  distinct := order48_all_reps_fin_pairwise

/-! ### Final interface in terms of the remaining finite action problems -/

/-- The complete order-`48` classification follows from the two compatible
`C₃`-action orbit problems over `RM` and `RN`, together with the `RO` cocycle
problem.  The action hypotheses only quantify over the four-Sylow-`3` branch,
which is exactly the branch produced by the cocycle reductions. -/
theorem order48_isClassif_of_action_complete
    (hRM : Order48RMWildActionComplete)
    (hRN : Order48RNWildActionComplete)
    (hRO : Order48FourCocycleExhaustive order24_RO) :
    IsClassif 48 order48_all_reps_fin := by
  exact order48_isClassif_of_cocycle_exhaustive
    (order48_RM_cocycle_exhaustive_of_wild_action_complete hRM)
    (order48_RN_cocycle_exhaustive_of_wild_action_complete hRN)
    hRO

end Smallgroups.UsefulTheorems
