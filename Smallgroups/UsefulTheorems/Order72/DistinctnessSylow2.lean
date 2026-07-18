/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order72.H8xP9
import Smallgroups.UsefulTheorems.Order72.DistinctnessDirect
import Smallgroups.UsefulTheorems.Counting
import Smallgroups.UsefulTheorems.PrimeSqClassification

namespace Smallgroups.UsefulTheorems

/-! # Sylow-2-normal semidirect branch distinctness for groups of order 72 -/

/-- The four nontrivial Sylow-`2`-normal semidirect products in the order-72 list. -/
noncomputable abbrev order72_sylow2_reps : Fin 4 → Type
  | 0 => order72_Q8_C9_cyc
  | 1 => order72_Q8_E9_cyc
  | 2 => order72_E8_C9_rot
  | 3 => order72_E8_E9_rot

noncomputable instance order72_sylow2_reps_group :
    (i : Fin 4) → Group (order72_sylow2_reps i)
  | 0 => inferInstance
  | 1 => inferInstance
  | 2 => inferInstance
  | 3 => inferInstance
  | ⟨n + 4, h⟩ => by omega

theorem order72_C9_not_mulEquiv_E9 :
    ¬ Nonempty (CyclicRep 9 ≃* ElemAbelianRep 3) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  simpa using (prime_sq_distinct (p := 3))

theorem order72_E9_not_mulEquiv_C9 :
    ¬ Nonempty (ElemAbelianRep 3 ≃* CyclicRep 9) := by
  rintro ⟨e⟩
  exact order72_C9_not_mulEquiv_E9 ⟨e.symm⟩

theorem order72_Q8_not_mulEquiv_E8 :
    ¬ Nonempty (QuaternionGroup 2 ≃* E8) := by
  rintro ⟨e⟩
  have hQ : order72_direct_pow_eq_one_card (QuaternionGroup 2) 2 = 2 := by
    simp only [order72_direct_pow_eq_one_card, Nat.card_eq_fintype_card]
    decide +kernel
  have hE : order72_direct_pow_eq_one_card E8 2 = 8 := by
    simp only [order72_direct_pow_eq_one_card, Nat.card_eq_fintype_card]
    decide +kernel
  have h := order72_direct_pow_eq_one_card_eq_of_mulEquiv 2 e
  rw [hQ, hE] at h
  norm_num at h

theorem order72_E8_not_mulEquiv_Q8 :
    ¬ Nonempty (E8 ≃* QuaternionGroup 2) := by
  rintro ⟨e⟩
  exact order72_Q8_not_mulEquiv_E8 ⟨e.symm⟩

theorem order72_Q8_C9_cyc_not_Q8_E9_cyc :
    ¬ Nonempty (order72_Q8_C9_cyc ≃* order72_Q8_E9_cyc) := by
  rintro ⟨e⟩
  exact order72_C9_not_mulEquiv_E9
    (semidirectProduct_congr_range
      (N := QuaternionGroup 2) (H1 := CyclicRep 9) (H2 := ElemAbelianRep 3)
      (φ1 := q8CycActionC9) (φ2 := q8CycActionE9)
      (by rw [card_order72_Q8, card_order72_E9]; norm_num) e)

theorem order72_Q8_E9_cyc_not_Q8_C9_cyc :
    ¬ Nonempty (order72_Q8_E9_cyc ≃* order72_Q8_C9_cyc) := by
  rintro ⟨e⟩
  exact order72_Q8_C9_cyc_not_Q8_E9_cyc ⟨e.symm⟩

theorem order72_E8_C9_rot_not_E8_E9_rot :
    ¬ Nonempty (order72_E8_C9_rot ≃* order72_E8_E9_rot) := by
  rintro ⟨e⟩
  exact order72_C9_not_mulEquiv_E9
    (semidirectProduct_congr_range
      (N := E8) (H1 := CyclicRep 9) (H2 := ElemAbelianRep 3)
      (φ1 := e8RotActionC9) (φ2 := e8RotActionE9)
      (by rw [card_order72_E8, card_order72_E9]; norm_num) e)

theorem order72_E8_E9_rot_not_E8_C9_rot :
    ¬ Nonempty (order72_E8_E9_rot ≃* order72_E8_C9_rot) := by
  rintro ⟨e⟩
  exact order72_E8_C9_rot_not_E8_E9_rot ⟨e.symm⟩

theorem order72_Q8_C9_cyc_not_E8_C9_rot :
    ¬ Nonempty (order72_Q8_C9_cyc ≃* order72_E8_C9_rot) := by
  rintro ⟨e⟩
  exact order72_Q8_not_mulEquiv_E8
    (semidirectProduct_congr_domain
      (N1 := QuaternionGroup 2) (N2 := E8) (H1 := CyclicRep 9) (H2 := CyclicRep 9)
      (φ1 := q8CycActionC9) (φ2 := e8RotActionC9)
      (by rw [card_order72_Q8, card_order72_E8])
      (by rw [card_order72_E8, card_order72_C9]; norm_num) e)

theorem order72_E8_C9_rot_not_Q8_C9_cyc :
    ¬ Nonempty (order72_E8_C9_rot ≃* order72_Q8_C9_cyc) := by
  rintro ⟨e⟩
  exact order72_Q8_C9_cyc_not_E8_C9_rot ⟨e.symm⟩

theorem order72_Q8_C9_cyc_not_E8_E9_rot :
    ¬ Nonempty (order72_Q8_C9_cyc ≃* order72_E8_E9_rot) := by
  rintro ⟨e⟩
  exact order72_Q8_not_mulEquiv_E8
    (semidirectProduct_congr_domain
      (N1 := QuaternionGroup 2) (N2 := E8) (H1 := CyclicRep 9) (H2 := ElemAbelianRep 3)
      (φ1 := q8CycActionC9) (φ2 := e8RotActionE9)
      (by rw [card_order72_Q8, card_order72_E8])
      (by rw [card_order72_E8, card_order72_E9]; norm_num) e)

theorem order72_E8_E9_rot_not_Q8_C9_cyc :
    ¬ Nonempty (order72_E8_E9_rot ≃* order72_Q8_C9_cyc) := by
  rintro ⟨e⟩
  exact order72_Q8_C9_cyc_not_E8_E9_rot ⟨e.symm⟩

theorem order72_Q8_E9_cyc_not_E8_C9_rot :
    ¬ Nonempty (order72_Q8_E9_cyc ≃* order72_E8_C9_rot) := by
  rintro ⟨e⟩
  exact order72_Q8_not_mulEquiv_E8
    (semidirectProduct_congr_domain
      (N1 := QuaternionGroup 2) (N2 := E8) (H1 := ElemAbelianRep 3) (H2 := CyclicRep 9)
      (φ1 := q8CycActionE9) (φ2 := e8RotActionC9)
      (by rw [card_order72_Q8, card_order72_E8])
      (by rw [card_order72_E8, card_order72_C9]; norm_num) e)

theorem order72_E8_C9_rot_not_Q8_E9_cyc :
    ¬ Nonempty (order72_E8_C9_rot ≃* order72_Q8_E9_cyc) := by
  rintro ⟨e⟩
  exact order72_Q8_E9_cyc_not_E8_C9_rot ⟨e.symm⟩

theorem order72_Q8_E9_cyc_not_E8_E9_rot :
    ¬ Nonempty (order72_Q8_E9_cyc ≃* order72_E8_E9_rot) := by
  rintro ⟨e⟩
  exact order72_Q8_not_mulEquiv_E8
    (semidirectProduct_congr_domain
      (N1 := QuaternionGroup 2) (N2 := E8) (H1 := ElemAbelianRep 3) (H2 := ElemAbelianRep 3)
      (φ1 := q8CycActionE9) (φ2 := e8RotActionE9)
      (by rw [card_order72_Q8, card_order72_E8])
      (by rw [card_order72_E8, card_order72_E9]; norm_num) e)

theorem order72_E8_E9_rot_not_Q8_E9_cyc :
    ¬ Nonempty (order72_E8_E9_rot ≃* order72_Q8_E9_cyc) := by
  rintro ⟨e⟩
  exact order72_Q8_E9_cyc_not_E8_E9_rot ⟨e.symm⟩

theorem order72_sylow2_reps_pairwise :
    PairwiseNonMulEquiv order72_sylow2_reps := by
  intro i j hiso
  fin_cases i <;> fin_cases j
  · rfl
  · exact False.elim (order72_Q8_C9_cyc_not_Q8_E9_cyc hiso)
  · exact False.elim (order72_Q8_C9_cyc_not_E8_C9_rot hiso)
  · exact False.elim (order72_Q8_C9_cyc_not_E8_E9_rot hiso)
  · exact False.elim (order72_Q8_E9_cyc_not_Q8_C9_cyc hiso)
  · rfl
  · exact False.elim (order72_Q8_E9_cyc_not_E8_C9_rot hiso)
  · exact False.elim (order72_Q8_E9_cyc_not_E8_E9_rot hiso)
  · exact False.elim (order72_E8_C9_rot_not_Q8_C9_cyc hiso)
  · exact False.elim (order72_E8_C9_rot_not_Q8_E9_cyc hiso)
  · rfl
  · exact False.elim (order72_E8_C9_rot_not_E8_E9_rot hiso)
  · exact False.elim (order72_E8_E9_rot_not_Q8_C9_cyc hiso)
  · exact False.elim (order72_E8_E9_rot_not_Q8_E9_cyc hiso)
  · exact False.elim (order72_E8_E9_rot_not_E8_C9_rot hiso)
  · rfl

end Smallgroups.UsefulTheorems
