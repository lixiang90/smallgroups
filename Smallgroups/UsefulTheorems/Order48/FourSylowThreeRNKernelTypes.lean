/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeRN
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeDistinctness

/-!
# Kernel types in the `RN` branch

The normal order-`16` preimage is a central double cover of `Q₈`.  Square-
and fourth-root counts in this quotient leave only `G₁₁` and `G₁₂`.
-/

namespace Smallgroups.UsefulTheorems

@[implicit_reducible]
private noncomputable def order48_RN_repFintype (i : Fin 14) :
    Fintype (order16_wild_reps i) :=
  match i with
  | 0 => inferInstance | 1 => inferInstance | 2 => inferInstance | 3 => inferInstance
  | 4 => inferInstance | 5 => inferInstance | 6 => inferInstance | 7 => inferInstance
  | 8 => inferInstance | 9 => inferInstance | 10 => inferInstance | 11 => inferInstance
  | 12 => inferInstance | 13 => inferInstance

private noncomputable def order48_RN_repDecidableEq (i : Fin 14) :
    DecidableEq (order16_wild_reps i) :=
  match i with
  | 0 => inferInstance | 1 => inferInstance | 2 => inferInstance | 3 => inferInstance
  | 4 => inferInstance | 5 => inferInstance | 6 => inferInstance | 7 => inferInstance
  | 8 => inferInstance | 9 => inferInstance | 10 => inferInstance | 11 => inferInstance
  | 12 => inferInstance | 13 => inferInstance

private noncomputable def order48_RN_kernelCandidate (i : Fin 14) : Prop :=
  letI := order48_RN_repFintype i
  letI := order48_RN_repDecidableEq i
  ∃ z : order16_wild_reps i,
    (∀ y : order16_wild_reps i, z * y = y * z) ∧
    z ^ 2 = 1 ∧ z ≠ 1 ∧
    (Finset.univ.filter (fun x : order16_wild_reps i =>
      x ^ 2 = 1 ∨ x ^ 2 = z)).card = 4 ∧
    (Finset.univ.filter (fun x : order16_wild_reps i =>
      x ^ 4 = 1 ∨ x ^ 4 = z)).card = 16

private noncomputable def order48_RN_kernelCandidate_decidable (i : Fin 14) :
    Decidable (order48_RN_kernelCandidate i) :=
  letI := order48_RN_repFintype i
  letI := order48_RN_repDecidableEq i
  @Fintype.decidableExistsFintype (order16_wild_reps i)
    (fun z => (∀ y : order16_wild_reps i, z * y = y * z) ∧
      z ^ 2 = 1 ∧ z ≠ 1 ∧
      (Finset.univ.filter (fun x : order16_wild_reps i =>
        x ^ 2 = 1 ∨ x ^ 2 = z)).card = 4 ∧
      (Finset.univ.filter (fun x : order16_wild_reps i =>
        x ^ 4 = 1 ∨ x ^ 4 = z)).card = 16)
    (fun z => by
      letI : Decidable (∀ y : order16_wild_reps i, z * y = y * z) :=
        @Fintype.decidableForallFintype (order16_wild_reps i)
          (fun y => z * y = y * z) (fun _ => inferInstance) inferInstance
      infer_instance) inferInstance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Kernel evaluation excludes the seven remaining nonabelian order-16 representatives.
private theorem order48_RN_kernelCandidate_index
    (i : Fin 14) (h : order48_RN_kernelCandidate i)
    (hi : i ≠ 0 ∧ i ≠ 1 ∧ i ≠ 6 ∧ i ≠ 7 ∧ i ≠ 13) :
    i = 11 ∨ i = 12 := by
  fin_cases i <;> simp_all
  all_goals
    exact (@of_decide_eq_false _ (order48_RN_kernelCandidate_decidable _)
      (by decide +kernel)) h

private def order48_RN_pairRootsEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (z : G) (n : ℕ) :
    {x : G // x ^ n = 1 ∨ x ^ n = z} ≃
      {y : H // y ^ n = 1 ∨ y ^ n = e z} where
  toFun x := ⟨e x, by
    rcases x.2 with hx | hx
    · left
      rw [← map_pow, hx, map_one]
    · right
      rw [← map_pow, hx]⟩
  invFun y := ⟨e.symm y, by
    rcases y.2 with hy | hy
    · left
      rw [← map_pow, hy, map_one]
    · right
      rw [← map_pow, hy, e.symm_apply_apply]⟩
  left_inv x := by ext; exact e.symm_apply_apply x
  right_inv y := by ext; exact e.apply_symm_apply y

private theorem order48_RN_kernelCandidate_of_equiv
    (f : order24_RN → order24_RN → ZMod 2) (hf : IsCentralCocycle f)
    (i : Fin 14)
    (eP : order48CocycleTwoPreimage order24_c3ActionQ8 f hf ≃*
      order16_wild_reps i) :
    order48_RN_kernelCandidate i := by
  let P := order48CocycleTwoPreimage order24_c3ActionQ8 f hf
  let z : P := order48CocycleTwoPreimageKernelGenerator
    order24_c3ActionQ8 f hf
  let z' : order16_wild_reps i := eP z
  have hzord : orderOf z = 2 :=
    order_order48CocycleTwoPreimageKernelGenerator order24_c3ActionQ8 f hf
  have hzpow : z ^ 2 = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hzord] at h
  have hzne : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzord
    norm_num at hzord
  let eQ := order48CocycleTwoPreimageQuotientEquiv
    order24_c3ActionQ8 f hf card_order24_Q8
  have hq2 : Nat.card {x : P ⧸ Subgroup.zpowers z // x ^ 2 = 1} = 2 := by
    change pow_eq_one_card (P ⧸ Subgroup.zpowers z) 2 = 2
    rw [pow_eq_one_card_eq_of_mulEquiv 2 eQ, pow_eq_one_card,
      Nat.card_eq_fintype_card]
    decide +kernel
  have hq4 : Nat.card {x : P ⧸ Subgroup.zpowers z // x ^ 4 = 1} = 8 := by
    change pow_eq_one_card (P ⧸ Subgroup.zpowers z) 4 = 8
    rw [pow_eq_one_card_eq_of_mulEquiv 4 eQ, pow_eq_one_card,
      Nat.card_eq_fintype_card]
    decide +kernel
  have hp2 : Nat.card {x : P // x ^ 2 = 1 ∨ x ^ 2 = z} = 4 := by
    have h := card_pow_eq_one_quotient_central_involution (H := P) hzord 2
    rw [hq2] at h
    omega
  have hp4 : Nat.card {x : P // x ^ 4 = 1 ∨ x ^ 4 = z} = 16 := by
    have h := card_pow_eq_one_quotient_central_involution (H := P) hzord 4
    rw [hq4] at h
    omega
  have hz'comm : ∀ y : order16_wild_reps i, z' * y = y * z' := by
    intro y
    obtain ⟨x, rfl⟩ := eP.surjective y
    have hzcenter := order48CocycleTwoPreimageKernelGenerator_mem_center
      order24_c3ActionQ8 f hf
    have hzcomm := (Subgroup.mem_center_iff.mp hzcenter) x
    simpa only [z, z', map_mul] using congrArg eP hzcomm.symm
  have hz'pow : z' ^ 2 = 1 := by
    dsimp [z']
    rw [← map_pow, hzpow, map_one]
  have hz'ne : z' ≠ 1 := by
    intro h
    apply hzne
    apply eP.injective
    exact h.trans eP.map_one.symm
  have hp2' : Nat.card {x : order16_wild_reps i //
      x ^ 2 = 1 ∨ x ^ 2 = z'} = 4 := by
    calc
      Nat.card {x : order16_wild_reps i // x ^ 2 = 1 ∨ x ^ 2 = z'} =
          Nat.card {x : P // x ^ 2 = 1 ∨ x ^ 2 = z} :=
        (Nat.card_congr (order48_RN_pairRootsEquiv eP z 2)).symm
      _ = 4 := hp2
  have hp4' : Nat.card {x : order16_wild_reps i //
      x ^ 4 = 1 ∨ x ^ 4 = z'} = 16 := by
    calc
      Nat.card {x : order16_wild_reps i // x ^ 4 = 1 ∨ x ^ 4 = z'} =
          Nat.card {x : P // x ^ 4 = 1 ∨ x ^ 4 = z} :=
        (Nat.card_congr (order48_RN_pairRootsEquiv eP z 4)).symm
      _ = 16 := hp4
  letI := order48_RN_repFintype i
  letI := order48_RN_repDecidableEq i
  refine ⟨z', hz'comm, hz'pow, hz'ne, ?_, ?_⟩
  · rw [← Fintype.card_subtype]
    simpa only [Nat.card_eq_fintype_card] using hp2'
  · rw [← Fintype.card_subtype]
    simpa only [Nat.card_eq_fintype_card] using hp4'

/-- The normal order-`16` preimage in the `RN` branch is either
`G₁₁ = Q₈ × C₂` or `G₁₂ = C₄ ⋊ C₄`. -/
theorem order48_RN_cocycle_kernel_index_restriction
    (f : order24_RN → order24_RN → ZMod 2) (hf : IsCentralCocycle f)
    (i : Fin 14)
    (eP : order48CocycleTwoPreimage order24_c3ActionQ8 f hf ≃*
      order16_wild_reps i) :
    i = 11 ∨ i = 12 := by
  obtain ⟨i', eP', hi, _⟩ :=
    order48_RN_cocycle_wild_kernel_type_restriction f hf
  have hii : i = i' := order16_wild_distinct
    ⟨eP.symm.trans eP'⟩
  subst i'
  exact order48_RN_kernelCandidate_index i
    (order48_RN_kernelCandidate_of_equiv f hf i eP) hi

end Smallgroups.UsefulTheorems
