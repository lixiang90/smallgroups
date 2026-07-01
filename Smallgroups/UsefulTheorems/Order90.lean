/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order2PQ
import Smallgroups.UsefulTheorems.PrimeSqPrimeAbelian
import Smallgroups.UsefulTheorems.SchurZassenhaus
import Mathlib.Tactic.NormNum.Prime

/-!
# First structural reductions for groups of order 90

The order `90 = 2 * 45` has odd half-order.  The sign of the left regular action
therefore gives an index-two normal subgroup, and Schur--Zassenhaus splits over it.
-/

namespace Smallgroups.UsefulTheorems

open Subgroup

variable {G : Type*} [Group G]

private lemma order90_sign_mulLeft_of_orderOf_two [Fintype G] [DecidableEq G]
    (a : G) (ha : orderOf a = 2) (hcard : Odd (Nat.card G / 2)) :
    Equiv.Perm.sign (Equiv.mulLeft a) = -1 := by
  classical
  have ha2 : a ^ 2 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, ha]
  have hperm2 : (Equiv.mulLeft a : Equiv.Perm G) ^ 2 = 1 := by
    ext x
    change a * (a * x) = x
    rw [← mul_assoc, ← pow_two, ha2, one_mul]
  rw [Equiv.Perm.sign_of_pow_two_eq_one hperm2]
  have hfixed : Fintype.card (Function.fixedPoints (Equiv.mulLeft a : Equiv.Perm G)) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    rintro ⟨x, hx⟩
    have : a * x = x := hx
    have ha1 : a = 1 := by
      simpa using congr_arg (fun y => y * x⁻¹) this
    have : orderOf a = 1 := by simp [ha1]
    omega
  rw [hfixed, tsub_zero]
  rw [Nat.card_eq_fintype_card] at hcard
  exact hcard.neg_one_pow

/-- Every group of order `90` has a normal subgroup of order `45`. -/
theorem order90_normal_45_subgroup [Finite G] (hG : Nat.card G = 90) :
    ∃ N : Subgroup G, N.Normal ∧ Nat.card N = 45 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  let χ : G →* ℤˣ := Equiv.Perm.sign.comp (MulAction.toPermHom G G)
  have hGft : Fintype.card G = 90 := by
    simpa [Nat.card_eq_fintype_card] using hG
  have hhalf : Nat.card G / 2 = 45 := by
    rw [Nat.card_eq_fintype_card, hGft]
  have hhalfodd : Odd (Nat.card G / 2) := by
    rw [hhalf]
    exact ⟨22, by norm_num⟩
  have htwo_dvd : 2 ∣ Nat.card G := by
    rw [hG]
    norm_num
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 htwo_dvd
  have hχa : χ a = -1 := by
    change Equiv.Perm.sign (MulAction.toPermHom G G a) = -1
    have hperm : MulAction.toPermHom G G a = Equiv.mulLeft a := by
      ext x
      rfl
    rw [hperm]
    exact order90_sign_mulLeft_of_orderOf_two a ha hhalfodd
  have hχsurj : Function.Surjective χ := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one χ⟩
    · exact ⟨a, hχa⟩
  have hindex : χ.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective χ hχsurj]
    simp [Nat.card_eq_fintype_card, Fintype.card_units_int]
  have hNcard : Nat.card χ.ker = 45 := by
    have hmul : Nat.card χ.ker * 2 = Nat.card G := by
      simpa [hindex] using χ.ker.card_mul_index
    apply Nat.mul_right_cancel (m := 2) (by norm_num : 0 < 2)
    rw [hmul, hG]
  exact ⟨χ.ker, inferInstance, hNcard⟩

/-- Every group of order `90` is a semidirect product of a normal group of order `45`
by a complement of order `2`. -/
theorem order90_semidirect [Finite G] (hG : Nat.card G = 90) :
    ∃ (N : Subgroup G) (_ : N.Normal) (_ : Nat.card N = 45)
      (K : Subgroup G) (φ : K →* MulAut N),
      Nonempty (G ≃* SemidirectProduct N K φ) := by
  obtain ⟨N, hNnormal, hNcard⟩ := order90_normal_45_subgroup hG
  haveI : N.Normal := hNnormal
  have hcop : Nat.Coprime 45 2 := by norm_num
  have hcard : Nat.card G = 45 * 2 := by
    norm_num [hG]
  obtain ⟨K, φ, hiso⟩ := schurZassenhaus_of_card hcard hcop N hNcard
  exact ⟨N, hNnormal, hNcard, K, φ, hiso⟩

/-- The index-two kernel in the order-`90` split is one of the two groups of order `45`. -/
theorem order90_semidirect_kernel_cases [Finite G] (hG : Nat.card G = 90) :
    ∃ (N : Subgroup G) (_ : N.Normal) (_ : Nat.card N = 45)
      (K : Subgroup G) (φ : K →* MulAut N),
      Nonempty (G ≃* SemidirectProduct N K φ) ∧
        (Nonempty (N ≃* psqPrimeRep1 3 5) ∨ Nonempty (N ≃* psqPrimeRep2 3 5)) := by
  obtain ⟨N, hNnormal, hNcard, K, φ, hiso⟩ := order90_semidirect hG
  haveI : Finite N := inferInstance
  have hNcard' : Nat.card N = 3 ^ 2 * 5 := by
    rw [hNcard]
    norm_num
  have hcases :
      Nonempty (N ≃* psqPrimeRep1 3 5) ∨ Nonempty (N ≃* psqPrimeRep2 3 5) :=
    psq_prime_abelian_classification (G := N) (p := 3) (q := 5) (by norm_num)
      (by norm_num) (by norm_num) (by decide) (by decide) hNcard'
  exact ⟨N, hNnormal, hNcard, K, φ, hiso, hcases⟩

end Smallgroups.UsefulTheorems
