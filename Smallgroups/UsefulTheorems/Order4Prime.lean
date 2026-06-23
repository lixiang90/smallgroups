/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.SchurZassenhaus
import Smallgroups.UsefulTheorems.PrimeSqClassification
import Smallgroups.UsefulTheorems.SemidirectProductClassify
import Mathlib.GroupTheory.Sylow
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.IntervalCases

/-!
# Groups of order `4 * p`, first reduction

For a prime `p > 4`, the Sylow `p`-subgroup of a group of order `4p` is unique and normal.
Schur--Zassenhaus therefore writes the group as a semidirect product `P ⋊ K`, where `|P| = p`
and `|K| = 4`.

This is the structural starting point for classifying the `4p` orders such as `20`, `28`, `44`,
`52`, `68`, `76`, and `92`.
-/

namespace Smallgroups.UsefulTheorems

open Sylow

variable {G : Type*} [Group G]

/-- For `p > 4`, a group of order `4p` has a unique Sylow `p`-subgroup. -/
theorem card_sylow_p_eq_one_of_card_four_mul_prime {p : ℕ} (hp : p.Prime) (hp4 : 4 < p)
    [Finite G] (hG : Nat.card G = 4 * p) :
    Nat.card (Sylow p G) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow p G))
  have hdvd4p : Nat.card (Sylow p G) ∣ 4 * p :=
    hG ▸ (P0.card_dvd_index.trans (Subgroup.index_dvd_card _))
  have hndvd_p : ¬ p ∣ Nat.card (Sylow p G) := not_dvd_card_sylow p G
  have hcop : Nat.Coprime (Nat.card (Sylow p G)) p :=
    (hp.coprime_iff_not_dvd.mpr hndvd_p).symm
  have hdvd4 : Nat.card (Sylow p G) ∣ 4 :=
    hcop.dvd_of_dvd_mul_left (by rwa [Nat.mul_comm 4 p] at hdvd4p)
  set n := Nat.card (Sylow p G) with hn
  have hnpos : 0 < n := by
    rw [hn]
    exact Nat.card_pos
  have hnle4 : n ≤ 4 := Nat.le_of_dvd (by norm_num) (by simpa [hn] using hdvd4)
  interval_cases n
  · rfl
  · exfalso
    have hmod := card_sylow_modEq_one p G
    rw [← hn] at hmod
    have hpdiv : p ∣ 2 - 1 :=
      (Nat.modEq_iff_dvd' (by norm_num : 1 ≤ 2)).mp hmod.symm
    have hple : p ≤ 1 := Nat.le_of_dvd (by norm_num) hpdiv
    omega
  · exfalso
    have hmod := card_sylow_modEq_one p G
    rw [← hn] at hmod
    have hpdiv : p ∣ 3 - 1 :=
      (Nat.modEq_iff_dvd' (by norm_num : 1 ≤ 3)).mp hmod.symm
    have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpdiv
    omega
  · exfalso
    have hmod := card_sylow_modEq_one p G
    rw [← hn] at hmod
    have hpdiv : p ∣ 4 - 1 :=
      (Nat.modEq_iff_dvd' (by norm_num : 1 ≤ 4)).mp hmod.symm
    have hple : p ≤ 3 := Nat.le_of_dvd (by norm_num) hpdiv
    omega

/-- The Sylow `p`-subgroup is normal in a group of order `4p`, for `p > 4`. -/
theorem sylow_p_normal_of_card_four_mul_prime {p : ℕ} (hp : p.Prime) (hp4 : 4 < p)
    [Finite G] (hG : Nat.card G = 4 * p) (P : Sylow p G) :
    (↑P : Subgroup G).Normal := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Subsingleton (Sylow p G) :=
    (Nat.card_eq_one_iff_unique.mp
      (card_sylow_p_eq_one_of_card_four_mul_prime hp hp4 hG)).1
  exact normal_of_subsingleton P

/-- The Sylow `p`-subgroup of a group of order `4p`, for `p > 4`, has order `p`. -/
theorem card_sylow_p_subgroup_of_card_four_mul_prime {p : ℕ} (hp : p.Prime) (hp4 : 4 < p)
    [Finite G] (hG : Nat.card G = 4 * p) (P : Sylow p G) :
    Nat.card (↑P : Subgroup G) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpndvd4 : ¬ p ∣ 4 := fun h => by
    have hle : p ≤ 4 := Nat.le_of_dvd (by norm_num) h
    omega
  have hfact : (4 * p).factorization p = 1 := by
    rw [Nat.factorization_mul (by norm_num : 4 ≠ 0) hp.ne_zero, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpndvd4, hp.factorization_self, zero_add]
  rw [Sylow.card_eq_multiplicity, hG, hfact, pow_one]

/-- **Schur--Zassenhaus reduction for order `4p`, `p > 4`.** The group splits as a semidirect
product `P ⋊[φ] K`, with `P` the normal Sylow `p`-subgroup of order `p` and `K` a complement of
order `4`. -/
theorem four_mul_prime_semidirectProduct {p : ℕ} (hp : p.Prime) (hp4 : 4 < p)
    [Finite G] (hG : Nat.card G = 4 * p) :
    ∃ (P K : Subgroup G) (φ : K →* MulAut P),
      P.Normal ∧ Nat.card P = p ∧ Nat.card K = 4 ∧
        Nonempty (G ≃* SemidirectProduct P K φ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow p G))
  haveI hnorm : (↑P0 : Subgroup G).Normal :=
    sylow_p_normal_of_card_four_mul_prime hp hp4 hG P0
  have hcardP : Nat.card (↑P0 : Subgroup G) = p :=
    card_sylow_p_subgroup_of_card_four_mul_prime hp hp4 hG P0
  haveI : (↑P0 : Subgroup G).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
  have hcop : Nat.Coprime (Nat.card (↑P0 : Subgroup G)) (↑P0 : Subgroup G).index := by
    rw [hcardP]
    exact hp.coprime_iff_not_dvd.mpr P0.not_dvd_index
  obtain ⟨K, φ, ⟨e⟩⟩ := schurZassenhaus_semidirectProduct (↑P0 : Subgroup G) hcop
  have hcardK : Nat.card K = 4 := by
    have h1 : Nat.card G = Nat.card (↑P0 : Subgroup G) * Nat.card K := by
      rw [Nat.card_congr e.toEquiv, Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
    rw [hG, hcardP, Nat.mul_comm 4 p] at h1
    exact (Nat.eq_of_mul_eq_mul_left hp.pos h1).symm
  exact ⟨↑P0, K, φ, hnorm, hcardP, hcardK, ⟨e⟩⟩

/-- The complement in the order-`4p` semidirect product is either cyclic of order `4` or
elementary abelian of order `4`. This reduces the remaining classification problem to actions of
`ℤ/4` and `ℤ/2 × ℤ/2` on the normal subgroup of order `p`. -/
theorem four_mul_prime_semidirectProduct_complement_cases {p : ℕ} (hp : p.Prime) (hp4 : 4 < p)
    [Finite G] (hG : Nat.card G = 4 * p) :
    ∃ P : Subgroup G, P.Normal ∧ Nat.card P = p ∧
      ((∃ φ : CyclicRep 4 →* MulAut P,
          Nonempty (G ≃* SemidirectProduct P (CyclicRep 4) φ)) ∨
        (∃ φ : ElemAbelianRep 2 →* MulAut P,
          Nonempty (G ≃* SemidirectProduct P (ElemAbelianRep 2) φ))) := by
  obtain ⟨P, K, φ, hnorm, hcardP, hcardK, ⟨e⟩⟩ :=
    four_mul_prime_semidirectProduct hp hp4 hG
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKcard : Nat.card K = 2 ^ 2 := by
    rw [hcardK]; norm_num
  refine ⟨P, hnorm, hcardP, ?_⟩
  rcases prime_sq_classification (G := K) (p := 2) hKcard with hcyc | helem
  · obtain ⟨σ⟩ := hcyc
    let φ' : CyclicRep 4 →* MulAut P := φ.comp σ.symm.toMonoidHom
    refine Or.inl ⟨φ', ⟨e.trans ?_⟩⟩
    exact semidirectProductCongr (MulEquiv.refl P) σ (by
      intro k
      ext n
      simp [φ'])
  · obtain ⟨σ⟩ := helem
    let φ' : ElemAbelianRep 2 →* MulAut P := φ.comp σ.symm.toMonoidHom
    refine Or.inr ⟨φ', ⟨e.trans ?_⟩⟩
    exact semidirectProductCongr (MulEquiv.refl P) σ (by
      intro k
      ext n
      simp [φ'])

end Smallgroups.UsefulTheorems
