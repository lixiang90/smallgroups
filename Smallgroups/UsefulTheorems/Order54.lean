/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.P3Group
import Smallgroups.UsefulTheorems.PrimeOrderClassification
import Smallgroups.UsefulTheorems.SchurZassenhaus
import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic.NormNum.Prime

/-!
# First reductions for groups of order 54

Since `54 = 2 * 3^3`, the Sylow `3`-subgroup of a group of order `54` is
unique.  Thus every group of order `54` has a normal subgroup of order `27`,
and Schur--Zassenhaus splits it as a semidirect product `N ⋊ H` with
`|N| = 27` and `|H| = 2`.

The remaining classification problem is the orbit calculation for actions
`H → Aut(N)`, where `N` is one of the five groups of order `27` from
`P3Group.classification`.
-/

namespace Smallgroups.UsefulTheorems

open Sylow

variable {G : Type*} [Group G]

/-! ### Standard factors -/

/-- The complement in the order-`54` semidirect-product reduction. -/
abbrev order54_C2 : Type := CyclicRep 2

/-- `C₂₇`. -/
abbrev order54_C27 : Type := Multiplicative (P3Group.CyclicP3 3)

/-- `C₉ × C₃`. -/
abbrev order54_C9C3 : Type :=
  Multiplicative (ZMod (3 ^ 2)) × Multiplicative (ZMod 3)

/-- `(C₃)³`. -/
abbrev order54_C3C3C3 : Type :=
  Multiplicative (ZMod 3) × Multiplicative (ZMod 3) × Multiplicative (ZMod 3)

/-- The non-abelian exponent-`3` group of order `27`. -/
abbrev order54_Heisenberg : Type := P3Group.HeisenbergGroup 3

/-- The non-abelian exponent-`9` group of order `27`. -/
abbrev order54_SemidirectP2P : Type := P3Group.SemidirectP2P 3

/-! ### Cardinalities of the standard factors -/

theorem card_order54_C2 : Nat.card order54_C2 = 2 :=
  card_cyclicRep (by norm_num)

theorem card_order54_C27 : Nat.card order54_C27 = 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  simp

theorem card_order54_C9C3 : Nat.card order54_C9C3 = 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  simp

theorem card_order54_C3C3C3 : Nat.card order54_C3C3C3 = 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  simp

theorem card_order54_Heisenberg : Nat.card order54_Heisenberg = 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  simpa using P3Group.HeisenbergGroup.card_heisenberg 3

theorem card_order54_SemidirectP2P : Nat.card order54_SemidirectP2P = 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  simpa using P3Group.SemidirectP2P.card_semidirectP2P 3

theorem card_order54_semidirect_C27 (φ : order54_C2 →* MulAut order54_C27) :
    Nat.card (SemidirectProduct order54_C27 order54_C2 φ) = 54 := by
  rw [SemidirectProduct.card, card_order54_C27, card_order54_C2]

theorem card_order54_semidirect_C9C3 (φ : order54_C2 →* MulAut order54_C9C3) :
    Nat.card (SemidirectProduct order54_C9C3 order54_C2 φ) = 54 := by
  rw [SemidirectProduct.card, card_order54_C9C3, card_order54_C2]

theorem card_order54_semidirect_C3C3C3 (φ : order54_C2 →* MulAut order54_C3C3C3) :
    Nat.card (SemidirectProduct order54_C3C3C3 order54_C2 φ) = 54 := by
  rw [SemidirectProduct.card, card_order54_C3C3C3, card_order54_C2]

theorem card_order54_semidirect_Heisenberg (φ : order54_C2 →* MulAut order54_Heisenberg) :
    Nat.card (SemidirectProduct order54_Heisenberg order54_C2 φ) = 54 := by
  rw [SemidirectProduct.card, card_order54_Heisenberg, card_order54_C2]

theorem card_order54_semidirect_SemidirectP2P
    (φ : order54_C2 →* MulAut order54_SemidirectP2P) :
    Nat.card (SemidirectProduct order54_SemidirectP2P order54_C2 φ) = 54 := by
  rw [SemidirectProduct.card, card_order54_SemidirectP2P, card_order54_C2]

/-! ### Sylow-3 normality and semidirect-product reduction -/

/-- The Sylow `3`-subgroup is unique in a group of order `54`. -/
theorem card_sylow_3_eq_one_of_card_54 [Finite G] (hG : Nat.card G = 54) :
    Nat.card (Sylow 3 G) = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 3 G))
  have hndvd_3 : ¬ 3 ∣ Nat.card (Sylow 3 G) := not_dvd_card_sylow 3 G
  have hdvd54 : Nat.card (Sylow 3 G) ∣ 54 := by
    rw [← hG]
    exact P0.card_dvd_index.trans (Subgroup.index_dvd_card _)
  have h54 : 54 = 2 * 3 ^ 3 := by norm_num
  have hdvd2_mul : Nat.card (Sylow 3 G) ∣ 2 * 3 ^ 3 := by
    simpa [h54] using hdvd54
  have hp3 : Nat.Prime 3 := by norm_num
  have hcop : Nat.Coprime (Nat.card (Sylow 3 G)) 3 :=
    (hp3.coprime_iff_not_dvd.mpr hndvd_3).symm
  have hcop_pow : Nat.Coprime (Nat.card (Sylow 3 G)) (3 ^ 3) :=
    hcop.pow_right 3
  have hdvd2 : Nat.card (Sylow 3 G) ∣ 2 := hcop_pow.dvd_of_dvd_mul_right hdvd2_mul
  have hmod := card_sylow_modEq_one 3 G
  have hle : Nat.card (Sylow 3 G) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
  have hpos : 0 < Nat.card (Sylow 3 G) := Nat.card_pos
  have hlt : Nat.card (Sylow 3 G) < 3 := by omega
  unfold Nat.ModEq at hmod
  rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 1 < 3)] at hmod
  exact hmod

/-- The Sylow `3`-subgroup of a group of order `54` is normal. -/
theorem sylow_3_normal_of_card_54 [Finite G] (hG : Nat.card G = 54) (P : Sylow 3 G) :
    (↑P : Subgroup G).Normal := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Subsingleton (Sylow 3 G) :=
    (Nat.card_eq_one_iff_unique.mp (card_sylow_3_eq_one_of_card_54 hG)).1
  exact normal_of_subsingleton P

/-- The Sylow `3`-subgroup of a group of order `54` has order `27`. -/
theorem card_sylow_3_subgroup_of_card_54 [Finite G] (hG : Nat.card G = 54)
    (P : Sylow 3 G) : Nat.card (↑P : Subgroup G) = 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hfact : (54 : ℕ).factorization 3 = 3 := by
    rw [show (54 : ℕ) = 2 * 3 ^ 3 by norm_num,
      Nat.factorization_mul (by norm_num) (pow_ne_zero 3 (by norm_num : (3 : ℕ) ≠ 0)),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2),
      Nat.factorization_pow, Finsupp.smul_apply,
      Nat.Prime.factorization_self (by norm_num : Nat.Prime 3)]
    norm_num
  rw [Sylow.card_eq_multiplicity, hG]
  rw [hfact]
  norm_num

/-- **Schur-Zassenhaus reduction for order `54`.**
Every group of order `54` is a semidirect product `N ⋊[φ] H`, where
`N` has order `27` and `H` has order `2`. -/
theorem order54_semidirectProduct [Finite G] (hG : Nat.card G = 54) :
    ∃ (N H : Subgroup G) (φ : H →* MulAut N),
      N.Normal ∧ Nat.card N = 27 ∧ Nat.card H = 2 ∧
        Nonempty (G ≃* SemidirectProduct N H φ) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 3 G))
  haveI hnorm : (↑P0 : Subgroup G).Normal := sylow_3_normal_of_card_54 hG P0
  have hcardN : Nat.card (↑P0 : Subgroup G) = 27 :=
    card_sylow_3_subgroup_of_card_54 hG P0
  haveI : (↑P0 : Subgroup G).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
  have hcop : Nat.Coprime (Nat.card (↑P0 : Subgroup G)) (↑P0 : Subgroup G).index := by
    rw [hcardN]
    have hnot : ¬ 3 ∣ (↑P0 : Subgroup G).index := P0.not_dvd_index
    have hcop3 : Nat.Coprime 3 (↑P0 : Subgroup G).index :=
      (show Nat.Prime 3 by norm_num).coprime_iff_not_dvd.mpr hnot
    simpa using hcop3.pow_left 3
  obtain ⟨H, φ, ⟨e⟩⟩ := schurZassenhaus_semidirectProduct (↑P0 : Subgroup G) hcop
  have hcardH : Nat.card H = 2 := by
    have h1 : Nat.card G = Nat.card (↑P0 : Subgroup G) * Nat.card H := by
      rw [Nat.card_congr e.toEquiv, Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
    rw [hG, hcardN] at h1
    have h1' : 27 * Nat.card H = 27 * 2 := by omega
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 27) h1'
  exact ⟨↑P0, H, φ, hnorm, hcardN, hcardH, ⟨e⟩⟩

/-! ### Standard order-27 kernel cases -/

/-- The normal subgroup in an order-`54` semidirect product is one of the five groups of
order `27`. -/
theorem order54_kernel_cases {N : Type*} [Group N] [Fintype N] (hN : Nat.card N = 27) :
    P3Group.IsP3Group 3 N := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact P3Group.classification 3 N (hN.trans (by norm_num))

/-- Combined standard-case reduction: the normal subgroup in the Schur--Zassenhaus
decomposition is one of the five standard groups of order `27`. -/
theorem order54_semidirectProduct_kernel_cases [Finite G] (hG : Nat.card G = 54) :
    ∃ (N H : Subgroup G) (φ : H →* MulAut N),
      ∃ (_ : Fintype N),
      N.Normal ∧ Nat.card N = 27 ∧ Nat.card H = 2 ∧
        P3Group.IsP3Group 3 N ∧ Nonempty (G ≃* SemidirectProduct N H φ) := by
  rcases order54_semidirectProduct (G := G) hG with
    ⟨N, H, φ, hnorm, hcardN, hcardH, hiso⟩
  haveI : Fintype N := Fintype.ofFinite N
  exact ⟨N, H, φ, inferInstance, hnorm, hcardN, hcardH, order54_kernel_cases hcardN, hiso⟩

/-- Every group of order `54` is a semidirect product of `C₂` acting on one of the five
standard groups of order `27`.  The remaining work is to classify the possible actions in
each branch. -/
theorem order54_semidirectProduct_standard_cases [Finite G] (hG : Nat.card G = 54) :
    (∃ φ : order54_C2 →* MulAut order54_C27,
      Nonempty (G ≃* SemidirectProduct order54_C27 order54_C2 φ)) ∨
    (∃ φ : order54_C2 →* MulAut order54_C9C3,
      Nonempty (G ≃* SemidirectProduct order54_C9C3 order54_C2 φ)) ∨
    (∃ φ : order54_C2 →* MulAut order54_C3C3C3,
      Nonempty (G ≃* SemidirectProduct order54_C3C3C3 order54_C2 φ)) ∨
    (∃ φ : order54_C2 →* MulAut order54_Heisenberg,
      Nonempty (G ≃* SemidirectProduct order54_Heisenberg order54_C2 φ)) ∨
    (∃ φ : order54_C2 →* MulAut order54_SemidirectP2P,
      Nonempty (G ≃* SemidirectProduct order54_SemidirectP2P order54_C2 φ)) := by
  rcases order54_semidirectProduct (G := G) hG with
    ⟨N, H, φ, _, hcardN, hcardH, ⟨e⟩⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fintype N := Fintype.ofFinite N
  obtain ⟨eH⟩ := prime_classification (by norm_num : Nat.Prime 2) hcardH
  rcases P3Group.classification 3 N (hcardN.trans (by norm_num)) with
    hN | hN | hN | hN | hN | hN | hN
  · change Nonempty (N ≃* order54_C27) at hN
    obtain ⟨eN⟩ := hN
    exact Or.inl ⟨_, ⟨e.trans (SemidirectProduct.congr' eN eH)⟩⟩
  · change Nonempty (N ≃* order54_C9C3) at hN
    obtain ⟨eN⟩ := hN
    exact Or.inr (Or.inl ⟨_, ⟨e.trans (SemidirectProduct.congr' eN eH)⟩⟩)
  · change Nonempty (N ≃* order54_C3C3C3) at hN
    obtain ⟨eN⟩ := hN
    exact Or.inr (Or.inr (Or.inl ⟨_, ⟨e.trans (SemidirectProduct.congr' eN eH)⟩⟩))
  · change 3 ≠ 2 ∧ Nonempty (N ≃* order54_Heisenberg) at hN
    obtain ⟨eN⟩ := hN.2
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨_, ⟨e.trans (SemidirectProduct.congr' eN eH)⟩⟩)))
  · change 3 ≠ 2 ∧ Nonempty (N ≃* order54_SemidirectP2P) at hN
    obtain ⟨eN⟩ := hN.2
    exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨_, ⟨e.trans (SemidirectProduct.congr' eN eH)⟩⟩)))
  · exfalso
    exact (by norm_num : ¬ (3 : ℕ) = 2) hN.1
  · exfalso
    exact (by norm_num : ¬ (3 : ℕ) = 2) hN.1

end Smallgroups.UsefulTheorems
