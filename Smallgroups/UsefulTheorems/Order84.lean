/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order4P_12
import Smallgroups.UsefulTheorems.PrimeOrderClassification
import Smallgroups.UsefulTheorems.SchurZassenhaus
import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic.NormNum.Prime

/-!
# First reductions for groups of order 84

Since `84 = 12 * 7`, the Sylow `7`-subgroup is normal.  Thus every group of
order `84` splits as `C₇ ⋊ H`, where `H` is a group of order `12`.

This file records that reduction.  The next classification step is to use the
order-`12` classification for `H` and classify the actions `H → Aut(C₇)`.
-/

namespace Smallgroups.UsefulTheorems

open Sylow

variable {G : Type*} [Group G]

/-! ### Sylow-7 normality and semidirect-product reduction -/

/-- The Sylow `7`-subgroup is unique in a group of order `84`. -/
theorem card_sylow_7_eq_one_of_card_84 [Finite G] (hG : Nat.card G = 84) :
    Nat.card (Sylow 7 G) = 1 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 7 G))
  have hndvd_7 : ¬ 7 ∣ Nat.card (Sylow 7 G) := not_dvd_card_sylow 7 G
  have hdvd84 : Nat.card (Sylow 7 G) ∣ 84 := by
    rw [← hG]
    exact P0.card_dvd_index.trans (Subgroup.index_dvd_card _)
  have h84 : 84 = 12 * 7 := by norm_num
  have hdvd12_mul : Nat.card (Sylow 7 G) ∣ 12 * 7 := by
    simpa [h84] using hdvd84
  have hcop : Nat.Coprime (Nat.card (Sylow 7 G)) 7 :=
    ((show Nat.Prime 7 by norm_num).coprime_iff_not_dvd.mpr hndvd_7).symm
  have hdvd12 : Nat.card (Sylow 7 G) ∣ 12 := hcop.dvd_of_dvd_mul_right hdvd12_mul
  have hmod := card_sylow_modEq_one 7 G
  have hle : Nat.card (Sylow 7 G) ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd12
  have hpos : 0 < Nat.card (Sylow 7 G) := Nat.card_pos
  interval_cases h : Nat.card (Sylow 7 G)
  · rfl
  · unfold Nat.ModEq at hmod
    norm_num at hmod
  · unfold Nat.ModEq at hmod
    norm_num at hmod
  · unfold Nat.ModEq at hmod
    norm_num at hmod
  · norm_num at hdvd12
  · unfold Nat.ModEq at hmod
    norm_num at hmod
  · norm_num at hdvd12
  · norm_num at hdvd12
  · norm_num at hdvd12
  · norm_num at hdvd12
  · norm_num at hdvd12
  · unfold Nat.ModEq at hmod
    norm_num at hmod

/-- The Sylow `7`-subgroup of a group of order `84` is normal. -/
theorem sylow_7_normal_of_card_84 [Finite G] (hG : Nat.card G = 84) (P : Sylow 7 G) :
    (↑P : Subgroup G).Normal := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Subsingleton (Sylow 7 G) :=
    (Nat.card_eq_one_iff_unique.mp (card_sylow_7_eq_one_of_card_84 hG)).1
  exact normal_of_subsingleton P

/-- The Sylow `7`-subgroup of a group of order `84` has order `7`. -/
theorem card_sylow_7_subgroup_of_card_84 [Finite G] (hG : Nat.card G = 84)
    (P : Sylow 7 G) : Nat.card (↑P : Subgroup G) = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hndvd : ¬ 7 ∣ 12 := by norm_num
  have hfact : (84 : ℕ).factorization 7 = 1 := by
    rw [show 84 = 12 * 7 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hndvd,
      Nat.Prime.factorization_self (by norm_num : Nat.Prime 7), zero_add]
  rw [Sylow.card_eq_multiplicity, hG, hfact, pow_one]

/-- **Schur-Zassenhaus reduction for order `84`.**
Every group of order `84` is a semidirect product `N ⋊[φ] H`, where
`N` has order `7` and `H` has order `12`. -/
theorem order84_semidirectProduct [Finite G] (hG : Nat.card G = 84) :
    ∃ (N H : Subgroup G) (φ : H →* MulAut N),
      N.Normal ∧ Nat.card N = 7 ∧ Nat.card H = 12 ∧
        Nonempty (G ≃* SemidirectProduct N H φ) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 7 G))
  haveI hnorm : (↑P0 : Subgroup G).Normal := sylow_7_normal_of_card_84 hG P0
  have hcardN : Nat.card (↑P0 : Subgroup G) = 7 :=
    card_sylow_7_subgroup_of_card_84 hG P0
  haveI : (↑P0 : Subgroup G).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
  have hcop : Nat.Coprime (Nat.card (↑P0 : Subgroup G)) (↑P0 : Subgroup G).index := by
    rw [hcardN]
    exact (show Nat.Prime 7 by norm_num).coprime_iff_not_dvd.mpr P0.not_dvd_index
  obtain ⟨H, φ, ⟨e⟩⟩ := schurZassenhaus_semidirectProduct (↑P0 : Subgroup G) hcop
  have hcardH : Nat.card H = 12 := by
    have h1 : Nat.card G = Nat.card (↑P0 : Subgroup G) * Nat.card H := by
      rw [Nat.card_congr e.toEquiv, Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
    rw [hG, hcardN] at h1
    have h1' : 7 * Nat.card H = 7 * 12 := by omega
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 7) h1'
  exact ⟨↑P0, H, φ, hnorm, hcardN, hcardH, ⟨e⟩⟩

/-! ### Standard factor choices -/

/-- The normal subgroup in the order-`84` representatives. -/
abbrev order84_C7 : Type := CyclicRep 7

/-- `ℤ/12`. -/
abbrev order84_HA : Type := fourP_I 3

/-- `ℤ/2 × ℤ/6`. -/
abbrev order84_HB : Type := fourP_II 3

/-- `ℤ/3 ⋊_{-1} ℤ/4`. -/
abbrev order84_HC : Type := fourP_III 3

/-- `ℤ/2 × D₆`. -/
abbrev order84_HD : Type := fourP_V 3

/-- The alternating group `A₄`. -/
abbrev order84_HE : Type := fourP_A4

/-! ### Unit-valued characters for the cyclic complement -/

/-- A generator of `(ZMod 7)ˣ`. -/
noncomputable abbrev order84_u6 : (ZMod 7)ˣ :=
  ZMod.unitOfCoprime 3 (by norm_num : Nat.Coprime 3 7)

theorem order84_unit_cases (u : (ZMod 7)ˣ) :
    u = 1 ∨ u = order84_u6 ∨ u = order84_u6 ^ 2 ∨ u = order84_u6 ^ 3 ∨
      u = order84_u6 ^ 4 ∨ u = order84_u6 ^ 5 := by
  decide +revert

/-- Turn a unit-valued character into the corresponding action on `C₇`. -/
noncomputable abbrev order84_action {H : Type} [Group H] (χ : H →* (ZMod 7)ˣ) :
    H →* MulAut order84_C7 :=
  unitAutHom.comp χ

noncomputable abbrev order84_chiC12_six : order84_HA →* (ZMod 7)ˣ :=
  powHom (p := 7) (q := 12) order84_u6 (by decide)

noncomputable abbrev order84_chiC12_three : order84_HA →* (ZMod 7)ˣ :=
  powHom (p := 7) (q := 12) (order84_u6 ^ 2) (by decide)

noncomputable abbrev order84_chiC12_two : order84_HA →* (ZMod 7)ˣ :=
  powHom (p := 7) (q := 12) (order84_u6 ^ 3) (by decide)

noncomputable abbrev order84_chiC12_three_inv : order84_HA →* (ZMod 7)ˣ :=
  powHom (p := 7) (q := 12) (order84_u6 ^ 4) (by decide)

noncomputable abbrev order84_chiC12_six_inv : order84_HA →* (ZMod 7)ˣ :=
  powHom (p := 7) (q := 12) (order84_u6 ^ 5) (by decide)

@[simp]
theorem order84_chiC12_six_gen :
    order84_chiC12_six (Multiplicative.ofAdd (1 : ZMod 12)) = order84_u6 := by
  decide

@[simp]
theorem order84_chiC12_three_gen :
    order84_chiC12_three (Multiplicative.ofAdd (1 : ZMod 12)) = order84_u6 ^ 2 := by
  decide

@[simp]
theorem order84_chiC12_two_gen :
    order84_chiC12_two (Multiplicative.ofAdd (1 : ZMod 12)) = order84_u6 ^ 3 := by
  decide

@[simp]
theorem order84_chiC12_three_inv_gen :
    order84_chiC12_three_inv (Multiplicative.ofAdd (1 : ZMod 12)) = order84_u6 ^ 4 := by
  decide

@[simp]
theorem order84_chiC12_six_inv_gen :
    order84_chiC12_six_inv (Multiplicative.ofAdd (1 : ZMod 12)) = order84_u6 ^ 5 := by
  decide

/-- Homomorphisms out of `C₁₂` are determined by the additive generator `1`. -/
theorem order84_c12_unit_hom_ext {χ ψ : order84_HA →* (ZMod 7)ˣ}
    (hgen : χ (Multiplicative.ofAdd (1 : ZMod 12)) =
      ψ (Multiplicative.ofAdd (1 : ZMod 12))) :
    χ = ψ := by
  apply MonoidHom.ext
  intro x
  let n : ZMod 12 := Multiplicative.toAdd x
  have hx : x = (Multiplicative.ofAdd (1 : ZMod 12)) ^ n.val := by
    rw [show x = Multiplicative.ofAdd n from (ofAdd_toAdd _).symm]
    calc
      Multiplicative.ofAdd n = Multiplicative.ofAdd ((n.val : ZMod 12)) := by
        rw [ZMod.natCast_zmod_val]
      _ = Multiplicative.ofAdd (n.val • (1 : ZMod 12)) := by simp
      _ = (Multiplicative.ofAdd (1 : ZMod 12)) ^ n.val := by rw [ofAdd_nsmul]
  rw [hx, map_pow, map_pow, hgen]

/-- Actions out of `C₁₂` are determined by the additive generator `1`. -/
theorem order84_c12_action_hom_ext {φ ψ : order84_HA →* MulAut order84_C7}
    (hgen : φ (Multiplicative.ofAdd (1 : ZMod 12)) =
      ψ (Multiplicative.ofAdd (1 : ZMod 12))) :
    φ = ψ := by
  apply MonoidHom.ext
  intro x
  let n : ZMod 12 := Multiplicative.toAdd x
  have hx : x = (Multiplicative.ofAdd (1 : ZMod 12)) ^ n.val := by
    rw [show x = Multiplicative.ofAdd n from (ofAdd_toAdd _).symm]
    calc
      Multiplicative.ofAdd n = Multiplicative.ofAdd ((n.val : ZMod 12)) := by
        rw [ZMod.natCast_zmod_val]
      _ = Multiplicative.ofAdd (n.val • (1 : ZMod 12)) := by simp
      _ = (Multiplicative.ofAdd (1 : ZMod 12)) ^ n.val := by rw [ofAdd_nsmul]
  rw [hx, map_pow, map_pow, hgen]

/-- Unit-valued characters of `C₁₂` are the six displayed characters. -/
theorem order84_c12_unit_character_cases (χ : order84_HA →* (ZMod 7)ˣ) :
    χ = 1 ∨ χ = order84_chiC12_six ∨ χ = order84_chiC12_three ∨
      χ = order84_chiC12_two ∨ χ = order84_chiC12_three_inv ∨
      χ = order84_chiC12_six_inv := by
  let g : order84_HA := Multiplicative.ofAdd (1 : ZMod 12)
  rcases order84_unit_cases (χ g) with h | h | h | h | h | h
  · left
    apply order84_c12_unit_hom_ext
    simp [g, h]
  · right; left
    apply order84_c12_unit_hom_ext
    rw [h, order84_chiC12_six_gen]
  · right; right; left
    apply order84_c12_unit_hom_ext
    rw [h, order84_chiC12_three_gen]
  · right; right; right; left
    apply order84_c12_unit_hom_ext
    rw [h, order84_chiC12_two_gen]
  · right; right; right; right; left
    apply order84_c12_unit_hom_ext
    rw [h, order84_chiC12_three_inv_gen]
  · right; right; right; right; right
    apply order84_c12_unit_hom_ext
    rw [h, order84_chiC12_six_inv_gen]

/-- Actions `C₁₂ → Aut(C₇)` are the six displayed unit actions. -/
theorem order84_c12_action_cases (φ : order84_HA →* MulAut order84_C7) :
    φ = 1 ∨ φ = order84_action order84_chiC12_six ∨
      φ = order84_action order84_chiC12_three ∨
      φ = order84_action order84_chiC12_two ∨
      φ = order84_action order84_chiC12_three_inv ∨
      φ = order84_action order84_chiC12_six_inv := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let g : order84_HA := Multiplicative.ofAdd (1 : ZMod 12)
  obtain ⟨u, hu⟩ := exists_unitAutHom_eq (p := 7) (φ g)
  rcases order84_unit_cases u with h | h | h | h | h | h
  · left
    apply order84_c12_action_hom_ext
    rw [hu, h]
    exact map_one (unitAutHom (p := 7))
  · right; left
    apply order84_c12_action_hom_ext
    rw [hu, h]
    change unitAutHom order84_u6 =
      unitAutHom (order84_chiC12_six (Multiplicative.ofAdd (1 : ZMod 12)))
    rw [order84_chiC12_six_gen]
  · right; right; left
    apply order84_c12_action_hom_ext
    rw [hu, h]
    change unitAutHom (order84_u6 ^ 2) =
      unitAutHom (order84_chiC12_three (Multiplicative.ofAdd (1 : ZMod 12)))
    rw [order84_chiC12_three_gen]
  · right; right; right; left
    apply order84_c12_action_hom_ext
    rw [hu, h]
    change unitAutHom (order84_u6 ^ 3) =
      unitAutHom (order84_chiC12_two (Multiplicative.ofAdd (1 : ZMod 12)))
    rw [order84_chiC12_two_gen]
  · right; right; right; right; left
    apply order84_c12_action_hom_ext
    rw [hu, h]
    change unitAutHom (order84_u6 ^ 4) =
      unitAutHom (order84_chiC12_three_inv (Multiplicative.ofAdd (1 : ZMod 12)))
    rw [order84_chiC12_three_inv_gen]
  · right; right; right; right; right
    apply order84_c12_action_hom_ext
    rw [hu, h]
    change unitAutHom (order84_u6 ^ 5) =
      unitAutHom (order84_chiC12_six_inv (Multiplicative.ofAdd (1 : ZMod 12)))
    rw [order84_chiC12_six_inv_gen]

/-- Every group of order `84` is one of five standard semidirect-product action problems,
according to the order-`12` complement. -/
theorem order84_semidirectProduct_standard_cases [Finite G] (hG : Nat.card G = 84) :
    (∃ φ : order84_HA →* MulAut order84_C7,
      Nonempty (G ≃* SemidirectProduct order84_C7 order84_HA φ)) ∨
    (∃ φ : order84_HB →* MulAut order84_C7,
      Nonempty (G ≃* SemidirectProduct order84_C7 order84_HB φ)) ∨
    (∃ φ : order84_HC →* MulAut order84_C7,
      Nonempty (G ≃* SemidirectProduct order84_C7 order84_HC φ)) ∨
    (∃ φ : order84_HD →* MulAut order84_C7,
      Nonempty (G ≃* SemidirectProduct order84_C7 order84_HD φ)) ∨
    (∃ φ : order84_HE →* MulAut order84_C7,
      Nonempty (G ≃* SemidirectProduct order84_C7 order84_HE φ)) := by
  obtain ⟨N, H, φ, _, hcardN, hcardH, ⟨e⟩⟩ := order84_semidirectProduct hG
  obtain ⟨eN⟩ := prime_classification (by norm_num : Nat.Prime 7) hcardN
  rcases fourP_12_classification (G := H) hcardH with hH | hH | hH | hH | hH
  · have hH' : Nonempty (H ≃* order84_HA) := by simpa [order84_HA] using hH
    obtain ⟨eH⟩ := hH'
    exact Or.inl ⟨_, ⟨e.trans (SemidirectProduct.congr' eN eH)⟩⟩
  · have hH' : Nonempty (H ≃* order84_HB) := by simpa [order84_HB] using hH
    obtain ⟨eH⟩ := hH'
    exact Or.inr <| Or.inl ⟨_, ⟨e.trans (SemidirectProduct.congr' eN eH)⟩⟩
  · have hH' : Nonempty (H ≃* order84_HC) := by simpa [order84_HC] using hH
    obtain ⟨eH⟩ := hH'
    exact Or.inr <| Or.inr <| Or.inl ⟨_, ⟨e.trans (SemidirectProduct.congr' eN eH)⟩⟩
  · have hH' : Nonempty (H ≃* order84_HD) := by simpa [order84_HD] using hH
    obtain ⟨eH⟩ := hH'
    exact Or.inr <| Or.inr <| Or.inr <|
      Or.inl ⟨_, ⟨e.trans (SemidirectProduct.congr' eN eH)⟩⟩
  · have hH' : Nonempty (H ≃* order84_HE) := by simpa [order84_HE] using hH
    obtain ⟨eH⟩ := hH'
    exact Or.inr <| Or.inr <| Or.inr <|
      Or.inr ⟨_, ⟨e.trans (SemidirectProduct.congr' eN eH)⟩⟩

end Smallgroups.UsefulTheorems
