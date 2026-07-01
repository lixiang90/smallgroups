/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order4P_12
import Smallgroups.UsefulTheorems.PrimeOrderClassification
import Smallgroups.UsefulTheorems.SchurZassenhaus
import Smallgroups.UsefulTheorems.SemidirectProductClassify
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

theorem order84_u6_pow3_pow3_ne_one : (order84_u6 ^ 3) ^ 3 ≠ (1 : (ZMod 7)ˣ) := by
  decide

theorem order84_u6_pow4_ne_one : order84_u6 ^ 4 ≠ (1 : (ZMod 7)ˣ) := by
  decide

theorem order84_u6_pow2_pow4_ne_one : (order84_u6 ^ 2) ^ 4 ≠ (1 : (ZMod 7)ˣ) := by
  decide

theorem order84_u6_pow4_pow4_ne_one : (order84_u6 ^ 4) ^ 4 ≠ (1 : (ZMod 7)ˣ) := by
  decide

theorem order84_u6_pow5_pow4_ne_one : (order84_u6 ^ 5) ^ 4 ≠ (1 : (ZMod 7)ˣ) := by
  decide

theorem order84_unit_sq_eq_one_cases (u : (ZMod 7)ˣ) (hu : u ^ 2 = 1) :
    u = 1 ∨ u = order84_u6 ^ 3 := by
  rcases order84_unit_cases u with h | h | h | h | h | h
  · exact Or.inl h
  · exfalso
    have hbad : order84_u6 ^ 2 = (1 : (ZMod 7)ˣ) := by simpa [h] using hu
    exact (by decide : order84_u6 ^ 2 ≠ (1 : (ZMod 7)ˣ)) hbad
  · exfalso
    have hbad : (order84_u6 ^ 2) ^ 2 = (1 : (ZMod 7)ˣ) := by simpa [h] using hu
    exact (by decide : (order84_u6 ^ 2) ^ 2 ≠ (1 : (ZMod 7)ˣ)) hbad
  · exact Or.inr h
  · exfalso
    have hbad : (order84_u6 ^ 4) ^ 2 = (1 : (ZMod 7)ˣ) := by simpa [h] using hu
    exact (by decide : (order84_u6 ^ 4) ^ 2 ≠ (1 : (ZMod 7)ˣ)) hbad
  · exfalso
    have hbad : (order84_u6 ^ 5) ^ 2 = (1 : (ZMod 7)ˣ) := by simpa [h] using hu
    exact (by decide : (order84_u6 ^ 5) ^ 2 ≠ (1 : (ZMod 7)ˣ)) hbad

theorem order84_mulAut_sq_eq_one_cases (α : MulAut order84_C7) (hα : α ^ 2 = 1) :
    α = 1 ∨ α = unitAutHom (order84_u6 ^ 3) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨u, hu⟩ := exists_unitAutHom_eq (p := 7) α
  have hu2 : u ^ 2 = 1 := by
    apply unitAutHom_injective (p := 7)
    rw [map_pow, ← hu, hα, map_one]
  rcases order84_unit_sq_eq_one_cases u hu2 with h | h
  · left
    rw [hu, h]
    exact map_one (unitAutHom (p := 7))
  · right
    rw [hu, h]

theorem order84_mulAut_comm (α β : MulAut order84_C7) : α * β = β * α := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨u, hu⟩ := exists_unitAutHom_eq (p := 7) α
  obtain ⟨v, hv⟩ := exists_unitAutHom_eq (p := 7) β
  rw [hu, hv, ← map_mul, ← map_mul, mul_comm]

/-- Turn a unit-valued character into the corresponding action on `C₇`. -/
noncomputable abbrev order84_action {H : Type} [Group H] (χ : H →* (ZMod 7)ˣ) :
    H →* MulAut order84_C7 :=
  unitAutHom.comp χ

noncomputable def order84_action_precomp_mulEquiv {H : Type} [Group H]
    (χ : H →* (ZMod 7)ˣ) (σ : H ≃* H) :
    SemidirectProduct order84_C7 H (order84_action (χ.comp σ.toMonoidHom)) ≃*
      SemidirectProduct order84_C7 H (order84_action χ) :=
  semidirectProductCongrAut (N := order84_C7) (H := H) (φ := order84_action χ) σ

noncomputable def order84_action_precomp_eq_mulEquiv {H : Type} [Group H]
    (χ ψ : H →* (ZMod 7)ˣ) (σ : H ≃* H)
    (h : χ.comp σ.toMonoidHom = ψ) :
    SemidirectProduct order84_C7 H (order84_action ψ) ≃*
      SemidirectProduct order84_C7 H (order84_action χ) := by
  have haction : order84_action ψ = order84_action (χ.comp σ.toMonoidHom) := by
    rw [h]
  exact (semidirectProductCongr_eq haction).trans
    (order84_action_precomp_mulEquiv χ σ)

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

/-! ### Automorphism orbits for cyclic-complement actions -/

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

/-! ### Cyclic-complement semidirect-product cases -/

/-- The automorphism of `C₁₂` sending the additive generator to five times itself. -/
noncomputable def order84_C12_mulFive : order84_HA ≃* order84_HA :=
  unitAutHom (p := 12) (ZMod.unitOfCoprime 5 (by norm_num : Nat.Coprime 5 12))

/-- The two faithful characters of `C₁₂` lie in the same automorphism orbit. -/
theorem order84_chiC12_six_comp_mulFive :
    order84_chiC12_six.comp order84_C12_mulFive.toMonoidHom =
      order84_chiC12_six_inv := by
  apply order84_c12_unit_hom_ext
  decide

/-- The two order-`3` characters of `C₁₂` lie in the same automorphism orbit. -/
theorem order84_chiC12_three_comp_mulFive :
    order84_chiC12_three.comp order84_C12_mulFive.toMonoidHom =
      order84_chiC12_three_inv := by
  apply order84_c12_unit_hom_ext
  decide

/-- The order-`2` character of `C₁₂` is fixed by the multiplication-by-five automorphism. -/
theorem order84_chiC12_two_comp_mulFive :
    order84_chiC12_two.comp order84_C12_mulFive.toMonoidHom =
      order84_chiC12_two := by
  apply order84_c12_unit_hom_ext
  decide

noncomputable abbrev order84_c12_trivial : Type :=
  order84_C7 × order84_HA

noncomputable abbrev order84_c12_six : Type :=
  SemidirectProduct order84_C7 order84_HA (order84_action order84_chiC12_six)

noncomputable abbrev order84_c12_three : Type :=
  SemidirectProduct order84_C7 order84_HA (order84_action order84_chiC12_three)

noncomputable abbrev order84_c12_two : Type :=
  SemidirectProduct order84_C7 order84_HA (order84_action order84_chiC12_two)

noncomputable def order84_c12_six_inv_equiv_six :
    SemidirectProduct order84_C7 order84_HA (order84_action order84_chiC12_six_inv) ≃*
      order84_c12_six :=
  order84_action_precomp_eq_mulEquiv order84_chiC12_six order84_chiC12_six_inv
    order84_C12_mulFive order84_chiC12_six_comp_mulFive

noncomputable def order84_c12_three_inv_equiv_three :
    SemidirectProduct order84_C7 order84_HA (order84_action order84_chiC12_three_inv) ≃*
      order84_c12_three :=
  order84_action_precomp_eq_mulEquiv order84_chiC12_three order84_chiC12_three_inv
    order84_C12_mulFive order84_chiC12_three_comp_mulFive

theorem order84_c12_action_semidirect_cases (φ : order84_HA →* MulAut order84_C7) :
    Nonempty (SemidirectProduct order84_C7 order84_HA φ ≃* order84_c12_trivial) ∨
      Nonempty (SemidirectProduct order84_C7 order84_HA φ ≃* order84_c12_six) ∨
      Nonempty (SemidirectProduct order84_C7 order84_HA φ ≃* order84_c12_three) ∨
      Nonempty (SemidirectProduct order84_C7 order84_HA φ ≃* order84_c12_two) := by
  rcases order84_c12_action_cases φ with hφ | hφ | hφ | hφ | hφ | hφ
  · left
    exact ⟨(semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd⟩
  · right; left
    exact ⟨semidirectProductCongr_eq hφ⟩
  · right; right; left
    exact ⟨semidirectProductCongr_eq hφ⟩
  · right; right; right
    exact ⟨semidirectProductCongr_eq hφ⟩
  · right; right; left
    exact ⟨(semidirectProductCongr_eq hφ).trans order84_c12_three_inv_equiv_three⟩
  · right; left
    exact ⟨(semidirectProductCongr_eq hφ).trans order84_c12_six_inv_equiv_six⟩

/-! ### `C₂ × C₆`-complement actions -/

noncomputable abbrev order84_c2UnitHom : Multiplicative (ZMod 2) →* (ZMod 7)ˣ :=
  powHom (p := 7) (q := 2) (order84_u6 ^ 3) (by decide)

noncomputable abbrev order84_chiC2C6_fst_two : order84_HB →* (ZMod 7)ˣ :=
  order84_c2UnitHom.comp
    (MonoidHom.fst (Multiplicative (ZMod 2)) (Multiplicative (ZMod 6)))

noncomputable abbrev order84_chiC2C6_snd_six : order84_HB →* (ZMod 7)ˣ :=
  (powHom (p := 7) (q := 6) order84_u6 (by decide)).comp
    (MonoidHom.snd (Multiplicative (ZMod 2)) (Multiplicative (ZMod 6)))

noncomputable abbrev order84_chiC2C6_snd_three : order84_HB →* (ZMod 7)ˣ :=
  (powHom (p := 7) (q := 6) (order84_u6 ^ 2) (by decide)).comp
    (MonoidHom.snd (Multiplicative (ZMod 2)) (Multiplicative (ZMod 6)))

noncomputable abbrev order84_chiC2C6_snd_two : order84_HB →* (ZMod 7)ˣ :=
  (powHom (p := 7) (q := 6) (order84_u6 ^ 3) (by decide)).comp
    (MonoidHom.snd (Multiplicative (ZMod 2)) (Multiplicative (ZMod 6)))

noncomputable abbrev order84_chiC2C6_snd_three_inv : order84_HB →* (ZMod 7)ˣ :=
  (powHom (p := 7) (q := 6) (order84_u6 ^ 4) (by decide)).comp
    (MonoidHom.snd (Multiplicative (ZMod 2)) (Multiplicative (ZMod 6)))

noncomputable abbrev order84_chiC2C6_snd_six_inv : order84_HB →* (ZMod 7)ˣ :=
  (powHom (p := 7) (q := 6) (order84_u6 ^ 5) (by decide)).comp
    (MonoidHom.snd (Multiplicative (ZMod 2)) (Multiplicative (ZMod 6)))

noncomputable abbrev order84_chiC2C6_fst_two_snd_six : order84_HB →* (ZMod 7)ˣ :=
  order84_chiC2C6_fst_two * order84_chiC2C6_snd_six

noncomputable abbrev order84_chiC2C6_fst_two_snd_three : order84_HB →* (ZMod 7)ˣ :=
  order84_chiC2C6_fst_two * order84_chiC2C6_snd_three

noncomputable abbrev order84_chiC2C6_fst_two_snd_two : order84_HB →* (ZMod 7)ˣ :=
  order84_chiC2C6_fst_two * order84_chiC2C6_snd_two

noncomputable abbrev order84_chiC2C6_fst_two_snd_three_inv : order84_HB →* (ZMod 7)ˣ :=
  order84_chiC2C6_fst_two * order84_chiC2C6_snd_three_inv

noncomputable abbrev order84_chiC2C6_fst_two_snd_six_inv : order84_HB →* (ZMod 7)ˣ :=
  order84_chiC2C6_fst_two * order84_chiC2C6_snd_six_inv

@[simp]
theorem order84_c2UnitHom_gen :
    order84_c2UnitHom (Multiplicative.ofAdd (1 : ZMod 2)) = order84_u6 ^ 3 := by
  decide

@[simp]
theorem order84_powHom_zmod6_gen (c : (ZMod 7)ˣ) (hc : c ^ 6 = 1) :
    powHom (p := 7) (q := 6) c hc (Multiplicative.ofAdd (1 : ZMod 6)) = c := by
  change c ^ (1 : ZMod 6).val = c
  haveI : Fact (1 < 6) := ⟨by norm_num⟩
  rw [ZMod.val_one]
  simp

@[simp]
theorem order84_chiC2C6_snd_six_g6 :
    order84_chiC2C6_snd_six (1, Multiplicative.ofAdd (1 : ZMod 6)) = order84_u6 := by
  decide

@[simp]
theorem order84_chiC2C6_snd_three_g6 :
    order84_chiC2C6_snd_three (1, Multiplicative.ofAdd (1 : ZMod 6)) =
      order84_u6 ^ 2 := by
  decide

@[simp]
theorem order84_chiC2C6_snd_two_g6 :
    order84_chiC2C6_snd_two (1, Multiplicative.ofAdd (1 : ZMod 6)) =
      order84_u6 ^ 3 := by
  decide

@[simp]
theorem order84_chiC2C6_snd_three_inv_g6 :
    order84_chiC2C6_snd_three_inv (1, Multiplicative.ofAdd (1 : ZMod 6)) =
      order84_u6 ^ 4 := by
  decide

@[simp]
theorem order84_chiC2C6_snd_six_inv_g6 :
    order84_chiC2C6_snd_six_inv (1, Multiplicative.ofAdd (1 : ZMod 6)) =
      order84_u6 ^ 5 := by
  decide

/-- Homomorphisms out of `C₂ × C₆` are determined by the two standard generators. -/
theorem order84_c2c6_hom_ext {M : Type} [Group M] {χ ψ : order84_HB →* M}
    (h2 : χ (Multiplicative.ofAdd (1 : ZMod 2), 1) =
      ψ (Multiplicative.ofAdd (1 : ZMod 2), 1))
    (h6 : χ (1, Multiplicative.ofAdd (1 : ZMod 6)) =
      ψ (1, Multiplicative.ofAdd (1 : ZMod 6))) :
    χ = ψ := by
  apply MonoidHom.ext
  rintro ⟨x2, x6⟩
  obtain ⟨a, rfl⟩ := Multiplicative.ofAdd.surjective x2
  obtain ⟨b, rfl⟩ := Multiplicative.ofAdd.surjective x6
  let g2 : order84_HB := (Multiplicative.ofAdd (1 : ZMod 2), 1)
  let g6 : order84_HB := (1, Multiplicative.ofAdd (1 : ZMod 6))
  have ha : Multiplicative.ofAdd a = (Multiplicative.ofAdd (1 : ZMod 2)) ^ a.val := by
    calc
      Multiplicative.ofAdd a = Multiplicative.ofAdd ((a.val : ZMod 2)) := by
        rw [ZMod.natCast_zmod_val]
      _ = Multiplicative.ofAdd (a.val • (1 : ZMod 2)) := by simp
      _ = (Multiplicative.ofAdd (1 : ZMod 2)) ^ a.val := by rw [ofAdd_nsmul]
  have hb : Multiplicative.ofAdd b = (Multiplicative.ofAdd (1 : ZMod 6)) ^ b.val := by
    calc
      Multiplicative.ofAdd b = Multiplicative.ofAdd ((b.val : ZMod 6)) := by
        rw [ZMod.natCast_zmod_val]
      _ = Multiplicative.ofAdd (b.val • (1 : ZMod 6)) := by simp
      _ = (Multiplicative.ofAdd (1 : ZMod 6)) ^ b.val := by rw [ofAdd_nsmul]
  have hx : (Multiplicative.ofAdd a, Multiplicative.ofAdd b) = g2 ^ a.val * g6 ^ b.val := by
    simp [g2, g6, Prod.pow_mk, ha, hb]
  rw [hx, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, h2, h6]

/-- Actions `C₂ × C₆ → Aut(C₇)` are the twelve displayed unit actions. -/
theorem order84_c2c6_action_cases (φ : order84_HB →* MulAut order84_C7) :
    φ = 1 ∨ φ = order84_action order84_chiC2C6_snd_six ∨
      φ = order84_action order84_chiC2C6_snd_three ∨
      φ = order84_action order84_chiC2C6_snd_two ∨
      φ = order84_action order84_chiC2C6_snd_three_inv ∨
      φ = order84_action order84_chiC2C6_snd_six_inv ∨
      φ = order84_action order84_chiC2C6_fst_two ∨
      φ = order84_action order84_chiC2C6_fst_two_snd_six ∨
      φ = order84_action order84_chiC2C6_fst_two_snd_three ∨
      φ = order84_action order84_chiC2C6_fst_two_snd_two ∨
      φ = order84_action order84_chiC2C6_fst_two_snd_three_inv ∨
      φ = order84_action order84_chiC2C6_fst_two_snd_six_inv := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let g2 : order84_HB := (Multiplicative.ofAdd (1 : ZMod 2), 1)
  let g6 : order84_HB := (1, Multiplicative.ofAdd (1 : ZMod 6))
  obtain ⟨u, hu6⟩ := exists_unitAutHom_eq (p := 7) (φ g6)
  have hsq2 : (φ g2) ^ 2 = 1 := by
    rw [← map_pow, show g2 ^ 2 = 1 by decide, map_one]
  rcases order84_mulAut_sq_eq_one_cases (φ g2) hsq2 with h2 | h2 <;>
    rcases order84_unit_cases u with h6 | h6 | h6 | h6 | h6 | h6
  · left
    apply order84_c2c6_hom_ext <;>
      simp [g2, g6, hu6, h2, h6]
  · right; left
    apply order84_c2c6_hom_ext <;>
      simp [g2, g6, hu6, h2, h6]
  · right; right; left
    apply order84_c2c6_hom_ext <;>
      simp [g2, g6, hu6, h2, h6]
  · right; right; right; left
    apply order84_c2c6_hom_ext <;>
      simp [g2, g6, hu6, h2, h6]
  · right; right; right; right; left
    apply order84_c2c6_hom_ext <;>
      simp [g2, g6, hu6, h2, h6]
  · right; right; right; right; right; left
    apply order84_c2c6_hom_ext <;>
      simp [g2, g6, hu6, h2, h6]
  · right; right; right; right; right; right; left
    apply order84_c2c6_hom_ext <;>
      simp [g2, g6, hu6, h2, h6]
  · right; right; right; right; right; right; right; left
    apply order84_c2c6_hom_ext <;>
      simp [g2, g6, hu6, h2, h6]
  · right; right; right; right; right; right; right; right; left
    apply order84_c2c6_hom_ext <;>
      simp [g2, g6, hu6, h2, h6]
  · right; right; right; right; right; right; right; right; right; left
    apply order84_c2c6_hom_ext <;>
      simp [g2, g6, hu6, h2, h6]
  · right; right; right; right; right; right; right; right; right; right; left
    apply order84_c2c6_hom_ext <;>
      simp [g2, g6, hu6, h2, h6]
  · right; right; right; right; right; right; right; right; right; right; right
    apply order84_c2c6_hom_ext <;>
      simp [g2, g6, hu6, h2, h6]

/-! ### `(C₃ ⋊ C₄)`-complement actions -/

noncomputable abbrev order84_chiHC_two : order84_HC →* (ZMod 7)ˣ :=
  (powHom (p := 7) (q := 4) (order84_u6 ^ 3) (by decide)).comp
    SemidirectProduct.rightHom

@[simp]
theorem order84_powHom_zmod4_gen (c : (ZMod 7)ˣ) (hc : c ^ 4 = 1) :
    powHom (p := 7) (q := 4) c hc (Multiplicative.ofAdd (1 : ZMod 4)) = c := by
  change c ^ (1 : ZMod 4).val = c
  haveI : Fact (1 < 4) := ⟨by norm_num⟩
  rw [ZMod.val_one]
  simp

/-- Homomorphisms out of `C₃ ⋊ C₄` are determined by the two standard generators. -/
theorem order84_hc_hom_ext {M : Type} [Group M] {χ ψ : order84_HC →* M}
    (h3 : χ (SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 3))) =
      ψ (SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 3))))
    (h4 : χ (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 4))) =
      ψ (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 4)))) :
    χ = ψ := by
  apply SemidirectProduct.hom_ext
  · apply MonoidHom.ext
    intro x
    obtain ⟨a, rfl⟩ := Multiplicative.ofAdd.surjective x
    have hx : Multiplicative.ofAdd a = (Multiplicative.ofAdd (1 : ZMod 3)) ^ a.val := by
      calc
        Multiplicative.ofAdd a = Multiplicative.ofAdd ((a.val : ZMod 3)) := by
          rw [ZMod.natCast_zmod_val]
        _ = Multiplicative.ofAdd (a.val • (1 : ZMod 3)) := by simp
        _ = (Multiplicative.ofAdd (1 : ZMod 3)) ^ a.val := by rw [ofAdd_nsmul]
    rw [hx, map_pow, map_pow]
    simpa using congrArg (fun y : M => y ^ a.val) h3
  · apply MonoidHom.ext
    intro x
    obtain ⟨a, rfl⟩ := Multiplicative.ofAdd.surjective x
    have hx : Multiplicative.ofAdd a = (Multiplicative.ofAdd (1 : ZMod 4)) ^ a.val := by
      calc
        Multiplicative.ofAdd a = Multiplicative.ofAdd ((a.val : ZMod 4)) := by
          rw [ZMod.natCast_zmod_val]
        _ = Multiplicative.ofAdd (a.val • (1 : ZMod 4)) := by simp
        _ = (Multiplicative.ofAdd (1 : ZMod 4)) ^ a.val := by rw [ofAdd_nsmul]
    rw [hx, map_pow, map_pow]
    simpa using congrArg (fun y : M => y ^ a.val) h4

theorem order84_hc_inl_generator_maps_trivially
    (φ : order84_HC →* MulAut order84_C7) :
    φ (SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 3))) = 1 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let a : order84_HC := SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 3))
  let b : order84_HC := SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 4))
  have hrel : b * a * b⁻¹ = a⁻¹ := by decide
  have hφrel : φ b * φ a * (φ b)⁻¹ = (φ a)⁻¹ := by
    simpa [a, b, map_mul] using congrArg (fun x => φ x) hrel
  have hleft : φ b * φ a * (φ b)⁻¹ = φ a := by
    rw [order84_mulAut_comm (φ b) (φ a)]
    group
  have ha_inv : φ a = (φ a)⁻¹ := hleft.symm.trans hφrel
  have ha2 : (φ a) ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [ha_inv]
    exact mul_inv_cancel _
  rcases order84_mulAut_sq_eq_one_cases (φ a) ha2 with ha | ha
  · simpa [a] using ha
  · have ha3 : (φ a) ^ 3 = 1 := by
      rw [← map_pow, show a ^ 3 = 1 by decide, map_one]
    rw [ha] at ha3
    have hunit : (order84_u6 ^ 3) ^ 3 = (1 : (ZMod 7)ˣ) := by
      apply unitAutHom_injective (p := 7)
      rw [map_pow, map_one]
      exact ha3
    exact False.elim (order84_u6_pow3_pow3_ne_one hunit)

/-- Actions `(C₃ ⋊ C₄) → Aut(C₇)` are either trivial or factor through the order-`2`
quotient of the `C₄` factor. -/
theorem order84_hc_action_cases (φ : order84_HC →* MulAut order84_C7) :
    φ = 1 ∨ φ = order84_action order84_chiHC_two := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let a : order84_HC := SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 3))
  let b : order84_HC := SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 4))
  have ha : φ a = 1 := by
    simpa [a] using order84_hc_inl_generator_maps_trivially φ
  obtain ⟨u, hu⟩ := exists_unitAutHom_eq (p := 7) (φ b)
  have hu4 : u ^ 4 = 1 := by
    apply unitAutHom_injective (p := 7)
    rw [map_pow, ← hu, ← map_pow, show b ^ 4 = 1 by decide, map_one, map_one]
  rcases order84_unit_cases u with h | h | h | h | h | h
  · left
    apply order84_hc_hom_ext <;>
      simp [a, b, ha, hu, h]
  · exfalso
    have hbad : order84_u6 ^ 4 = (1 : (ZMod 7)ˣ) := by simpa [h] using hu4
    exact order84_u6_pow4_ne_one hbad
  · exfalso
    have hbad : (order84_u6 ^ 2) ^ 4 = (1 : (ZMod 7)ˣ) := by simpa [h] using hu4
    exact order84_u6_pow2_pow4_ne_one hbad
  · right
    apply order84_hc_hom_ext <;>
      simp [a, b, ha, hu, h]
  · exfalso
    have hbad : (order84_u6 ^ 4) ^ 4 = (1 : (ZMod 7)ˣ) := by simpa [h] using hu4
    exact order84_u6_pow4_pow4_ne_one hbad
  · exfalso
    have hbad : (order84_u6 ^ 5) ^ 4 = (1 : (ZMod 7)ˣ) := by simpa [h] using hu4
    exact order84_u6_pow5_pow4_ne_one hbad

/-! ### `(C₂ × D₆)`-complement actions -/

/-- The `D₆ → (ZMod 7)ˣ` character non-trivial on reflections. -/
noncomputable def order84_chiD3_ref : DihedralGroup 3 →* (ZMod 7)ˣ where
  toFun
    | DihedralGroup.r _ => 1
    | DihedralGroup.sr _ => order84_u6 ^ 3
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j)
    · rfl
    · simp [DihedralGroup.r_mul_sr]
    · simp [DihedralGroup.sr_mul_r]
    · simp only [DihedralGroup.sr_mul_sr]
      decide

noncomputable abbrev order84_chiHD_fst_two : order84_HD →* (ZMod 7)ˣ :=
  order84_c2UnitHom.comp
    (MonoidHom.fst (Multiplicative (ZMod 2)) (DihedralGroup 3))

noncomputable abbrev order84_chiHD_ref : order84_HD →* (ZMod 7)ˣ :=
  order84_chiD3_ref.comp
    (MonoidHom.snd (Multiplicative (ZMod 2)) (DihedralGroup 3))

noncomputable abbrev order84_chiHD_prod : order84_HD →* (ZMod 7)ˣ :=
  order84_chiHD_fst_two * order84_chiHD_ref

@[simp]
theorem order84_chiD3_ref_r1 :
    order84_chiD3_ref (DihedralGroup.r (1 : ZMod 3)) = 1 := by
  rfl

@[simp]
theorem order84_chiD3_ref_s0 :
    order84_chiD3_ref (DihedralGroup.sr (0 : ZMod 3)) = order84_u6 ^ 3 := by
  rfl

/-- Homomorphisms out of `D₆` are determined by a rotation and a reflection. -/
theorem order84_d3_hom_ext {M : Type} [Group M] {χ ψ : DihedralGroup 3 →* M}
    (hr : χ (DihedralGroup.r (1 : ZMod 3)) =
      ψ (DihedralGroup.r (1 : ZMod 3)))
    (hs : χ (DihedralGroup.sr (0 : ZMod 3)) =
      ψ (DihedralGroup.sr (0 : ZMod 3))) :
    χ = ψ := by
  apply MonoidHom.ext
  intro x
  rcases x with i | i
  · have hi : DihedralGroup.r i = (DihedralGroup.r (1 : ZMod 3)) ^ i.val := by
      calc
        DihedralGroup.r i = DihedralGroup.r ((i.val : ZMod 3)) := by
          rw [ZMod.natCast_zmod_val]
        _ = DihedralGroup.r ((1 : ZMod 3) * (i.val : ZMod 3)) := by simp
        _ = (DihedralGroup.r (1 : ZMod 3)) ^ i.val := by rw [DihedralGroup.r_pow]
    rw [hi, map_pow, map_pow, hr]
  · have hri : DihedralGroup.r i = (DihedralGroup.r (1 : ZMod 3)) ^ i.val := by
      calc
        DihedralGroup.r i = DihedralGroup.r ((i.val : ZMod 3)) := by
          rw [ZMod.natCast_zmod_val]
        _ = DihedralGroup.r ((1 : ZMod 3) * (i.val : ZMod 3)) := by simp
        _ = (DihedralGroup.r (1 : ZMod 3)) ^ i.val := by rw [DihedralGroup.r_pow]
    have hi : DihedralGroup.sr i =
        DihedralGroup.sr (0 : ZMod 3) * (DihedralGroup.r (1 : ZMod 3)) ^ i.val := by
      rw [← hri]
      simp [DihedralGroup.sr_mul_r]
    rw [hi, map_mul, map_mul, map_pow, map_pow, hs, hr]

/-- Homomorphisms out of `C₂ × D₆` are determined by the `C₂` generator, a rotation,
and a reflection. -/
theorem order84_hd_hom_ext {M : Type} [Group M] {χ ψ : order84_HD →* M}
    (h2 : χ (Multiplicative.ofAdd (1 : ZMod 2), 1) =
      ψ (Multiplicative.ofAdd (1 : ZMod 2), 1))
    (hr : χ (1, DihedralGroup.r (1 : ZMod 3)) =
      ψ (1, DihedralGroup.r (1 : ZMod 3)))
    (hs : χ (1, DihedralGroup.sr (0 : ZMod 3)) =
      ψ (1, DihedralGroup.sr (0 : ZMod 3))) :
    χ = ψ := by
  apply MonoidHom.ext
  rintro ⟨x2, xd⟩
  obtain ⟨a, rfl⟩ := Multiplicative.ofAdd.surjective x2
  let g2 : order84_HD := (Multiplicative.ofAdd (1 : ZMod 2), 1)
  let gr : order84_HD := (1, DihedralGroup.r (1 : ZMod 3))
  let gs : order84_HD := (1, DihedralGroup.sr (0 : ZMod 3))
  have ha : Multiplicative.ofAdd a = (Multiplicative.ofAdd (1 : ZMod 2)) ^ a.val := by
    calc
      Multiplicative.ofAdd a = Multiplicative.ofAdd ((a.val : ZMod 2)) := by
        rw [ZMod.natCast_zmod_val]
      _ = Multiplicative.ofAdd (a.val • (1 : ZMod 2)) := by simp
      _ = (Multiplicative.ofAdd (1 : ZMod 2)) ^ a.val := by rw [ofAdd_nsmul]
  rcases xd with i | i
  · have hri : DihedralGroup.r i = (DihedralGroup.r (1 : ZMod 3)) ^ i.val := by
      calc
        DihedralGroup.r i = DihedralGroup.r ((i.val : ZMod 3)) := by
          rw [ZMod.natCast_zmod_val]
        _ = DihedralGroup.r ((1 : ZMod 3) * (i.val : ZMod 3)) := by simp
        _ = (DihedralGroup.r (1 : ZMod 3)) ^ i.val := by rw [DihedralGroup.r_pow]
    have hx : (Multiplicative.ofAdd a, DihedralGroup.r i) = g2 ^ a.val * gr ^ i.val := by
      calc
        (Multiplicative.ofAdd a, DihedralGroup.r i)
            = ((Multiplicative.ofAdd (1 : ZMod 2)) ^ a.val,
                (DihedralGroup.r (1 : ZMod 3)) ^ i.val) := by
              rw [← ha, ← hri]
        _ = g2 ^ a.val * gr ^ i.val := by
              rw [Prod.pow_mk, Prod.pow_mk]
              simp only [one_pow, Prod.mk_mul_mk, mul_one, one_mul]
    rw [hx, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, h2, hr]
  · have hri : DihedralGroup.r i = (DihedralGroup.r (1 : ZMod 3)) ^ i.val := by
      calc
        DihedralGroup.r i = DihedralGroup.r ((i.val : ZMod 3)) := by
          rw [ZMod.natCast_zmod_val]
        _ = DihedralGroup.r ((1 : ZMod 3) * (i.val : ZMod 3)) := by simp
        _ = (DihedralGroup.r (1 : ZMod 3)) ^ i.val := by rw [DihedralGroup.r_pow]
    have hsi : DihedralGroup.sr i =
        DihedralGroup.sr (0 : ZMod 3) * (DihedralGroup.r (1 : ZMod 3)) ^ i.val := by
      rw [← hri]
      simp [DihedralGroup.sr_mul_r]
    have hx : (Multiplicative.ofAdd a, DihedralGroup.sr i) =
        g2 ^ a.val * gs * gr ^ i.val := by
      calc
        (Multiplicative.ofAdd a, DihedralGroup.sr i)
            = ((Multiplicative.ofAdd (1 : ZMod 2)) ^ a.val,
                DihedralGroup.sr (0 : ZMod 3) *
                  (DihedralGroup.r (1 : ZMod 3)) ^ i.val) := by
              rw [← ha, ← hsi]
        _ = g2 ^ a.val * gs * gr ^ i.val := by
              rw [Prod.pow_mk, Prod.pow_mk]
              simp only [gs, one_pow, Prod.mk_mul_mk, mul_one, one_mul]
    rw [hx, map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow,
      h2, hs, hr]

theorem order84_hd_rotation_maps_trivially
    (φ : order84_HD →* MulAut order84_C7) :
    φ (1, DihedralGroup.r (1 : ZMod 3)) = 1 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let r : order84_HD := (1, DihedralGroup.r (1 : ZMod 3))
  let s : order84_HD := (1, DihedralGroup.sr (0 : ZMod 3))
  have hrel : s * r * s⁻¹ = r⁻¹ := by decide
  have hφrel : φ s * φ r * (φ s)⁻¹ = (φ r)⁻¹ := by
    simpa only [map_mul, map_inv] using congrArg (fun x => φ x) hrel
  have hleft : φ s * φ r * (φ s)⁻¹ = φ r := by
    rw [order84_mulAut_comm (φ s) (φ r)]
    group
  have hr_inv : φ r = (φ r)⁻¹ := hleft.symm.trans hφrel
  have hr2 : (φ r) ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [hr_inv]
    exact mul_inv_cancel _
  rcases order84_mulAut_sq_eq_one_cases (φ r) hr2 with hr | hr
  · simpa [r] using hr
  · have hr3 : (φ r) ^ 3 = 1 := by
      rw [← map_pow, show r ^ 3 = 1 by decide, map_one]
    rw [hr] at hr3
    have hunit : (order84_u6 ^ 3) ^ 3 = (1 : (ZMod 7)ˣ) := by
      apply unitAutHom_injective (p := 7)
      rw [map_pow, map_one]
      exact hr3
    exact False.elim (order84_u6_pow3_pow3_ne_one hunit)

/-- Actions `C₂ × D₆ → Aut(C₇)` are the four displayed unit actions. -/
theorem order84_hd_action_cases (φ : order84_HD →* MulAut order84_C7) :
    φ = 1 ∨ φ = order84_action order84_chiHD_fst_two ∨
      φ = order84_action order84_chiHD_ref ∨
      φ = order84_action order84_chiHD_prod := by
  let g2 : order84_HD := (Multiplicative.ofAdd (1 : ZMod 2), 1)
  let gr : order84_HD := (1, DihedralGroup.r (1 : ZMod 3))
  let gs : order84_HD := (1, DihedralGroup.sr (0 : ZMod 3))
  have hr : φ gr = 1 := by
    simpa [gr] using order84_hd_rotation_maps_trivially φ
  have hg2sq : (φ g2) ^ 2 = 1 := by
    rw [← map_pow, show g2 ^ 2 = 1 by decide, map_one]
  have hgssq : (φ gs) ^ 2 = 1 := by
    rw [← map_pow, show gs ^ 2 = 1 by decide, map_one]
  rcases order84_mulAut_sq_eq_one_cases (φ g2) hg2sq with h2 | h2 <;>
    rcases order84_mulAut_sq_eq_one_cases (φ gs) hgssq with hs | hs
  · left
    apply order84_hd_hom_ext <;>
      simp [g2, gr, gs, h2, hr, hs]
  · right; right; left
    apply order84_hd_hom_ext <;>
      simp [g2, gr, gs, h2, hr, hs]
  · right; left
    apply order84_hd_hom_ext <;>
      simp [g2, gr, gs, h2, hr, hs]
  · right; right; right
    apply order84_hd_hom_ext <;>
      simp [g2, gr, gs, h2, hr, hs]

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
