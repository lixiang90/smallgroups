/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order4P_12
import Smallgroups.UsefulTheorems.PrimeOrderClassification
import Smallgroups.UsefulTheorems.SchurZassenhaus
import Smallgroups.UsefulTheorems.SemidirectProductClassify
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
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

theorem order84_unit_cube_eq_one_cases (u : (ZMod 7)ˣ) (hu : u ^ 3 = 1) :
    u = 1 ∨ u = order84_u6 ^ 2 ∨ u = order84_u6 ^ 4 := by
  rcases order84_unit_cases u with h | h | h | h | h | h
  · exact Or.inl h
  · exfalso
    have hbad : order84_u6 ^ 3 = (1 : (ZMod 7)ˣ) := by simpa [h] using hu
    exact (by decide : order84_u6 ^ 3 ≠ (1 : (ZMod 7)ˣ)) hbad
  · exact Or.inr <| Or.inl h
  · exfalso
    have hbad : (order84_u6 ^ 3) ^ 3 = (1 : (ZMod 7)ˣ) := by simpa [h] using hu
    exact order84_u6_pow3_pow3_ne_one hbad
  · exact Or.inr <| Or.inr h
  · exfalso
    have hbad : (order84_u6 ^ 5) ^ 3 = (1 : (ZMod 7)ˣ) := by simpa [h] using hu
    exact (by decide : (order84_u6 ^ 5) ^ 3 ≠ (1 : (ZMod 7)ˣ)) hbad

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

theorem order84_mulAut_cube_eq_one_cases (α : MulAut order84_C7) (hα : α ^ 3 = 1) :
    α = 1 ∨ α = unitAutHom (order84_u6 ^ 2) ∨ α = unitAutHom (order84_u6 ^ 4) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨u, hu⟩ := exists_unitAutHom_eq (p := 7) α
  have hu3 : u ^ 3 = 1 := by
    apply unitAutHom_injective (p := 7)
    rw [map_pow, ← hu, hα, map_one]
  rcases order84_unit_cube_eq_one_cases u hu3 with h | h | h
  · left
    rw [hu, h]
    exact map_one (unitAutHom (p := 7))
  · right; left
    rw [hu, h]
  · right; right
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

/-! ### Automorphism orbits for `C₂ × C₆`-complement actions -/

noncomputable def order84_HB_mulFive : order84_HB ≃* order84_HB :=
  MulEquiv.prodCongr (MulEquiv.refl (Multiplicative (ZMod 2)))
    (unitAutHom (p := 6) (ZMod.unitOfCoprime 5 (by norm_num : Nat.Coprime 5 6)))

noncomputable def order84_HB_shearRight : order84_HB ≃* order84_HB where
  toFun x :=
    (Multiplicative.ofAdd (Multiplicative.toAdd x.1 +
      ZMod.castHom (by norm_num : 2 ∣ 6) (ZMod 2) (Multiplicative.toAdd x.2)), x.2)
  invFun x :=
    (Multiplicative.ofAdd (Multiplicative.toAdd x.1 +
      ZMod.castHom (by norm_num : 2 ∣ 6) (ZMod 2) (Multiplicative.toAdd x.2)), x.2)
  left_inv := by
    rintro ⟨a, b⟩
    ext <;> decide +revert
  right_inv := by
    rintro ⟨a, b⟩
    ext <;> decide +revert
  map_mul' := by
    rintro ⟨a, b⟩ ⟨c, d⟩
    ext <;> decide +revert

noncomputable def order84_HB_shearLeft : order84_HB ≃* order84_HB where
  toFun x :=
    (x.1, Multiplicative.ofAdd (Multiplicative.toAdd x.2 +
      (3 : ZMod 6) * ((Multiplicative.toAdd x.1).val : ZMod 6)))
  invFun x :=
    (x.1, Multiplicative.ofAdd (Multiplicative.toAdd x.2 +
      (3 : ZMod 6) * ((Multiplicative.toAdd x.1).val : ZMod 6)))
  left_inv := by
    rintro ⟨a, b⟩
    ext <;> decide +revert
  right_inv := by
    rintro ⟨a, b⟩
    ext <;> decide +revert
  map_mul' := by
    rintro ⟨a, b⟩ ⟨c, d⟩
    ext <;> decide +revert

theorem order84_chiC2C6_snd_six_comp_mulFive :
    order84_chiC2C6_snd_six.comp order84_HB_mulFive.toMonoidHom =
      order84_chiC2C6_snd_six_inv := by
  apply order84_c2c6_hom_ext <;> decide

theorem order84_chiC2C6_snd_three_comp_mulFive :
    order84_chiC2C6_snd_three.comp order84_HB_mulFive.toMonoidHom =
      order84_chiC2C6_snd_three_inv := by
  apply order84_c2c6_hom_ext <;> decide

theorem order84_chiC2C6_snd_two_comp_mulFive :
    order84_chiC2C6_snd_two.comp order84_HB_mulFive.toMonoidHom =
      order84_chiC2C6_snd_two := by
  apply order84_c2c6_hom_ext <;> decide

theorem order84_chiC2C6_fst_two_snd_six_comp_mulFive :
    order84_chiC2C6_fst_two_snd_six.comp order84_HB_mulFive.toMonoidHom =
      order84_chiC2C6_fst_two_snd_six_inv := by
  apply order84_c2c6_hom_ext <;> decide

theorem order84_chiC2C6_fst_two_snd_three_comp_mulFive :
    order84_chiC2C6_fst_two_snd_three.comp order84_HB_mulFive.toMonoidHom =
      order84_chiC2C6_fst_two_snd_three_inv := by
  apply order84_c2c6_hom_ext <;> decide

theorem order84_chiC2C6_fst_two_snd_two_comp_mulFive :
    order84_chiC2C6_fst_two_snd_two.comp order84_HB_mulFive.toMonoidHom =
      order84_chiC2C6_fst_two_snd_two := by
  apply order84_c2c6_hom_ext <;> decide

theorem order84_chiC2C6_fst_two_comp_shearRight :
    order84_chiC2C6_fst_two.comp order84_HB_shearRight.toMonoidHom =
      order84_chiC2C6_fst_two_snd_two := by
  apply order84_c2c6_hom_ext <;> decide

theorem order84_chiC2C6_snd_two_comp_shearLeft :
    order84_chiC2C6_snd_two.comp order84_HB_shearLeft.toMonoidHom =
      order84_chiC2C6_fst_two_snd_two := by
  apply order84_c2c6_hom_ext <;> decide

theorem order84_chiC2C6_snd_six_comp_shearLeft :
    order84_chiC2C6_snd_six.comp order84_HB_shearLeft.toMonoidHom =
      order84_chiC2C6_fst_two_snd_six := by
  apply order84_c2c6_hom_ext <;> decide

theorem order84_chiC2C6_fst_two_snd_three_comp_shearRight :
    order84_chiC2C6_fst_two_snd_three.comp order84_HB_shearRight.toMonoidHom =
      order84_chiC2C6_fst_two_snd_six_inv := by
  apply order84_c2c6_hom_ext <;> decide

noncomputable abbrev order84_c2c6_trivial : Type :=
  order84_C7 × order84_HB

noncomputable abbrev order84_c2c6_snd_six : Type :=
  SemidirectProduct order84_C7 order84_HB (order84_action order84_chiC2C6_snd_six)

noncomputable abbrev order84_c2c6_snd_three : Type :=
  SemidirectProduct order84_C7 order84_HB (order84_action order84_chiC2C6_snd_three)

noncomputable abbrev order84_c2c6_snd_two : Type :=
  SemidirectProduct order84_C7 order84_HB (order84_action order84_chiC2C6_snd_two)

noncomputable abbrev order84_c2c6_fst_two : Type :=
  SemidirectProduct order84_C7 order84_HB (order84_action order84_chiC2C6_fst_two)

noncomputable abbrev order84_c2c6_fst_two_snd_six : Type :=
  SemidirectProduct order84_C7 order84_HB (order84_action order84_chiC2C6_fst_two_snd_six)

noncomputable abbrev order84_c2c6_fst_two_snd_three : Type :=
  SemidirectProduct order84_C7 order84_HB (order84_action order84_chiC2C6_fst_two_snd_three)

noncomputable abbrev order84_c2c6_fst_two_snd_two : Type :=
  SemidirectProduct order84_C7 order84_HB (order84_action order84_chiC2C6_fst_two_snd_two)

noncomputable def order84_c2c6_snd_six_inv_equiv_snd_six :
    SemidirectProduct order84_C7 order84_HB
        (order84_action order84_chiC2C6_snd_six_inv) ≃*
      order84_c2c6_snd_six :=
  order84_action_precomp_eq_mulEquiv order84_chiC2C6_snd_six
    order84_chiC2C6_snd_six_inv order84_HB_mulFive
    order84_chiC2C6_snd_six_comp_mulFive

noncomputable def order84_c2c6_snd_three_inv_equiv_snd_three :
    SemidirectProduct order84_C7 order84_HB
        (order84_action order84_chiC2C6_snd_three_inv) ≃*
      order84_c2c6_snd_three :=
  order84_action_precomp_eq_mulEquiv order84_chiC2C6_snd_three
    order84_chiC2C6_snd_three_inv order84_HB_mulFive
    order84_chiC2C6_snd_three_comp_mulFive

noncomputable def order84_c2c6_fst_two_snd_six_inv_equiv_fst_two_snd_six :
    SemidirectProduct order84_C7 order84_HB
        (order84_action order84_chiC2C6_fst_two_snd_six_inv) ≃*
      order84_c2c6_fst_two_snd_six :=
  order84_action_precomp_eq_mulEquiv order84_chiC2C6_fst_two_snd_six
    order84_chiC2C6_fst_two_snd_six_inv order84_HB_mulFive
    order84_chiC2C6_fst_two_snd_six_comp_mulFive

noncomputable def order84_c2c6_fst_two_snd_three_inv_equiv_fst_two_snd_three :
    SemidirectProduct order84_C7 order84_HB
        (order84_action order84_chiC2C6_fst_two_snd_three_inv) ≃*
      order84_c2c6_fst_two_snd_three :=
  order84_action_precomp_eq_mulEquiv order84_chiC2C6_fst_two_snd_three
    order84_chiC2C6_fst_two_snd_three_inv order84_HB_mulFive
    order84_chiC2C6_fst_two_snd_three_comp_mulFive

noncomputable def order84_c2c6_fst_two_snd_two_equiv_fst_two :
    order84_c2c6_fst_two_snd_two ≃* order84_c2c6_fst_two :=
  order84_action_precomp_eq_mulEquiv order84_chiC2C6_fst_two
    order84_chiC2C6_fst_two_snd_two order84_HB_shearRight
    order84_chiC2C6_fst_two_comp_shearRight

noncomputable def order84_c2c6_snd_two_equiv_fst_two :
    order84_c2c6_snd_two ≃* order84_c2c6_fst_two :=
  (order84_action_precomp_eq_mulEquiv order84_chiC2C6_snd_two
      order84_chiC2C6_fst_two_snd_two order84_HB_shearLeft
      order84_chiC2C6_snd_two_comp_shearLeft).symm.trans
    order84_c2c6_fst_two_snd_two_equiv_fst_two

noncomputable def order84_c2c6_snd_six_equiv_fst_two_snd_six :
    order84_c2c6_snd_six ≃* order84_c2c6_fst_two_snd_six :=
  (order84_action_precomp_eq_mulEquiv order84_chiC2C6_snd_six
      order84_chiC2C6_fst_two_snd_six order84_HB_shearLeft
      order84_chiC2C6_snd_six_comp_shearLeft).symm

noncomputable def order84_c2c6_fst_two_snd_three_equiv_fst_two_snd_six :
    order84_c2c6_fst_two_snd_three ≃* order84_c2c6_fst_two_snd_six :=
  (order84_action_precomp_eq_mulEquiv order84_chiC2C6_fst_two_snd_three
      order84_chiC2C6_fst_two_snd_six_inv order84_HB_shearRight
      order84_chiC2C6_fst_two_snd_three_comp_shearRight).symm.trans
    order84_c2c6_fst_two_snd_six_inv_equiv_fst_two_snd_six

theorem order84_c2c6_action_semidirect_cases (φ : order84_HB →* MulAut order84_C7) :
    Nonempty (SemidirectProduct order84_C7 order84_HB φ ≃* order84_c2c6_trivial) ∨
      Nonempty (SemidirectProduct order84_C7 order84_HB φ ≃* order84_c2c6_snd_six) ∨
      Nonempty (SemidirectProduct order84_C7 order84_HB φ ≃* order84_c2c6_snd_three) ∨
      Nonempty (SemidirectProduct order84_C7 order84_HB φ ≃* order84_c2c6_snd_two) ∨
      Nonempty (SemidirectProduct order84_C7 order84_HB φ ≃* order84_c2c6_fst_two) ∨
      Nonempty (SemidirectProduct order84_C7 order84_HB φ ≃*
        order84_c2c6_fst_two_snd_six) ∨
      Nonempty (SemidirectProduct order84_C7 order84_HB φ ≃*
        order84_c2c6_fst_two_snd_three) ∨
      Nonempty (SemidirectProduct order84_C7 order84_HB φ ≃*
        order84_c2c6_fst_two_snd_two) := by
  rcases order84_c2c6_action_cases φ with hφ | hφ | hφ | hφ | hφ | hφ |
    hφ | hφ | hφ | hφ | hφ | hφ
  · left
    exact ⟨(semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd⟩
  · right; left
    exact ⟨semidirectProductCongr_eq hφ⟩
  · right; right; left
    exact ⟨semidirectProductCongr_eq hφ⟩
  · right; right; right; left
    exact ⟨semidirectProductCongr_eq hφ⟩
  · right; right; left
    exact ⟨(semidirectProductCongr_eq hφ).trans
      order84_c2c6_snd_three_inv_equiv_snd_three⟩
  · right; left
    exact ⟨(semidirectProductCongr_eq hφ).trans
      order84_c2c6_snd_six_inv_equiv_snd_six⟩
  · right; right; right; right; left
    exact ⟨semidirectProductCongr_eq hφ⟩
  · right; right; right; right; right; left
    exact ⟨semidirectProductCongr_eq hφ⟩
  · right; right; right; right; right; right; left
    exact ⟨semidirectProductCongr_eq hφ⟩
  · right; right; right; right; right; right; right
    exact ⟨semidirectProductCongr_eq hφ⟩
  · right; right; right; right; right; right; left
    exact ⟨(semidirectProductCongr_eq hφ).trans
      order84_c2c6_fst_two_snd_three_inv_equiv_fst_two_snd_three⟩
  · right; right; right; right; right; left
    exact ⟨(semidirectProductCongr_eq hφ).trans
      order84_c2c6_fst_two_snd_six_inv_equiv_fst_two_snd_six⟩

theorem order84_c2c6_action_semidirect_cases_four (φ : order84_HB →* MulAut order84_C7) :
    Nonempty (SemidirectProduct order84_C7 order84_HB φ ≃* order84_c2c6_trivial) ∨
      Nonempty (SemidirectProduct order84_C7 order84_HB φ ≃* order84_c2c6_fst_two) ∨
      Nonempty (SemidirectProduct order84_C7 order84_HB φ ≃* order84_c2c6_snd_three) ∨
      Nonempty (SemidirectProduct order84_C7 order84_HB φ ≃*
        order84_c2c6_fst_two_snd_six) := by
  rcases order84_c2c6_action_semidirect_cases φ with hφ | hφ | hφ | hφ |
    hφ | hφ | hφ | hφ
  · left
    exact hφ
  · right; right; right
    obtain ⟨e⟩ := hφ
    exact ⟨e.trans order84_c2c6_snd_six_equiv_fst_two_snd_six⟩
  · right; right; left
    exact hφ
  · right; left
    obtain ⟨e⟩ := hφ
    exact ⟨e.trans order84_c2c6_snd_two_equiv_fst_two⟩
  · right; left
    exact hφ
  · right; right; right
    exact hφ
  · right; right; right
    obtain ⟨e⟩ := hφ
    exact ⟨e.trans order84_c2c6_fst_two_snd_three_equiv_fst_two_snd_six⟩
  · right; left
    obtain ⟨e⟩ := hφ
    exact ⟨e.trans order84_c2c6_fst_two_snd_two_equiv_fst_two⟩

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

noncomputable abbrev order84_hc_trivial : Type :=
  order84_C7 × order84_HC

noncomputable abbrev order84_hc_two : Type :=
  SemidirectProduct order84_C7 order84_HC (order84_action order84_chiHC_two)

theorem order84_hc_action_semidirect_cases (φ : order84_HC →* MulAut order84_C7) :
    Nonempty (SemidirectProduct order84_C7 order84_HC φ ≃* order84_hc_trivial) ∨
      Nonempty (SemidirectProduct order84_C7 order84_HC φ ≃* order84_hc_two) := by
  rcases order84_hc_action_cases φ with hφ | hφ
  · left
    exact ⟨(semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd⟩
  · right
    exact ⟨semidirectProductCongr_eq hφ⟩

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

noncomputable abbrev order84_hd_trivial : Type :=
  order84_C7 × order84_HD

noncomputable abbrev order84_hd_fst_two : Type :=
  SemidirectProduct order84_C7 order84_HD (order84_action order84_chiHD_fst_two)

noncomputable abbrev order84_hd_ref : Type :=
  SemidirectProduct order84_C7 order84_HD (order84_action order84_chiHD_ref)

noncomputable abbrev order84_hd_prod : Type :=
  SemidirectProduct order84_C7 order84_HD (order84_action order84_chiHD_prod)

noncomputable def order84_HD_shearRef : order84_HD ≃* order84_HD where
  toFun x :=
    match x.2 with
    | DihedralGroup.r _ => x
    | DihedralGroup.sr _ => (x.1 * Multiplicative.ofAdd (1 : ZMod 2), x.2)
  invFun x :=
    match x.2 with
    | DihedralGroup.r _ => x
    | DihedralGroup.sr _ => (x.1 * Multiplicative.ofAdd (1 : ZMod 2), x.2)
  left_inv := by
    rintro ⟨a, d⟩
    rcases d with i | i <;> ext <;> decide +revert
  right_inv := by
    rintro ⟨a, d⟩
    rcases d with i | i <;> ext <;> decide +revert
  map_mul' := by
    rintro ⟨a, d⟩ ⟨b, e⟩
    rcases d with i | i <;> rcases e with j | j <;> ext <;> decide +revert

theorem order84_chiHD_fst_two_comp_shearRef :
    order84_chiHD_fst_two.comp order84_HD_shearRef.toMonoidHom = order84_chiHD_prod := by
  apply order84_hd_hom_ext <;> decide

noncomputable def order84_hd_prod_equiv_fst_two : order84_hd_prod ≃* order84_hd_fst_two :=
  order84_action_precomp_eq_mulEquiv order84_chiHD_fst_two order84_chiHD_prod
    order84_HD_shearRef order84_chiHD_fst_two_comp_shearRef

theorem order84_hd_action_semidirect_cases (φ : order84_HD →* MulAut order84_C7) :
    Nonempty (SemidirectProduct order84_C7 order84_HD φ ≃* order84_hd_trivial) ∨
      Nonempty (SemidirectProduct order84_C7 order84_HD φ ≃* order84_hd_fst_two) ∨
      Nonempty (SemidirectProduct order84_C7 order84_HD φ ≃* order84_hd_ref) ∨
      Nonempty (SemidirectProduct order84_C7 order84_HD φ ≃* order84_hd_prod) := by
  rcases order84_hd_action_cases φ with hφ | hφ | hφ | hφ
  · left
    exact ⟨(semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd⟩
  · right; left
    exact ⟨semidirectProductCongr_eq hφ⟩
  · right; right; left
    exact ⟨semidirectProductCongr_eq hφ⟩
  · right; right; right
    exact ⟨semidirectProductCongr_eq hφ⟩

theorem order84_hd_action_semidirect_cases_three (φ : order84_HD →* MulAut order84_C7) :
    Nonempty (SemidirectProduct order84_C7 order84_HD φ ≃* order84_hd_trivial) ∨
      Nonempty (SemidirectProduct order84_C7 order84_HD φ ≃* order84_hd_fst_two) ∨
      Nonempty (SemidirectProduct order84_C7 order84_HD φ ≃* order84_hd_ref) := by
  rcases order84_hd_action_semidirect_cases φ with hφ | hφ | hφ | hφ
  · left
    exact hφ
  · right; left
    exact hφ
  · right; right
    exact hφ
  · right; left
    obtain ⟨e⟩ := hφ
    exact ⟨e.trans order84_hd_prod_equiv_fst_two⟩

/-! ### Cyclic `C₃` actions -/

noncomputable abbrev order84_chiC3_three : CyclicRep 3 →* (ZMod 7)ˣ :=
  powHom (p := 7) (q := 3) (order84_u6 ^ 2) (by decide)

noncomputable abbrev order84_chiC3_three_inv : CyclicRep 3 →* (ZMod 7)ˣ :=
  powHom (p := 7) (q := 3) (order84_u6 ^ 4) (by decide)

@[simp]
theorem order84_powHom_zmod3_gen (c : (ZMod 7)ˣ) (hc : c ^ 3 = 1) :
    powHom (p := 7) (q := 3) c hc (Multiplicative.ofAdd (1 : ZMod 3)) = c := by
  change c ^ (1 : ZMod 3).val = c
  haveI : Fact (1 < 3) := ⟨by norm_num⟩
  rw [ZMod.val_one]
  simp

theorem order84_c3_action_hom_ext {φ ψ : CyclicRep 3 →* MulAut order84_C7}
    (hgen : φ (Multiplicative.ofAdd (1 : ZMod 3)) =
      ψ (Multiplicative.ofAdd (1 : ZMod 3))) :
    φ = ψ := by
  apply MonoidHom.ext
  intro x
  let n : ZMod 3 := Multiplicative.toAdd x
  have hx : x = (Multiplicative.ofAdd (1 : ZMod 3)) ^ n.val := by
    rw [show x = Multiplicative.ofAdd n from (ofAdd_toAdd _).symm]
    calc
      Multiplicative.ofAdd n = Multiplicative.ofAdd ((n.val : ZMod 3)) := by
        rw [ZMod.natCast_zmod_val]
      _ = Multiplicative.ofAdd (n.val • (1 : ZMod 3)) := by simp
      _ = (Multiplicative.ofAdd (1 : ZMod 3)) ^ n.val := by rw [ofAdd_nsmul]
  rw [hx, map_pow, map_pow, hgen]

theorem order84_c3_action_cases (φ : CyclicRep 3 →* MulAut order84_C7) :
    φ = 1 ∨ φ = order84_action order84_chiC3_three ∨
      φ = order84_action order84_chiC3_three_inv := by
  let g : CyclicRep 3 := Multiplicative.ofAdd (1 : ZMod 3)
  have hg3 : g ^ 3 = 1 := by decide
  have hφg3 : (φ g) ^ 3 = 1 := by
    rw [← map_pow, hg3, map_one]
  rcases order84_mulAut_cube_eq_one_cases (φ g) hφg3 with h | h | h
  · left
    apply order84_c3_action_hom_ext
    rw [h]
    simp
  · right; left
    apply order84_c3_action_hom_ext
    rw [h]
    simp [order84_chiC3_three]
  · right; right
    apply order84_c3_action_hom_ext
    rw [h]
    simp [order84_chiC3_three_inv]

theorem order84_chiC3_three_inv_apply (x : CyclicRep 3) :
    order84_chiC3_three x⁻¹ = order84_chiC3_three_inv x := by
  obtain ⟨n, rfl⟩ := Multiplicative.ofAdd.surjective x
  fin_cases n <;> decide

/-! ### Alternating-complement action reductions -/

local instance order84_mulAutCommGroup : CommGroup (MulAut order84_C7) :=
  { (inferInstance : Group (MulAut order84_C7)) with
    mul_comm := order84_mulAut_comm }

local instance order84_a4KleinFourNormal :
    (alternatingGroup.kleinFour (Fin 4) : Subgroup order84_HE).Normal := by
  simpa [order84_HE, fourP_A4] using
    alternatingGroup.normal_kleinFour (α := Fin 4) (by simp)

abbrev order84_A4Quot : Type :=
  order84_HE ⧸ (alternatingGroup.kleinFour (Fin 4) : Subgroup order84_HE)

theorem order84_a4Quot_card : Nat.card order84_A4Quot = 3 := by
  let K : Subgroup order84_HE := alternatingGroup.kleinFour (Fin 4)
  have hcardA : Nat.card order84_HE = 12 := by
    simpa [order84_HE] using card_fourP_A4
  have hcardK : Nat.card K = 4 := by
    simpa [K, order84_HE, fourP_A4] using
      alternatingGroup.kleinFour_card_of_card_eq_four (α := Fin 4) (by simp)
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup K
  change Nat.card order84_HE = Nat.card order84_A4Quot * Nat.card K at h
  rw [hcardA, hcardK] at h
  omega

noncomputable def order84_A4QuotEquiv : order84_A4Quot ≃* CyclicRep 3 :=
  (prime_classification (by norm_num : Nat.Prime 3) order84_a4Quot_card).some

noncomputable abbrev order84_A4QuotMk : order84_HE →* order84_A4Quot :=
  QuotientGroup.mk' (alternatingGroup.kleinFour (Fin 4) : Subgroup order84_HE)

noncomputable abbrev order84_chiA4_three : order84_HE →* (ZMod 7)ˣ :=
  order84_chiC3_three.comp (order84_A4QuotEquiv.toMonoidHom.comp order84_A4QuotMk)

noncomputable abbrev order84_chiA4_three_inv : order84_HE →* (ZMod 7)ˣ :=
  order84_chiC3_three_inv.comp (order84_A4QuotEquiv.toMonoidHom.comp order84_A4QuotMk)

noncomputable def order84_A4_conjSwap : order84_HE ≃* order84_HE where
  toFun g := by
    let τ : Equiv.Perm (Fin 4) := Equiv.swap (0 : Fin 4) 1
    refine ⟨τ * (g : Equiv.Perm (Fin 4)) * τ⁻¹, ?_⟩
    rw [Equiv.Perm.mem_alternatingGroup]
    rw [map_mul, map_mul, Equiv.Perm.sign_inv]
    have hg : Equiv.Perm.sign (g : Equiv.Perm (Fin 4)) = 1 :=
      Equiv.Perm.mem_alternatingGroup.mp g.property
    rw [hg]
    decide
  invFun g := by
    let τ : Equiv.Perm (Fin 4) := Equiv.swap (0 : Fin 4) 1
    refine ⟨τ * (g : Equiv.Perm (Fin 4)) * τ⁻¹, ?_⟩
    rw [Equiv.Perm.mem_alternatingGroup]
    rw [map_mul, map_mul, Equiv.Perm.sign_inv]
    have hg : Equiv.Perm.sign (g : Equiv.Perm (Fin 4)) = 1 :=
      Equiv.Perm.mem_alternatingGroup.mp g.property
    rw [hg]
    decide
  left_inv := by
    intro g
    apply Subtype.ext
    ext x
    decide +revert
  right_inv := by
    intro g
    apply Subtype.ext
    ext x
    decide +revert
  map_mul' := by
    intro g h
    apply Subtype.ext
    ext x
    decide +revert

theorem order84_A4QuotMk_conjSwap (g : order84_HE) :
    order84_A4QuotMk (order84_A4_conjSwap g) = (order84_A4QuotMk g)⁻¹ := by
  let K : Subgroup order84_HE := alternatingGroup.kleinFour (Fin 4)
  change (QuotientGroup.mk' K) (order84_A4_conjSwap g) = ((QuotientGroup.mk' K) g)⁻¹
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, ← QuotientGroup.mk_inv K g]
  rw [QuotientGroup.eq]
  rw [← SetLike.mem_coe, alternatingGroup.coe_kleinFour_of_card_eq_four (α := Fin 4) (by simp)]
  fin_cases g <;> decide

theorem order84_chiA4_three_comp_conjSwap :
    order84_chiA4_three.comp order84_A4_conjSwap.toMonoidHom = order84_chiA4_three_inv := by
  apply MonoidHom.ext
  intro g
  change order84_chiC3_three
      (order84_A4QuotEquiv (order84_A4QuotMk (order84_A4_conjSwap g))) =
    order84_chiC3_three_inv (order84_A4QuotEquiv (order84_A4QuotMk g))
  rw [order84_A4QuotMk_conjSwap]
  rw [map_inv]
  exact order84_chiC3_three_inv_apply _

theorem order84_a4_kleinFour_eq_commutator :
    (alternatingGroup.kleinFour (Fin 4) : Subgroup order84_HE) = commutator order84_HE := by
  simpa [order84_HE, fourP_A4] using
    alternatingGroup.kleinFour_eq_commutator (α := Fin 4) (by simp)

theorem order84_a4_kleinFour_maps_trivially
    (φ : order84_HE →* MulAut order84_C7) {g : order84_HE}
    (hg : g ∈ alternatingGroup.kleinFour (Fin 4)) : φ g = 1 := by
  have hcomm : commutator order84_HE ≤ φ.ker := Abelianization.commutator_subset_ker φ
  rw [order84_a4_kleinFour_eq_commutator] at hg
  exact MonoidHom.mem_ker.mp (hcomm hg)

theorem order84_a4_order_two_mem_kleinFour (g : order84_HE) (hg : g ^ 2 = 1) :
    g ∈ alternatingGroup.kleinFour (Fin 4) := by
  have hgperm2 : ((g : Equiv.Perm (Fin 4)) ^ 2 = 1) := by
    simpa using congrArg (fun x : order84_HE => (x : Equiv.Perm (Fin 4))) hg
  have hdiv : orderOf (g : Equiv.Perm (Fin 4)) ∣ 2 ^ 1 := by
    rw [pow_one]
    exact orderOf_dvd_of_pow_eq_one hgperm2
  have hcycle := alternatingGroup.mem_kleinFour_of_order_two_pow (α := Fin 4)
    (by simp) g.property (n := 1) hdiv
  rw [← SetLike.mem_coe, alternatingGroup.coe_kleinFour_of_card_eq_four (α := Fin 4) (by simp),
    Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
  rcases hcycle with hcycle | hcycle
  · left
    apply Subtype.ext
    exact Equiv.Perm.cycleType_eq_zero.mp hcycle
  · right
    exact hcycle

theorem order84_a4_action_cube_eq_one (φ : order84_HE →* MulAut order84_C7)
    (g : order84_HE) : (φ g) ^ 3 = 1 := by
  rcases fourP_A4_pow g with hg2 | hg3
  · have hgK : g ∈ alternatingGroup.kleinFour (Fin 4) := by
      exact order84_a4_order_two_mem_kleinFour g hg2
    rw [order84_a4_kleinFour_maps_trivially φ hgK, one_pow]
  · rw [← map_pow, hg3, map_one]

theorem order84_a4_action_value_cases (φ : order84_HE →* MulAut order84_C7)
    (g : order84_HE) :
    φ g = 1 ∨ φ g = unitAutHom (order84_u6 ^ 2) ∨
      φ g = unitAutHom (order84_u6 ^ 4) :=
  order84_mulAut_cube_eq_one_cases (φ g) (order84_a4_action_cube_eq_one φ g)

theorem order84_a4_action_cases (φ : order84_HE →* MulAut order84_C7) :
    φ = 1 ∨ φ = order84_action order84_chiA4_three ∨
      φ = order84_action order84_chiA4_three_inv := by
  let K : Subgroup order84_HE := alternatingGroup.kleinFour (Fin 4)
  have hKker : K ≤ φ.ker := by
    intro g hg
    exact MonoidHom.mem_ker.mpr (order84_a4_kleinFour_maps_trivially φ hg)
  let φQ : order84_A4Quot →* MulAut order84_C7 := QuotientGroup.lift K φ hKker
  let φC3 : CyclicRep 3 →* MulAut order84_C7 :=
    φQ.comp order84_A4QuotEquiv.symm.toMonoidHom
  rcases order84_c3_action_cases φC3 with h | h | h
  · left
    apply MonoidHom.ext
    intro g
    have hcomp : φQ.comp order84_A4QuotEquiv.symm.toMonoidHom = 1 := h
    have hq : φQ (order84_A4QuotMk g) = 1 := by
      calc
        φQ (order84_A4QuotMk g) =
            φQ (order84_A4QuotEquiv.symm (order84_A4QuotEquiv (order84_A4QuotMk g))) := by
              simp
        _ = (φQ.comp order84_A4QuotEquiv.symm.toMonoidHom)
            (order84_A4QuotEquiv (order84_A4QuotMk g)) := rfl
        _ = 1 := by rw [hcomp]; simp
    simpa [φQ, order84_A4QuotMk] using hq
  · right; left
    apply MonoidHom.ext
    intro g
    have hcomp :
        φQ.comp order84_A4QuotEquiv.symm.toMonoidHom =
          order84_action order84_chiC3_three := h
    have hq :
        φQ (order84_A4QuotMk g) =
          order84_action order84_chiC3_three (order84_A4QuotEquiv (order84_A4QuotMk g)) := by
      calc
        φQ (order84_A4QuotMk g) =
            φQ (order84_A4QuotEquiv.symm (order84_A4QuotEquiv (order84_A4QuotMk g))) := by
              simp
        _ = (φQ.comp order84_A4QuotEquiv.symm.toMonoidHom)
            (order84_A4QuotEquiv (order84_A4QuotMk g)) := rfl
        _ = order84_action order84_chiC3_three
            (order84_A4QuotEquiv (order84_A4QuotMk g)) := by rw [hcomp]
    simpa [φQ, order84_A4QuotMk, order84_chiA4_three, order84_action] using hq
  · right; right
    apply MonoidHom.ext
    intro g
    have hcomp :
        φQ.comp order84_A4QuotEquiv.symm.toMonoidHom =
          order84_action order84_chiC3_three_inv := h
    have hq :
        φQ (order84_A4QuotMk g) =
          order84_action order84_chiC3_three_inv
            (order84_A4QuotEquiv (order84_A4QuotMk g)) := by
      calc
        φQ (order84_A4QuotMk g) =
            φQ (order84_A4QuotEquiv.symm (order84_A4QuotEquiv (order84_A4QuotMk g))) := by
              simp
        _ = (φQ.comp order84_A4QuotEquiv.symm.toMonoidHom)
            (order84_A4QuotEquiv (order84_A4QuotMk g)) := rfl
        _ = order84_action order84_chiC3_three_inv
            (order84_A4QuotEquiv (order84_A4QuotMk g)) := by rw [hcomp]
    simpa [φQ, order84_A4QuotMk, order84_chiA4_three_inv, order84_action] using hq

noncomputable abbrev order84_a4_trivial : Type :=
  order84_C7 × order84_HE

noncomputable abbrev order84_a4_three : Type :=
  SemidirectProduct order84_C7 order84_HE (order84_action order84_chiA4_three)

noncomputable abbrev order84_a4_three_inv : Type :=
  SemidirectProduct order84_C7 order84_HE (order84_action order84_chiA4_three_inv)

noncomputable def order84_a4_three_inv_equiv_three : order84_a4_three_inv ≃* order84_a4_three :=
  order84_action_precomp_eq_mulEquiv order84_chiA4_three order84_chiA4_three_inv
    order84_A4_conjSwap order84_chiA4_three_comp_conjSwap

theorem order84_a4_action_semidirect_cases (φ : order84_HE →* MulAut order84_C7) :
    Nonempty (SemidirectProduct order84_C7 order84_HE φ ≃* order84_a4_trivial) ∨
      Nonempty (SemidirectProduct order84_C7 order84_HE φ ≃* order84_a4_three) ∨
      Nonempty (SemidirectProduct order84_C7 order84_HE φ ≃* order84_a4_three_inv) := by
  rcases order84_a4_action_cases φ with hφ | hφ | hφ
  · left
    exact ⟨(semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd⟩
  · right; left
    exact ⟨semidirectProductCongr_eq hφ⟩
  · right; right
    exact ⟨semidirectProductCongr_eq hφ⟩

theorem order84_a4_action_semidirect_cases_two (φ : order84_HE →* MulAut order84_C7) :
    Nonempty (SemidirectProduct order84_C7 order84_HE φ ≃* order84_a4_trivial) ∨
      Nonempty (SemidirectProduct order84_C7 order84_HE φ ≃* order84_a4_three) := by
  rcases order84_a4_action_semidirect_cases φ with hφ | hφ | hφ
  · left
    exact hφ
  · right
    exact hφ
  · right
    obtain ⟨e⟩ := hφ
    exact ⟨e.trans order84_a4_three_inv_equiv_three⟩

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

/-! ### Indexed representatives and exhaustiveness -/

/-- The fifteen displayed representatives for groups of order `84`. -/
noncomputable abbrev order84_reps : Fin 15 → Type
  | 0 => order84_c12_trivial
  | 1 => order84_c12_six
  | 2 => order84_c12_three
  | 3 => order84_c12_two
  | 4 => order84_c2c6_trivial
  | 5 => order84_c2c6_fst_two
  | 6 => order84_c2c6_snd_three
  | 7 => order84_c2c6_fst_two_snd_six
  | 8 => order84_hc_trivial
  | 9 => order84_hc_two
  | 10 => order84_hd_trivial
  | 11 => order84_hd_fst_two
  | 12 => order84_hd_ref
  | 13 => order84_a4_trivial
  | 14 => order84_a4_three

noncomputable instance instGroupOrder84Reps : (i : Fin 15) → Group (order84_reps i)
  | 0 => inferInstanceAs (Group order84_c12_trivial)
  | 1 => inferInstanceAs (Group order84_c12_six)
  | 2 => inferInstanceAs (Group order84_c12_three)
  | 3 => inferInstanceAs (Group order84_c12_two)
  | 4 => inferInstanceAs (Group order84_c2c6_trivial)
  | 5 => inferInstanceAs (Group order84_c2c6_fst_two)
  | 6 => inferInstanceAs (Group order84_c2c6_snd_three)
  | 7 => inferInstanceAs (Group order84_c2c6_fst_two_snd_six)
  | 8 => inferInstanceAs (Group order84_hc_trivial)
  | 9 => inferInstanceAs (Group order84_hc_two)
  | 10 => inferInstanceAs (Group order84_hd_trivial)
  | 11 => inferInstanceAs (Group order84_hd_fst_two)
  | 12 => inferInstanceAs (Group order84_hd_ref)
  | 13 => inferInstanceAs (Group order84_a4_trivial)
  | 14 => inferInstanceAs (Group order84_a4_three)

/-- Every group of order `84` is isomorphic to one of the fifteen displayed representatives. -/
theorem order84_complete (G : Type) [Group G] [Finite G] (hG : Nat.card G = 84) :
    ∃ i : Fin 15, Nonempty (G ≃* order84_reps i) := by
  rcases order84_semidirectProduct_standard_cases (G := G) hG with h | h | h | h | h
  · obtain ⟨φ, ⟨e⟩⟩ := h
    rcases order84_c12_action_semidirect_cases φ with hφ | hφ | hφ | hφ
    · obtain ⟨eh⟩ := hφ
      exact ⟨0, by
        simpa [order84_reps] using (⟨e.trans eh⟩ : Nonempty (G ≃* order84_c12_trivial))⟩
    · obtain ⟨eh⟩ := hφ
      exact ⟨1, by
        simpa [order84_reps] using (⟨e.trans eh⟩ : Nonempty (G ≃* order84_c12_six))⟩
    · obtain ⟨eh⟩ := hφ
      exact ⟨2, by
        simpa [order84_reps] using (⟨e.trans eh⟩ : Nonempty (G ≃* order84_c12_three))⟩
    · obtain ⟨eh⟩ := hφ
      exact ⟨3, by
        simpa [order84_reps] using (⟨e.trans eh⟩ : Nonempty (G ≃* order84_c12_two))⟩
  · obtain ⟨φ, ⟨e⟩⟩ := h
    rcases order84_c2c6_action_semidirect_cases_four φ with hφ | hφ | hφ | hφ
    · obtain ⟨eh⟩ := hφ
      exact ⟨4, by
        simpa [order84_reps] using (⟨e.trans eh⟩ : Nonempty (G ≃* order84_c2c6_trivial))⟩
    · obtain ⟨eh⟩ := hφ
      exact ⟨5, by
        simpa [order84_reps] using (⟨e.trans eh⟩ : Nonempty (G ≃* order84_c2c6_fst_two))⟩
    · obtain ⟨eh⟩ := hφ
      exact ⟨6, by
        simpa [order84_reps] using (⟨e.trans eh⟩ : Nonempty (G ≃* order84_c2c6_snd_three))⟩
    · obtain ⟨eh⟩ := hφ
      exact ⟨7, by
        simpa [order84_reps] using
          (⟨e.trans eh⟩ : Nonempty (G ≃* order84_c2c6_fst_two_snd_six))⟩
  · obtain ⟨φ, ⟨e⟩⟩ := h
    rcases order84_hc_action_semidirect_cases φ with hφ | hφ
    · obtain ⟨eh⟩ := hφ
      exact ⟨8, by
        simpa [order84_reps] using (⟨e.trans eh⟩ : Nonempty (G ≃* order84_hc_trivial))⟩
    · obtain ⟨eh⟩ := hφ
      exact ⟨9, by
        simpa [order84_reps] using (⟨e.trans eh⟩ : Nonempty (G ≃* order84_hc_two))⟩
  · obtain ⟨φ, ⟨e⟩⟩ := h
    rcases order84_hd_action_semidirect_cases_three φ with hφ | hφ | hφ
    · obtain ⟨eh⟩ := hφ
      exact ⟨10, by
        simpa [order84_reps] using (⟨e.trans eh⟩ : Nonempty (G ≃* order84_hd_trivial))⟩
    · obtain ⟨eh⟩ := hφ
      exact ⟨11, by
        simpa [order84_reps] using (⟨e.trans eh⟩ : Nonempty (G ≃* order84_hd_fst_two))⟩
    · obtain ⟨eh⟩ := hφ
      exact ⟨12, by
        simpa [order84_reps] using (⟨e.trans eh⟩ : Nonempty (G ≃* order84_hd_ref))⟩
  · obtain ⟨φ, ⟨e⟩⟩ := h
    rcases order84_a4_action_semidirect_cases_two φ with hφ | hφ
    · obtain ⟨eh⟩ := hφ
      exact ⟨13, by
        simpa [order84_reps] using (⟨e.trans eh⟩ : Nonempty (G ≃* order84_a4_trivial))⟩
    · obtain ⟨eh⟩ := hφ
      exact ⟨14, by
        simpa [order84_reps] using (⟨e.trans eh⟩ : Nonempty (G ≃* order84_a4_three))⟩

end Smallgroups.UsefulTheorems
