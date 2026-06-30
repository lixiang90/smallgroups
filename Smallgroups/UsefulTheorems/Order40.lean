/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order88

/-!
# First reductions for groups of order 40

Since `40 = 8 * 5`, the Sylow `5`-subgroup is normal.  Thus every group of
order `40` splits as `C₅ ⋊ H`, where `H` is a group of order `8`.

This file records that reduction and the fourteen expected semidirect-product
representatives.  The remaining classification work is the orbit calculation
for homomorphisms `H → Aut(C₅)`.
-/

namespace Smallgroups.UsefulTheorems

open Sylow

variable {G : Type*} [Group G]

/-! ### Sylow-5 normality and semidirect-product reduction -/

/-- The Sylow `5`-subgroup is unique in a group of order `40`. -/
theorem card_sylow_5_eq_one_of_card_40 [Finite G] (hG : Nat.card G = 40) :
    Nat.card (Sylow 5 G) = 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 5 G))
  have hndvd_5 : ¬ 5 ∣ Nat.card (Sylow 5 G) := not_dvd_card_sylow 5 G
  have hdvd40 : Nat.card (Sylow 5 G) ∣ 40 := by
    rw [← hG]
    exact P0.card_dvd_index.trans (Subgroup.index_dvd_card _)
  have h40 : 40 = 8 * 5 := by norm_num
  have hdvd8_mul : Nat.card (Sylow 5 G) ∣ 8 * 5 := by
    simpa [h40] using hdvd40
  have hp5 : Nat.Prime 5 := by norm_num
  have hcop : Nat.Coprime (Nat.card (Sylow 5 G)) 5 :=
    (hp5.coprime_iff_not_dvd.mpr hndvd_5).symm
  have hdvd8 : Nat.card (Sylow 5 G) ∣ 8 := hcop.dvd_of_dvd_mul_right hdvd8_mul
  have hmod := card_sylow_modEq_one 5 G
  have hle : Nat.card (Sylow 5 G) ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd8
  have hpos : 0 < Nat.card (Sylow 5 G) := Nat.card_pos
  interval_cases h : Nat.card (Sylow 5 G)
  · rfl
  · unfold Nat.ModEq at hmod; norm_num at hmod
  · norm_num at hdvd8
  · unfold Nat.ModEq at hmod; norm_num at hmod
  · norm_num at hdvd8
  · norm_num at hdvd8
  · norm_num at hdvd8
  · unfold Nat.ModEq at hmod; norm_num at hmod

/-- The Sylow `5`-subgroup of a group of order `40` is normal. -/
theorem sylow_5_normal_of_card_40 [Finite G] (hG : Nat.card G = 40) (P : Sylow 5 G) :
    (↑P : Subgroup G).Normal := by
  haveI : Subsingleton (Sylow 5 G) :=
    (Nat.card_eq_one_iff_unique.mp (card_sylow_5_eq_one_of_card_40 hG)).1
  exact Sylow.normal_of_subsingleton P

/-- The Sylow `5`-subgroup of a group of order `40` has order `5`. -/
theorem card_sylow_5_subgroup_of_card_40 [Finite G] (hG : Nat.card G = 40)
    (P : Sylow 5 G) : Nat.card (↑P : Subgroup G) = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hndvd : ¬ 5 ∣ 8 := by norm_num
  have hfact : (40 : ℕ).factorization 5 = 1 := by
    rw [show 40 = 8 * 5 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hndvd,
      Nat.Prime.factorization_self (by norm_num : Nat.Prime 5), zero_add]
  rw [Sylow.card_eq_multiplicity, hG, hfact, pow_one]

/-- **Schur-Zassenhaus reduction for order `40`.**
Every group of order `40` is a semidirect product `N ⋊[φ] H`, where
`N` has order `5` and `H` has order `8`. -/
theorem order40_semidirectProduct [Finite G] (hG : Nat.card G = 40) :
    ∃ (N H : Subgroup G) (φ : H →* MulAut N),
      N.Normal ∧ Nat.card N = 5 ∧ Nat.card H = 8 ∧
        Nonempty (G ≃* SemidirectProduct N H φ) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 5 G))
  haveI hnorm : (↑P0 : Subgroup G).Normal := sylow_5_normal_of_card_40 hG P0
  have hcardN : Nat.card (↑P0 : Subgroup G) = 5 :=
    card_sylow_5_subgroup_of_card_40 hG P0
  haveI : (↑P0 : Subgroup G).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
  have hcop : Nat.Coprime (Nat.card (↑P0 : Subgroup G)) (↑P0 : Subgroup G).index := by
    rw [hcardN]
    have := P0.not_dvd_index
    exact (show Nat.Prime 5 by norm_num).coprime_iff_not_dvd.mpr this
  obtain ⟨H, φ, ⟨e⟩⟩ := schurZassenhaus_semidirectProduct (↑P0 : Subgroup G) hcop
  have hcardH : Nat.card H = 8 := by
    have h1 : Nat.card G = Nat.card (↑P0 : Subgroup G) * Nat.card H := by
      rw [Nat.card_congr e.toEquiv, Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
    rw [hG, hcardN] at h1
    have h1' : 5 * Nat.card H = 5 * 8 := by omega
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 5) h1'
  exact ⟨↑P0, H, φ, hnorm, hcardN, hcardH, ⟨e⟩⟩

/-! ### Candidate representatives -/

/-- The normal subgroup in the order-`40` representatives. -/
abbrev order40_C5 : Type := CyclicRep 5

abbrev order40_C8 : Type := Multiplicative (ZMod 8)
abbrev order40_C4C2 : Type := Multiplicative (ZMod 4) × Multiplicative (ZMod 2)
abbrev order40_C2C2C2 : Type :=
  Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)
abbrev order40_D8 : Type := DihedralGroup 4
abbrev order40_Q8 : Type := QuaternionGroup 2

/-- A chosen element of order `4` in `Aut(C₅) ≃ (ZMod 5)ˣ`. -/
noncomputable abbrev order40_u4 : (ZMod 5)ˣ :=
  ZMod.unitOfCoprime 2 (by norm_num : Nat.Coprime 2 5)

theorem order40_u4_pow_four : order40_u4 ^ 4 = 1 := by
  decide

theorem order40_unit_cases (u : (ZMod 5)ˣ) :
    u = 1 ∨ u = order40_u4 ∨ u = order40_u4 ^ 2 ∨ u = order40_u4 ^ 3 := by
  decide +revert

/-- The quotient map `C₂ → (ZMod 5)ˣ` sending the generator to `order40_u4 ^ 2`. -/
noncomputable abbrev order40_c2UnitHom : Multiplicative (ZMod 2) →* (ZMod 5)ˣ :=
  powHom (p := 5) (q := 2) (order40_u4 ^ 2) (by decide)

@[simp]
theorem order40_c2UnitHom_gen :
    order40_c2UnitHom (Multiplicative.ofAdd (1 : ZMod 2)) = order40_u4 ^ 2 := by
  decide

/-- Turn a unit-valued character into the corresponding action on `C₅`. -/
noncomputable abbrev order40_action {H : Type} [Group H] (χ : H →* (ZMod 5)ˣ) :
    H →* MulAut order40_C5 :=
  unitAutHom.comp χ

noncomputable abbrev order40_chiC8_two : order40_C8 →* (ZMod 5)ˣ :=
  order40_c2UnitHom.comp order88_chiC8

noncomputable abbrev order40_chiC8_four : order40_C8 →* (ZMod 5)ˣ :=
  powHom (p := 5) (q := 8) order40_u4 (by decide)

/-- The second order-`4` character on `C₈`, later identified with `order40_chiC8_four`
up to an automorphism of `C₈`. -/
noncomputable abbrev order40_chiC8_four_inv : order40_C8 →* (ZMod 5)ˣ :=
  powHom (p := 5) (q := 8) (order40_u4 ^ 3) (by decide)

/-- Homomorphisms out of `C₈` are determined by the additive generator `1`. -/
theorem order40_c8_unit_hom_ext {χ ψ : order40_C8 →* (ZMod 5)ˣ}
    (hgen : χ (Multiplicative.ofAdd (1 : ZMod 8)) =
      ψ (Multiplicative.ofAdd (1 : ZMod 8))) :
    χ = ψ := by
  apply MonoidHom.ext
  intro x
  let n : ZMod 8 := Multiplicative.toAdd x
  have hx : x = (Multiplicative.ofAdd (1 : ZMod 8)) ^ n.val := by
    rw [show x = Multiplicative.ofAdd n from (ofAdd_toAdd _).symm]
    calc
      Multiplicative.ofAdd n = Multiplicative.ofAdd ((n.val : ZMod 8)) := by
        rw [ZMod.natCast_zmod_val]
      _ = Multiplicative.ofAdd (n.val • (1 : ZMod 8)) := by simp
      _ = (Multiplicative.ofAdd (1 : ZMod 8)) ^ n.val := by rw [ofAdd_nsmul]
  rw [hx, map_pow, map_pow, hgen]

/-- Actions out of `C₈` are determined by the additive generator `1`. -/
theorem order40_c8_action_hom_ext {φ ψ : order40_C8 →* MulAut order40_C5}
    (hgen : φ (Multiplicative.ofAdd (1 : ZMod 8)) =
      ψ (Multiplicative.ofAdd (1 : ZMod 8))) :
    φ = ψ := by
  apply MonoidHom.ext
  intro x
  let n : ZMod 8 := Multiplicative.toAdd x
  have hx : x = (Multiplicative.ofAdd (1 : ZMod 8)) ^ n.val := by
    rw [show x = Multiplicative.ofAdd n from (ofAdd_toAdd _).symm]
    calc
      Multiplicative.ofAdd n = Multiplicative.ofAdd ((n.val : ZMod 8)) := by
        rw [ZMod.natCast_zmod_val]
      _ = Multiplicative.ofAdd (n.val • (1 : ZMod 8)) := by simp
      _ = (Multiplicative.ofAdd (1 : ZMod 8)) ^ n.val := by rw [ofAdd_nsmul]
  rw [hx, map_pow, map_pow, hgen]

theorem order40_chiC8_four_gen :
    order40_chiC8_four (Multiplicative.ofAdd (1 : ZMod 8)) = order40_u4 := by
  decide

theorem order40_chiC8_two_gen :
    order40_chiC8_two (Multiplicative.ofAdd (1 : ZMod 8)) = order40_u4 ^ 2 := by
  decide

theorem order40_chiC8_four_inv_gen :
    order40_chiC8_four_inv (Multiplicative.ofAdd (1 : ZMod 8)) = order40_u4 ^ 3 := by
  decide

/-- Characters `C₈ → (ZMod 5)ˣ` are one of the four displayed characters. -/
theorem order40_c8_unit_character_cases (χ : order40_C8 →* (ZMod 5)ˣ) :
    χ = 1 ∨ χ = order40_chiC8_four ∨ χ = order40_chiC8_two ∨
      χ = order40_chiC8_four_inv := by
  let g : order40_C8 := Multiplicative.ofAdd (1 : ZMod 8)
  rcases order40_unit_cases (χ g) with h | h | h | h
  · left
    apply order40_c8_unit_hom_ext
    simp [g, h]
  · right
    left
    apply order40_c8_unit_hom_ext
    rw [h, order40_chiC8_four_gen]
  · right
    right
    left
    apply order40_c8_unit_hom_ext
    rw [h, order40_chiC8_two_gen]
  · right
    right
    right
    apply order40_c8_unit_hom_ext
    rw [h, order40_chiC8_four_inv_gen]

/-- The automorphism of `C₈` sending the additive generator to three times itself. -/
noncomputable def order40_C8_mulThree : order40_C8 ≃* order40_C8 :=
  unitAutHom (p := 8) (ZMod.unitOfCoprime 3 (by norm_num : Nat.Coprime 3 8))

/-- The two order-`4` characters of `C₈` lie in the same automorphism orbit. -/
theorem order40_chiC8_four_comp_mulThree :
    order40_chiC8_four.comp order40_C8_mulThree.toMonoidHom =
      order40_chiC8_four_inv := by
  apply order40_c8_unit_hom_ext
  decide

noncomputable abbrev order40_chiC4C2_fst_two : order40_C4C2 →* (ZMod 5)ˣ :=
  order40_c2UnitHom.comp order88_chiC4C2_fst

noncomputable abbrev order40_chiC4C2_snd_two : order40_C4C2 →* (ZMod 5)ˣ :=
  order40_c2UnitHom.comp order88_chiC4C2_snd

noncomputable abbrev order40_chiC4C2_fst_four : order40_C4C2 →* (ZMod 5)ˣ :=
  (powHom (p := 5) (q := 4) order40_u4 (by decide)).comp
    (MonoidHom.fst (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2)))

noncomputable abbrev order40_chiC4C2_prod_two : order40_C4C2 →* (ZMod 5)ˣ :=
  order40_c2UnitHom.comp order88_chiC4C2_prod

noncomputable abbrev order40_chiC4C2_fst_four_snd : order40_C4C2 →* (ZMod 5)ˣ :=
  order40_chiC4C2_fst_four * order40_chiC4C2_snd_two

noncomputable abbrev order40_chiC4C2_fst_four_inv : order40_C4C2 →* (ZMod 5)ˣ :=
  (powHom (p := 5) (q := 4) (order40_u4 ^ 3) (by decide)).comp
    (MonoidHom.fst (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2)))

noncomputable abbrev order40_chiC4C2_fst_four_inv_snd :
    order40_C4C2 →* (ZMod 5)ˣ :=
  order40_chiC4C2_fst_four_inv * order40_chiC4C2_snd_two

@[simp]
theorem order40_chiC4C2_fst_two_g4 :
    order40_chiC4C2_fst_two (Multiplicative.ofAdd (1 : ZMod 4), 1) =
      order40_u4 ^ 2 := by
  decide

@[simp]
theorem order40_chiC4C2_fst_two_g2 :
    order40_chiC4C2_fst_two (1, Multiplicative.ofAdd (1 : ZMod 2)) = 1 := by
  decide

@[simp]
theorem order40_chiC4C2_snd_two_g4 :
    order40_chiC4C2_snd_two (Multiplicative.ofAdd (1 : ZMod 4), 1) = 1 := by
  decide

@[simp]
theorem order40_chiC4C2_snd_two_g2 :
    order40_chiC4C2_snd_two (1, Multiplicative.ofAdd (1 : ZMod 2)) =
      order40_u4 ^ 2 := by
  decide

@[simp]
theorem order40_chiC4C2_prod_two_g4 :
    order40_chiC4C2_prod_two (Multiplicative.ofAdd (1 : ZMod 4), 1) =
      order40_u4 ^ 2 := by
  decide

@[simp]
theorem order40_chiC4C2_prod_two_g2 :
    order40_chiC4C2_prod_two (1, Multiplicative.ofAdd (1 : ZMod 2)) =
      order40_u4 ^ 2 := by
  decide

@[simp]
theorem order40_chiC4C2_fst_four_g4 :
    order40_chiC4C2_fst_four (Multiplicative.ofAdd (1 : ZMod 4), 1) =
      order40_u4 := by
  decide

@[simp]
theorem order40_chiC4C2_fst_four_g2 :
    order40_chiC4C2_fst_four (1, Multiplicative.ofAdd (1 : ZMod 2)) = 1 := by
  decide

@[simp]
theorem order40_chiC4C2_fst_four_snd_g4 :
    order40_chiC4C2_fst_four_snd (Multiplicative.ofAdd (1 : ZMod 4), 1) =
      order40_u4 := by
  decide

@[simp]
theorem order40_chiC4C2_fst_four_snd_g2 :
    order40_chiC4C2_fst_four_snd (1, Multiplicative.ofAdd (1 : ZMod 2)) =
      order40_u4 ^ 2 := by
  decide

@[simp]
theorem order40_chiC4C2_fst_four_inv_g4 :
    order40_chiC4C2_fst_four_inv (Multiplicative.ofAdd (1 : ZMod 4), 1) =
      order40_u4 ^ 3 := by
  decide

@[simp]
theorem order40_chiC4C2_fst_four_inv_g2 :
    order40_chiC4C2_fst_four_inv (1, Multiplicative.ofAdd (1 : ZMod 2)) = 1 := by
  decide

@[simp]
theorem order40_chiC4C2_fst_four_inv_snd_g4 :
    order40_chiC4C2_fst_four_inv_snd (Multiplicative.ofAdd (1 : ZMod 4), 1) =
      order40_u4 ^ 3 := by
  decide

@[simp]
theorem order40_chiC4C2_fst_four_inv_snd_g2 :
    order40_chiC4C2_fst_four_inv_snd (1, Multiplicative.ofAdd (1 : ZMod 2)) =
      order40_u4 ^ 2 := by
  decide

@[simp]
theorem order40_action_chiC4C2_fst_two_g4 :
    (order40_action order40_chiC4C2_fst_two)
      (Multiplicative.ofAdd (1 : ZMod 4), 1) = unitAutHom (order40_u4 ^ 2) := by
  change unitAutHom (order40_chiC4C2_fst_two
    (Multiplicative.ofAdd (1 : ZMod 4), 1)) = unitAutHom (order40_u4 ^ 2)
  rw [order40_chiC4C2_fst_two_g4]

@[simp]
theorem order40_action_chiC4C2_fst_two_g2 :
    (order40_action order40_chiC4C2_fst_two)
      (1, Multiplicative.ofAdd (1 : ZMod 2)) = 1 := by
  change unitAutHom (order40_chiC4C2_fst_two
    (1, Multiplicative.ofAdd (1 : ZMod 2))) = 1
  rw [order40_chiC4C2_fst_two_g2, map_one]

@[simp]
theorem order40_action_chiC4C2_snd_two_g4 :
    (order40_action order40_chiC4C2_snd_two)
      (Multiplicative.ofAdd (1 : ZMod 4), 1) = 1 := by
  change unitAutHom (order40_chiC4C2_snd_two
    (Multiplicative.ofAdd (1 : ZMod 4), 1)) = 1
  rw [order40_chiC4C2_snd_two_g4, map_one]

@[simp]
theorem order40_action_chiC4C2_snd_two_g2 :
    (order40_action order40_chiC4C2_snd_two)
      (1, Multiplicative.ofAdd (1 : ZMod 2)) = unitAutHom (order40_u4 ^ 2) := by
  change unitAutHom (order40_chiC4C2_snd_two
    (1, Multiplicative.ofAdd (1 : ZMod 2))) = unitAutHom (order40_u4 ^ 2)
  rw [order40_chiC4C2_snd_two_g2]

@[simp]
theorem order40_action_chiC4C2_prod_two_g4 :
    (order40_action order40_chiC4C2_prod_two)
      (Multiplicative.ofAdd (1 : ZMod 4), 1) = unitAutHom (order40_u4 ^ 2) := by
  change unitAutHom (order40_chiC4C2_prod_two
    (Multiplicative.ofAdd (1 : ZMod 4), 1)) = unitAutHom (order40_u4 ^ 2)
  rw [order40_chiC4C2_prod_two_g4]

@[simp]
theorem order40_action_chiC4C2_prod_two_g2 :
    (order40_action order40_chiC4C2_prod_two)
      (1, Multiplicative.ofAdd (1 : ZMod 2)) = unitAutHom (order40_u4 ^ 2) := by
  change unitAutHom (order40_chiC4C2_prod_two
    (1, Multiplicative.ofAdd (1 : ZMod 2))) = unitAutHom (order40_u4 ^ 2)
  rw [order40_chiC4C2_prod_two_g2]

@[simp]
theorem order40_action_chiC4C2_fst_four_g4 :
    (order40_action order40_chiC4C2_fst_four)
      (Multiplicative.ofAdd (1 : ZMod 4), 1) = unitAutHom order40_u4 := by
  change unitAutHom (order40_chiC4C2_fst_four
    (Multiplicative.ofAdd (1 : ZMod 4), 1)) = unitAutHom order40_u4
  rw [order40_chiC4C2_fst_four_g4]

@[simp]
theorem order40_action_chiC4C2_fst_four_g2 :
    (order40_action order40_chiC4C2_fst_four)
      (1, Multiplicative.ofAdd (1 : ZMod 2)) = 1 := by
  change unitAutHom (order40_chiC4C2_fst_four
    (1, Multiplicative.ofAdd (1 : ZMod 2))) = 1
  rw [order40_chiC4C2_fst_four_g2, map_one]

@[simp]
theorem order40_action_chiC4C2_fst_four_snd_g4 :
    (order40_action order40_chiC4C2_fst_four_snd)
      (Multiplicative.ofAdd (1 : ZMod 4), 1) = unitAutHom order40_u4 := by
  change unitAutHom (order40_chiC4C2_fst_four_snd
    (Multiplicative.ofAdd (1 : ZMod 4), 1)) = unitAutHom order40_u4
  rw [order40_chiC4C2_fst_four_snd_g4]

@[simp]
theorem order40_action_chiC4C2_fst_four_snd_g2 :
    (order40_action order40_chiC4C2_fst_four_snd)
      (1, Multiplicative.ofAdd (1 : ZMod 2)) = unitAutHom (order40_u4 ^ 2) := by
  change unitAutHom (order40_chiC4C2_fst_four_snd
    (1, Multiplicative.ofAdd (1 : ZMod 2))) = unitAutHom (order40_u4 ^ 2)
  rw [order40_chiC4C2_fst_four_snd_g2]

@[simp]
theorem order40_action_chiC4C2_fst_four_inv_g4 :
    (order40_action order40_chiC4C2_fst_four_inv)
      (Multiplicative.ofAdd (1 : ZMod 4), 1) = unitAutHom (order40_u4 ^ 3) := by
  change unitAutHom (order40_chiC4C2_fst_four_inv
    (Multiplicative.ofAdd (1 : ZMod 4), 1)) = unitAutHom (order40_u4 ^ 3)
  rw [order40_chiC4C2_fst_four_inv_g4]

@[simp]
theorem order40_action_chiC4C2_fst_four_inv_g2 :
    (order40_action order40_chiC4C2_fst_four_inv)
      (1, Multiplicative.ofAdd (1 : ZMod 2)) = 1 := by
  change unitAutHom (order40_chiC4C2_fst_four_inv
    (1, Multiplicative.ofAdd (1 : ZMod 2))) = 1
  rw [order40_chiC4C2_fst_four_inv_g2, map_one]

@[simp]
theorem order40_action_chiC4C2_fst_four_inv_snd_g4 :
    (order40_action order40_chiC4C2_fst_four_inv_snd)
      (Multiplicative.ofAdd (1 : ZMod 4), 1) = unitAutHom (order40_u4 ^ 3) := by
  change unitAutHom (order40_chiC4C2_fst_four_inv_snd
    (Multiplicative.ofAdd (1 : ZMod 4), 1)) = unitAutHom (order40_u4 ^ 3)
  rw [order40_chiC4C2_fst_four_inv_snd_g4]

@[simp]
theorem order40_action_chiC4C2_fst_four_inv_snd_g2 :
    (order40_action order40_chiC4C2_fst_four_inv_snd)
      (1, Multiplicative.ofAdd (1 : ZMod 2)) = unitAutHom (order40_u4 ^ 2) := by
  change unitAutHom (order40_chiC4C2_fst_four_inv_snd
    (1, Multiplicative.ofAdd (1 : ZMod 2))) = unitAutHom (order40_u4 ^ 2)
  rw [order40_chiC4C2_fst_four_inv_snd_g2]

noncomputable abbrev order40_chiC2C2C2 : order40_C2C2C2 →* (ZMod 5)ˣ :=
  order40_c2UnitHom.comp order88_chiC2C2C2

noncomputable abbrev order40_chiC2C2C2_snd : order40_C2C2C2 →* (ZMod 5)ˣ :=
  order40_c2UnitHom.comp order88_chiC2C2C2_snd

noncomputable abbrev order40_chiC2C2C2_trd : order40_C2C2C2 →* (ZMod 5)ˣ :=
  order40_c2UnitHom.comp order88_chiC2C2C2_trd

noncomputable abbrev order40_chiC2C2C2_fst_snd : order40_C2C2C2 →* (ZMod 5)ˣ :=
  order40_c2UnitHom.comp order88_chiC2C2C2_fst_snd

noncomputable abbrev order40_chiC2C2C2_fst_trd : order40_C2C2C2 →* (ZMod 5)ˣ :=
  order40_c2UnitHom.comp order88_chiC2C2C2_fst_trd

noncomputable abbrev order40_chiC2C2C2_snd_trd : order40_C2C2C2 →* (ZMod 5)ˣ :=
  order40_c2UnitHom.comp order88_chiC2C2C2_snd_trd

noncomputable abbrev order40_chiC2C2C2_fst_snd_trd : order40_C2C2C2 →* (ZMod 5)ˣ :=
  order40_c2UnitHom.comp order88_chiC2C2C2_fst_snd_trd

theorem order40_unit_sq_eq_one_cases (u : (ZMod 5)ˣ) (hu : u ^ 2 = 1) :
    u = 1 ∨ u = order40_u4 ^ 2 := by
  rcases order40_unit_cases u with h | h | h | h
  · exact Or.inl h
  · exfalso
    have hbad : order40_u4 ^ 2 = (1 : (ZMod 5)ˣ) := by simpa [h] using hu
    exact (by decide : order40_u4 ^ 2 ≠ (1 : (ZMod 5)ˣ)) hbad
  · exact Or.inr h
  · exfalso
    have hbad : (order40_u4 ^ 3) ^ 2 = (1 : (ZMod 5)ˣ) := by simpa [h] using hu
    exact (by decide : (order40_u4 ^ 3) ^ 2 ≠ (1 : (ZMod 5)ˣ)) hbad

/-- Homomorphisms out of `C₄ × C₂` are determined by the two standard generators. -/
theorem order40_c4c2_hom_ext {M : Type} [Group M] {χ ψ : order40_C4C2 →* M}
    (h4 : χ (Multiplicative.ofAdd (1 : ZMod 4), 1) =
      ψ (Multiplicative.ofAdd (1 : ZMod 4), 1))
    (h2 : χ (1, Multiplicative.ofAdd (1 : ZMod 2)) =
      ψ (1, Multiplicative.ofAdd (1 : ZMod 2))) :
    χ = ψ := by
  apply MonoidHom.ext
  rintro ⟨x4, x2⟩
  obtain ⟨a, rfl⟩ := Multiplicative.ofAdd.surjective x4
  obtain ⟨b, rfl⟩ := Multiplicative.ofAdd.surjective x2
  let g4 : order40_C4C2 := (Multiplicative.ofAdd (1 : ZMod 4), 1)
  let g2 : order40_C4C2 := (1, Multiplicative.ofAdd (1 : ZMod 2))
  have ha : Multiplicative.ofAdd a = (Multiplicative.ofAdd (1 : ZMod 4)) ^ a.val := by
    calc
      Multiplicative.ofAdd a = Multiplicative.ofAdd ((a.val : ZMod 4)) := by
        rw [ZMod.natCast_zmod_val]
      _ = Multiplicative.ofAdd (a.val • (1 : ZMod 4)) := by simp
      _ = (Multiplicative.ofAdd (1 : ZMod 4)) ^ a.val := by rw [ofAdd_nsmul]
  have hb : Multiplicative.ofAdd b = (Multiplicative.ofAdd (1 : ZMod 2)) ^ b.val := by
    calc
      Multiplicative.ofAdd b = Multiplicative.ofAdd ((b.val : ZMod 2)) := by
        rw [ZMod.natCast_zmod_val]
      _ = Multiplicative.ofAdd (b.val • (1 : ZMod 2)) := by simp
      _ = (Multiplicative.ofAdd (1 : ZMod 2)) ^ b.val := by rw [ofAdd_nsmul]
  have hx : (Multiplicative.ofAdd a, Multiplicative.ofAdd b) = g4 ^ a.val * g2 ^ b.val := by
    simp [g4, g2, Prod.pow_mk, ha, hb]
  rw [hx, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, h4, h2]

theorem order40_c4c2_unit_character_cases (χ : order40_C4C2 →* (ZMod 5)ˣ) :
    χ = 1 ∨ χ = order40_chiC4C2_fst_two ∨ χ = order40_chiC4C2_snd_two ∨
      χ = order40_chiC4C2_prod_two ∨ χ = order40_chiC4C2_fst_four ∨
      χ = order40_chiC4C2_fst_four_snd ∨ χ = order40_chiC4C2_fst_four_inv ∨
      χ = order40_chiC4C2_fst_four_inv_snd := by
  let g4 : order40_C4C2 := (Multiplicative.ofAdd (1 : ZMod 4), 1)
  let g2 : order40_C4C2 := (1, Multiplicative.ofAdd (1 : ZMod 2))
  have hsq2 : χ g2 ^ 2 = 1 := by
    rw [← map_pow, show g2 ^ 2 = 1 by decide, map_one]
  rcases order40_unit_cases (χ g4) with h4 | h4 | h4 | h4 <;>
    rcases order40_unit_sq_eq_one_cases (χ g2) hsq2 with h2 | h2
  · left
    apply order40_c4c2_hom_ext <;>
      simp [g4, g2, h4, h2]
  · right
    right
    left
    apply order40_c4c2_hom_ext <;>
      simp [g4, g2, h4, h2]
  · right
    right
    right
    right
    left
    apply order40_c4c2_hom_ext <;>
      simp [g4, g2, h4, h2]
  · right
    right
    right
    right
    right
    left
    apply order40_c4c2_hom_ext <;>
      simp [g4, g2, h4, h2]
  · right
    left
    apply order40_c4c2_hom_ext <;>
      simp [g4, g2, h4, h2]
  · right
    right
    right
    left
    apply order40_c4c2_hom_ext <;>
      simp [g4, g2, h4, h2]
  · right
    right
    right
    right
    right
    right
    left
    apply order40_c4c2_hom_ext <;>
      simp [g4, g2, h4, h2]
  · right
    right
    right
    right
    right
    right
    right
    apply order40_c4c2_hom_ext <;>
      simp [g4, g2, h4, h2]

/-- Homomorphisms out of `C₂³` are determined by the three standard generators. -/
theorem order40_c2c2c2_hom_ext {M : Type} [Group M]
    {χ ψ : order40_C2C2C2 →* M}
    (h1 : χ (Multiplicative.ofAdd (1 : ZMod 2), 1) =
      ψ (Multiplicative.ofAdd (1 : ZMod 2), 1))
    (h2 : χ (1, (Multiplicative.ofAdd (1 : ZMod 2), 1)) =
      ψ (1, (Multiplicative.ofAdd (1 : ZMod 2), 1)))
    (h3 : χ (1, (1, Multiplicative.ofAdd (1 : ZMod 2))) =
      ψ (1, (1, Multiplicative.ofAdd (1 : ZMod 2)))) :
    χ = ψ := by
  apply MonoidHom.ext
  rintro ⟨x1, x23⟩
  rcases x23 with ⟨x2, x3⟩
  obtain ⟨a, rfl⟩ := Multiplicative.ofAdd.surjective x1
  obtain ⟨b, rfl⟩ := Multiplicative.ofAdd.surjective x2
  obtain ⟨c, rfl⟩ := Multiplicative.ofAdd.surjective x3
  let g1 : order40_C2C2C2 := (Multiplicative.ofAdd (1 : ZMod 2), 1)
  let g2 : order40_C2C2C2 := (1, (Multiplicative.ofAdd (1 : ZMod 2), 1))
  let g3 : order40_C2C2C2 := (1, (1, Multiplicative.ofAdd (1 : ZMod 2)))
  have ha : Multiplicative.ofAdd a = (Multiplicative.ofAdd (1 : ZMod 2)) ^ a.val := by
    calc
      Multiplicative.ofAdd a = Multiplicative.ofAdd ((a.val : ZMod 2)) := by
        rw [ZMod.natCast_zmod_val]
      _ = Multiplicative.ofAdd (a.val • (1 : ZMod 2)) := by simp
      _ = (Multiplicative.ofAdd (1 : ZMod 2)) ^ a.val := by rw [ofAdd_nsmul]
  have hb : Multiplicative.ofAdd b = (Multiplicative.ofAdd (1 : ZMod 2)) ^ b.val := by
    calc
      Multiplicative.ofAdd b = Multiplicative.ofAdd ((b.val : ZMod 2)) := by
        rw [ZMod.natCast_zmod_val]
      _ = Multiplicative.ofAdd (b.val • (1 : ZMod 2)) := by simp
      _ = (Multiplicative.ofAdd (1 : ZMod 2)) ^ b.val := by rw [ofAdd_nsmul]
  have hc : Multiplicative.ofAdd c = (Multiplicative.ofAdd (1 : ZMod 2)) ^ c.val := by
    calc
      Multiplicative.ofAdd c = Multiplicative.ofAdd ((c.val : ZMod 2)) := by
        rw [ZMod.natCast_zmod_val]
      _ = Multiplicative.ofAdd (c.val • (1 : ZMod 2)) := by simp
      _ = (Multiplicative.ofAdd (1 : ZMod 2)) ^ c.val := by rw [ofAdd_nsmul]
  have hx : (Multiplicative.ofAdd a, (Multiplicative.ofAdd b, Multiplicative.ofAdd c)) =
      g1 ^ a.val * g2 ^ b.val * g3 ^ c.val := by
    simp [g1, g2, g3, Prod.pow_mk, ha, hb, hc]
  rw [hx, map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow,
    map_pow, map_pow, h1, h2, h3]

theorem order40_c2c2c2_unit_character_cases (χ : order40_C2C2C2 →* (ZMod 5)ˣ) :
    χ = 1 ∨ χ = order40_chiC2C2C2 ∨ χ = order40_chiC2C2C2_snd ∨
      χ = order40_chiC2C2C2_trd ∨ χ = order40_chiC2C2C2_fst_snd ∨
      χ = order40_chiC2C2C2_fst_trd ∨ χ = order40_chiC2C2C2_snd_trd ∨
      χ = order40_chiC2C2C2_fst_snd_trd := by
  let g1 : order40_C2C2C2 := (Multiplicative.ofAdd (1 : ZMod 2), 1)
  let g2 : order40_C2C2C2 := (1, (Multiplicative.ofAdd (1 : ZMod 2), 1))
  let g3 : order40_C2C2C2 := (1, (1, Multiplicative.ofAdd (1 : ZMod 2)))
  have hsq1 : χ g1 ^ 2 = 1 := by
    rw [← map_pow, show g1 ^ 2 = 1 by decide, map_one]
  have hsq2 : χ g2 ^ 2 = 1 := by
    rw [← map_pow, show g2 ^ 2 = 1 by decide, map_one]
  have hsq3 : χ g3 ^ 2 = 1 := by
    rw [← map_pow, show g3 ^ 2 = 1 by decide, map_one]
  rcases order40_unit_sq_eq_one_cases (χ g1) hsq1 with h1 | h1 <;>
    rcases order40_unit_sq_eq_one_cases (χ g2) hsq2 with h2 | h2 <;>
      rcases order40_unit_sq_eq_one_cases (χ g3) hsq3 with h3 | h3
  · left
    apply order40_c2c2c2_hom_ext <;>
      simp [g1, g2, g3, h1, h2, h3]
  · right
    right
    right
    left
    apply order40_c2c2c2_hom_ext <;>
      simp [g1, g2, g3, h1, h2, h3, order40_chiC2C2C2_trd, order40_c2UnitHom]
  · right
    right
    left
    apply order40_c2c2c2_hom_ext <;>
      simp [g1, g2, g3, h1, h2, h3, order40_chiC2C2C2_snd, order40_c2UnitHom]
  · right
    right
    right
    right
    right
    right
    left
    apply order40_c2c2c2_hom_ext <;>
      simp [g1, g2, g3, h1, h2, h3, order40_chiC2C2C2_snd_trd, order40_c2UnitHom]
  · right
    left
    apply order40_c2c2c2_hom_ext <;>
      simp [g1, g2, g3, h1, h2, h3, order40_chiC2C2C2, order40_c2UnitHom]
  · right
    right
    right
    right
    right
    left
    apply order40_c2c2c2_hom_ext <;>
      simp [g1, g2, g3, h1, h2, h3, order40_chiC2C2C2_fst_trd, order40_c2UnitHom]
  · right
    right
    right
    right
    left
    apply order40_c2c2c2_hom_ext <;>
      simp [g1, g2, g3, h1, h2, h3, order40_chiC2C2C2_fst_snd, order40_c2UnitHom]
  · right
    right
    right
    right
    right
    right
    right
    apply order40_c2c2c2_hom_ext <;>
      simp [g1, g2, g3, h1, h2, h3, order40_chiC2C2C2_fst_snd_trd, order40_c2UnitHom]

noncomputable abbrev order40_chiD8_rot : order40_D8 →* (ZMod 5)ˣ :=
  order40_c2UnitHom.comp order88_chiD8_rot

noncomputable abbrev order40_chiD8_ref : order40_D8 →* (ZMod 5)ˣ :=
  order40_c2UnitHom.comp order88_chiD8_ref

noncomputable abbrev order40_chiD8_prod : order40_D8 →* (ZMod 5)ˣ :=
  order40_c2UnitHom.comp order88_chiD8_prod

@[simp]
theorem order40_chiD8_rot_r1 :
    order40_chiD8_rot (DihedralGroup.r (1 : ZMod 4)) = order40_u4 ^ 2 := by
  decide

@[simp]
theorem order40_chiD8_rot_s0 :
    order40_chiD8_rot (DihedralGroup.sr (0 : ZMod 4)) = 1 := by
  decide

@[simp]
theorem order40_chiD8_ref_r1 :
    order40_chiD8_ref (DihedralGroup.r (1 : ZMod 4)) = 1 := by
  decide

@[simp]
theorem order40_chiD8_ref_s0 :
    order40_chiD8_ref (DihedralGroup.sr (0 : ZMod 4)) = order40_u4 ^ 2 := by
  decide

@[simp]
theorem order40_chiD8_prod_r1 :
    order40_chiD8_prod (DihedralGroup.r (1 : ZMod 4)) = order40_u4 ^ 2 := by
  decide

@[simp]
theorem order40_chiD8_prod_s0 :
    order40_chiD8_prod (DihedralGroup.sr (0 : ZMod 4)) = order40_u4 ^ 2 := by
  decide

@[simp]
theorem order40_action_chiD8_rot_r1 :
    (order40_action order40_chiD8_rot) (DihedralGroup.r (1 : ZMod 4)) =
      unitAutHom (order40_u4 ^ 2) := by
  change unitAutHom (order40_chiD8_rot (DihedralGroup.r (1 : ZMod 4))) =
    unitAutHom (order40_u4 ^ 2)
  rw [order40_chiD8_rot_r1]

@[simp]
theorem order40_action_chiD8_rot_s0 :
    (order40_action order40_chiD8_rot) (DihedralGroup.sr (0 : ZMod 4)) = 1 := by
  change unitAutHom (order40_chiD8_rot (DihedralGroup.sr (0 : ZMod 4))) = 1
  rw [order40_chiD8_rot_s0, map_one]

@[simp]
theorem order40_action_chiD8_ref_r1 :
    (order40_action order40_chiD8_ref) (DihedralGroup.r (1 : ZMod 4)) = 1 := by
  change unitAutHom (order40_chiD8_ref (DihedralGroup.r (1 : ZMod 4))) = 1
  rw [order40_chiD8_ref_r1, map_one]

@[simp]
theorem order40_action_chiD8_ref_s0 :
    (order40_action order40_chiD8_ref) (DihedralGroup.sr (0 : ZMod 4)) =
      unitAutHom (order40_u4 ^ 2) := by
  change unitAutHom (order40_chiD8_ref (DihedralGroup.sr (0 : ZMod 4))) =
    unitAutHom (order40_u4 ^ 2)
  rw [order40_chiD8_ref_s0]

@[simp]
theorem order40_action_chiD8_prod_r1 :
    (order40_action order40_chiD8_prod) (DihedralGroup.r (1 : ZMod 4)) =
      unitAutHom (order40_u4 ^ 2) := by
  change unitAutHom (order40_chiD8_prod (DihedralGroup.r (1 : ZMod 4))) =
    unitAutHom (order40_u4 ^ 2)
  rw [order40_chiD8_prod_r1]

@[simp]
theorem order40_action_chiD8_prod_s0 :
    (order40_action order40_chiD8_prod) (DihedralGroup.sr (0 : ZMod 4)) =
      unitAutHom (order40_u4 ^ 2) := by
  change unitAutHom (order40_chiD8_prod (DihedralGroup.sr (0 : ZMod 4))) =
    unitAutHom (order40_u4 ^ 2)
  rw [order40_chiD8_prod_s0]

noncomputable abbrev order40_chiQ8 : order40_Q8 →* (ZMod 5)ˣ :=
  order40_c2UnitHom.comp order88_chiQ8

noncomputable abbrev order40_chiQ8_xa : order40_Q8 →* (ZMod 5)ˣ :=
  order40_c2UnitHom.comp order88_chiQ8_xa

noncomputable abbrev order40_chiQ8_prod : order40_Q8 →* (ZMod 5)ˣ :=
  order40_c2UnitHom.comp order88_chiQ8_prod

@[simp]
theorem order40_chiQ8_a1 :
    order40_chiQ8 (QuaternionGroup.a (1 : ZMod 4)) = order40_u4 ^ 2 := by
  decide

@[simp]
theorem order40_chiQ8_x0 :
    order40_chiQ8 (QuaternionGroup.xa (0 : ZMod 4)) = 1 := by
  decide

@[simp]
theorem order40_chiQ8_xa_a1 :
    order40_chiQ8_xa (QuaternionGroup.a (1 : ZMod 4)) = 1 := by
  decide

@[simp]
theorem order40_chiQ8_xa_x0 :
    order40_chiQ8_xa (QuaternionGroup.xa (0 : ZMod 4)) = order40_u4 ^ 2 := by
  decide

@[simp]
theorem order40_chiQ8_prod_a1 :
    order40_chiQ8_prod (QuaternionGroup.a (1 : ZMod 4)) = order40_u4 ^ 2 := by
  decide

@[simp]
theorem order40_chiQ8_prod_x0 :
    order40_chiQ8_prod (QuaternionGroup.xa (0 : ZMod 4)) = order40_u4 ^ 2 := by
  decide

@[simp]
theorem order40_action_chiQ8_a1 :
    (order40_action order40_chiQ8) (QuaternionGroup.a (1 : ZMod 4)) =
      unitAutHom (order40_u4 ^ 2) := by
  change unitAutHom (order40_chiQ8 (QuaternionGroup.a (1 : ZMod 4))) =
    unitAutHom (order40_u4 ^ 2)
  rw [order40_chiQ8_a1]

@[simp]
theorem order40_action_chiQ8_x0 :
    (order40_action order40_chiQ8) (QuaternionGroup.xa (0 : ZMod 4)) = 1 := by
  change unitAutHom (order40_chiQ8 (QuaternionGroup.xa (0 : ZMod 4))) = 1
  rw [order40_chiQ8_x0, map_one]

@[simp]
theorem order40_action_chiQ8_xa_a1 :
    (order40_action order40_chiQ8_xa) (QuaternionGroup.a (1 : ZMod 4)) = 1 := by
  change unitAutHom (order40_chiQ8_xa (QuaternionGroup.a (1 : ZMod 4))) = 1
  rw [order40_chiQ8_xa_a1, map_one]

@[simp]
theorem order40_action_chiQ8_xa_x0 :
    (order40_action order40_chiQ8_xa) (QuaternionGroup.xa (0 : ZMod 4)) =
      unitAutHom (order40_u4 ^ 2) := by
  change unitAutHom (order40_chiQ8_xa (QuaternionGroup.xa (0 : ZMod 4))) =
    unitAutHom (order40_u4 ^ 2)
  rw [order40_chiQ8_xa_x0]

@[simp]
theorem order40_action_chiQ8_prod_a1 :
    (order40_action order40_chiQ8_prod) (QuaternionGroup.a (1 : ZMod 4)) =
      unitAutHom (order40_u4 ^ 2) := by
  change unitAutHom (order40_chiQ8_prod (QuaternionGroup.a (1 : ZMod 4))) =
    unitAutHom (order40_u4 ^ 2)
  rw [order40_chiQ8_prod_a1]

@[simp]
theorem order40_action_chiQ8_prod_x0 :
    (order40_action order40_chiQ8_prod) (QuaternionGroup.xa (0 : ZMod 4)) =
      unitAutHom (order40_u4 ^ 2) := by
  change unitAutHom (order40_chiQ8_prod (QuaternionGroup.xa (0 : ZMod 4))) =
    unitAutHom (order40_u4 ^ 2)
  rw [order40_chiQ8_prod_x0]

/-- Homomorphisms out of `D₈` are determined by a rotation and a reflection. -/
theorem order40_d8_hom_ext {M : Type} [Group M] {χ ψ : order40_D8 →* M}
    (hr : χ (DihedralGroup.r (1 : ZMod 4)) =
      ψ (DihedralGroup.r (1 : ZMod 4)))
    (hs : χ (DihedralGroup.sr (0 : ZMod 4)) =
      ψ (DihedralGroup.sr (0 : ZMod 4))) :
    χ = ψ := by
  apply MonoidHom.ext
  intro x
  rcases x with i | i
  · have hi : DihedralGroup.r i = (DihedralGroup.r (1 : ZMod 4)) ^ i.val := by
      calc
        DihedralGroup.r i = DihedralGroup.r ((i.val : ZMod 4)) := by
          rw [ZMod.natCast_zmod_val]
        _ = DihedralGroup.r ((1 : ZMod 4) * (i.val : ZMod 4)) := by simp
        _ = (DihedralGroup.r (1 : ZMod 4)) ^ i.val := by rw [DihedralGroup.r_pow]
    rw [hi, map_pow, map_pow, hr]
  · have hri : DihedralGroup.r i = (DihedralGroup.r (1 : ZMod 4)) ^ i.val := by
      calc
        DihedralGroup.r i = DihedralGroup.r ((i.val : ZMod 4)) := by
          rw [ZMod.natCast_zmod_val]
        _ = DihedralGroup.r ((1 : ZMod 4) * (i.val : ZMod 4)) := by simp
        _ = (DihedralGroup.r (1 : ZMod 4)) ^ i.val := by rw [DihedralGroup.r_pow]
    have hi : DihedralGroup.sr i =
        DihedralGroup.sr (0 : ZMod 4) * (DihedralGroup.r (1 : ZMod 4)) ^ i.val := by
      rw [← hri]
      simp [DihedralGroup.sr_mul_r]
    rw [hi, map_mul, map_mul, map_pow, map_pow, hs, hr]

theorem order40_d8_character_rot_sq (χ : order40_D8 →* (ZMod 5)ˣ) :
    χ (DihedralGroup.r (1 : ZMod 4)) ^ 2 = 1 := by
  let r1 : order40_D8 := DihedralGroup.r (1 : ZMod 4)
  let s0 : order40_D8 := DihedralGroup.sr (0 : ZMod 4)
  have hrel : s0 * r1 = r1⁻¹ * s0 := by
    simp [r1, s0, DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.inv_r]
  have himg : χ (s0 * r1) = χ (r1⁻¹ * s0) := congrArg χ hrel
  rw [map_mul, map_mul, map_inv] at himg
  have hmul : χ r1 = (χ r1)⁻¹ := by
    have := congrArg (fun x => x * (χ s0)⁻¹) himg
    simpa [mul_assoc, mul_comm, mul_left_comm] using this
  rw [pow_two]
  nth_rw 2 [hmul]
  exact mul_inv_cancel _

theorem order40_d8_unit_character_cases (χ : order40_D8 →* (ZMod 5)ˣ) :
    χ = 1 ∨ χ = order40_chiD8_rot ∨ χ = order40_chiD8_ref ∨
      χ = order40_chiD8_prod := by
  let r1 : order40_D8 := DihedralGroup.r (1 : ZMod 4)
  let s0 : order40_D8 := DihedralGroup.sr (0 : ZMod 4)
  have hsq_r : χ r1 ^ 2 = 1 := by
    exact order40_d8_character_rot_sq χ
  have hsq_s : χ s0 ^ 2 = 1 := by
    rw [← map_pow, show s0 ^ 2 = 1 by decide, map_one]
  rcases order40_unit_sq_eq_one_cases (χ r1) hsq_r with hr | hr <;>
    rcases order40_unit_sq_eq_one_cases (χ s0) hsq_s with hs | hs
  · left
    apply order40_d8_hom_ext <;>
      simp [r1, s0, hr, hs]
  · right
    right
    left
    apply order40_d8_hom_ext <;>
      simp [r1, s0, hr, hs]
  · right
    left
    apply order40_d8_hom_ext <;>
      simp [r1, s0, hr, hs]
  · right
    right
    right
    apply order40_d8_hom_ext <;>
      simp [r1, s0, hr, hs]

/-- Homomorphisms out of `Q₈` are determined by the two displayed four-order generators. -/
theorem order40_q8_hom_ext {M : Type} [Group M] {χ ψ : order40_Q8 →* M}
    (ha : χ (QuaternionGroup.a (1 : ZMod 4)) =
      ψ (QuaternionGroup.a (1 : ZMod 4)))
    (hx : χ (QuaternionGroup.xa (0 : ZMod 4)) =
      ψ (QuaternionGroup.xa (0 : ZMod 4))) :
    χ = ψ := by
  apply MonoidHom.ext
  intro x
  rcases x with i | i
  · have hi : QuaternionGroup.a i = (QuaternionGroup.a (1 : ZMod 4) : order40_Q8) ^ i.val := by
      calc
        QuaternionGroup.a i = QuaternionGroup.a ((i.val : ZMod 4)) := by
          rw [ZMod.natCast_zmod_val]
        _ = (QuaternionGroup.a (1 : ZMod 4) : order40_Q8) ^ i.val := by
          rw [QuaternionGroup.a_one_pow]
    rw [hi, map_pow, map_pow, ha]
  · have hai : QuaternionGroup.a i =
        (QuaternionGroup.a (1 : ZMod 4) : order40_Q8) ^ i.val := by
      calc
        QuaternionGroup.a i = QuaternionGroup.a ((i.val : ZMod 4)) := by
          rw [ZMod.natCast_zmod_val]
        _ = (QuaternionGroup.a (1 : ZMod 4) : order40_Q8) ^ i.val := by
          rw [QuaternionGroup.a_one_pow]
    have hi : QuaternionGroup.xa i =
        QuaternionGroup.xa (0 : ZMod 4) *
          (QuaternionGroup.a (1 : ZMod 4) : order40_Q8) ^ i.val := by
      rw [← hai]
      simp [QuaternionGroup.xa_mul_a]
    rw [hi, map_mul, map_mul, map_pow, map_pow, hx, ha]

theorem order40_q8_character_a_sq (χ : order40_Q8 →* (ZMod 5)ˣ) :
    χ (QuaternionGroup.a (1 : ZMod 4)) ^ 2 = 1 := by
  let a1 : order40_Q8 := QuaternionGroup.a (1 : ZMod 4)
  let x0 : order40_Q8 := QuaternionGroup.xa (0 : ZMod 4)
  have hrel : x0 * a1 = a1⁻¹ * x0 := by decide
  have himg : χ (x0 * a1) = χ (a1⁻¹ * x0) := congrArg χ hrel
  rw [map_mul, map_mul, map_inv] at himg
  have hmul : χ a1 = (χ a1)⁻¹ := by
    have := congrArg (fun x => x * (χ x0)⁻¹) himg
    simpa [mul_assoc, mul_comm, mul_left_comm] using this
  rw [pow_two]
  nth_rw 2 [hmul]
  exact mul_inv_cancel _

theorem order40_q8_character_x_sq (χ : order40_Q8 →* (ZMod 5)ˣ)
    (ha : χ (QuaternionGroup.a (1 : ZMod 4)) ^ 2 = 1) :
    χ (QuaternionGroup.xa (0 : ZMod 4)) ^ 2 = 1 := by
  let a1 : order40_Q8 := QuaternionGroup.a (1 : ZMod 4)
  let x0 : order40_Q8 := QuaternionGroup.xa (0 : ZMod 4)
  have hrel : x0 ^ 2 = a1 ^ 2 := by decide
  have himg : χ (x0 ^ 2) = χ (a1 ^ 2) := congrArg χ hrel
  rw [map_pow, map_pow] at himg
  change χ x0 ^ 2 = 1
  rw [himg]
  exact ha

theorem order40_q8_unit_character_cases (χ : order40_Q8 →* (ZMod 5)ˣ) :
    χ = 1 ∨ χ = order40_chiQ8 ∨ χ = order40_chiQ8_xa ∨
      χ = order40_chiQ8_prod := by
  let a1 : order40_Q8 := QuaternionGroup.a (1 : ZMod 4)
  let x0 : order40_Q8 := QuaternionGroup.xa (0 : ZMod 4)
  have hsq_a : χ a1 ^ 2 = 1 := by
    exact order40_q8_character_a_sq χ
  have hsq_x : χ x0 ^ 2 = 1 := by
    exact order40_q8_character_x_sq χ hsq_a
  rcases order40_unit_sq_eq_one_cases (χ a1) hsq_a with ha | ha <;>
    rcases order40_unit_sq_eq_one_cases (χ x0) hsq_x with hx | hx
  · left
    apply order40_q8_hom_ext <;>
      simp [a1, x0, ha, hx]
  · right
    right
    left
    apply order40_q8_hom_ext <;>
      simp [a1, x0, ha, hx]
  · right
    left
    apply order40_q8_hom_ext <;>
      simp [a1, x0, ha, hx]
  · right
    right
    right
    apply order40_q8_hom_ext <;>
      simp [a1, x0, ha, hx]

/-- Direct-product representative attached to a group `H` of order `8`. -/
abbrev order40_DP (H : Type) : Type := order40_C5 × H

/-- Semidirect-product representative attached to a character `χ : H → (ZMod 5)ˣ`. -/
noncomputable abbrev order40_SD (H : Type) [Group H] (χ : H →* (ZMod 5)ˣ) : Type :=
  SemidirectProduct order40_C5 H (order40_action χ)

noncomputable def order40_SD_equiv_of_character_comp {H : Type} [Group H]
    (χ ψ : H →* (ZMod 5)ˣ) (σ : H ≃* H)
    (hχ : χ.comp σ.toMonoidHom = ψ) :
    order40_SD H ψ ≃* order40_SD H χ := by
  have haction : (order40_action χ).comp σ.toMonoidHom = order40_action ψ := by
    ext h x
    change unitAutHom (χ (σ h)) x = unitAutHom (ψ h) x
    rw [show χ (σ h) = ψ h from congrArg (fun f : H →* (ZMod 5)ˣ => f h) hχ]
  exact (semidirectProductCongr_eq haction.symm).trans
    (semidirectProductCongrAut (N := order40_C5) (φ := order40_action χ) σ)

noncomputable instance instFintypeOrder40SD {H : Type} [Group H] [Fintype H]
    (χ : H →* (ZMod 5)ˣ) : Fintype (order40_SD H χ) :=
  Fintype.ofEquiv (order40_C5 × H) SemidirectProduct.equivProd.symm

noncomputable abbrev order40_RA : Type := order40_DP order40_C8
noncomputable abbrev order40_RB : Type := order40_SD order40_C8 order40_chiC8_two
noncomputable abbrev order40_RC : Type := order40_SD order40_C8 order40_chiC8_four
noncomputable abbrev order40_RD : Type := order40_DP order40_C4C2
noncomputable abbrev order40_RE : Type := order40_SD order40_C4C2 order40_chiC4C2_fst_two
noncomputable abbrev order40_RF : Type := order40_SD order40_C4C2 order40_chiC4C2_snd_two
noncomputable abbrev order40_RG : Type := order40_SD order40_C4C2 order40_chiC4C2_fst_four
noncomputable abbrev order40_RH : Type := order40_DP order40_C2C2C2
noncomputable abbrev order40_RI : Type := order40_SD order40_C2C2C2 order40_chiC2C2C2
noncomputable abbrev order40_RJ : Type := order40_DP order40_D8
noncomputable abbrev order40_RK : Type := order40_SD order40_D8 order40_chiD8_rot
noncomputable abbrev order40_RL : Type := order40_SD order40_D8 order40_chiD8_ref
noncomputable abbrev order40_RM : Type := order40_DP order40_Q8
noncomputable abbrev order40_RN : Type := order40_SD order40_Q8 order40_chiQ8

noncomputable def order40_c8_four_inv_equiv_four :
    order40_SD order40_C8 order40_chiC8_four_inv ≃* order40_RC :=
  order40_SD_equiv_of_character_comp order40_chiC8_four order40_chiC8_four_inv
    order40_C8_mulThree order40_chiC8_four_comp_mulThree

noncomputable def order40_C4C2_mulThree : order40_C4C2 ≃* order40_C4C2 where
  toFun x := (x.1 ^ 3, x.2)
  invFun x := (x.1 ^ 3, x.2)
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

noncomputable def order40_C4C2_addSecond : order40_C4C2 ≃* order40_C4C2 where
  toFun x := (x.1 * (if x.2 = 1 then 1 else Multiplicative.ofAdd (2 : ZMod 4)), x.2)
  invFun x := (x.1 * (if x.2 = 1 then 1 else Multiplicative.ofAdd (2 : ZMod 4)), x.2)
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

noncomputable def order40_C4C2_mulThreeAddSecond : order40_C4C2 ≃* order40_C4C2 where
  toFun x := (x.1 ^ 3 * (if x.2 = 1 then 1 else Multiplicative.ofAdd (2 : ZMod 4)), x.2)
  invFun x := (x.1 ^ 3 * (if x.2 = 1 then 1 else Multiplicative.ofAdd (2 : ZMod 4)), x.2)
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

theorem order40_chiC4C2_snd_two_comp_shear :
    order40_chiC4C2_snd_two.comp order88_C4C2_shear.toMonoidHom =
      order40_chiC4C2_prod_two := by
  unfold order40_chiC4C2_snd_two order40_chiC4C2_prod_two
  rw [MonoidHom.comp_assoc, order88_chiC4C2_snd_comp_shear]

theorem order40_chiC4C2_fst_four_comp_addSecond :
    order40_chiC4C2_fst_four.comp order40_C4C2_addSecond.toMonoidHom =
      order40_chiC4C2_fst_four_snd := by
  apply order40_c4c2_hom_ext <;> decide

theorem order40_chiC4C2_fst_four_comp_mulThree :
    order40_chiC4C2_fst_four.comp order40_C4C2_mulThree.toMonoidHom =
      order40_chiC4C2_fst_four_inv := by
  apply order40_c4c2_hom_ext <;> decide

theorem order40_chiC4C2_fst_four_comp_mulThreeAddSecond :
    order40_chiC4C2_fst_four.comp order40_C4C2_mulThreeAddSecond.toMonoidHom =
      order40_chiC4C2_fst_four_inv_snd := by
  apply order40_c4c2_hom_ext <;> decide

noncomputable def order40_c4c2_prod_two_equiv_snd :
    order40_SD order40_C4C2 order40_chiC4C2_prod_two ≃*
      order40_RF :=
  order40_SD_equiv_of_character_comp order40_chiC4C2_snd_two
    order40_chiC4C2_prod_two order88_C4C2_shear order40_chiC4C2_snd_two_comp_shear

noncomputable def order40_c4c2_fst_four_snd_equiv_four :
    order40_SD order40_C4C2 order40_chiC4C2_fst_four_snd ≃*
      order40_RG :=
  order40_SD_equiv_of_character_comp order40_chiC4C2_fst_four
    order40_chiC4C2_fst_four_snd order40_C4C2_addSecond
    order40_chiC4C2_fst_four_comp_addSecond

noncomputable def order40_c4c2_fst_four_inv_equiv_four :
    order40_SD order40_C4C2 order40_chiC4C2_fst_four_inv ≃*
      order40_RG :=
  order40_SD_equiv_of_character_comp order40_chiC4C2_fst_four
    order40_chiC4C2_fst_four_inv order40_C4C2_mulThree
    order40_chiC4C2_fst_four_comp_mulThree

noncomputable def order40_c4c2_fst_four_inv_snd_equiv_four :
    order40_SD order40_C4C2 order40_chiC4C2_fst_four_inv_snd ≃*
      order40_RG :=
  order40_SD_equiv_of_character_comp order40_chiC4C2_fst_four
    order40_chiC4C2_fst_four_inv_snd order40_C4C2_mulThreeAddSecond
    order40_chiC4C2_fst_four_comp_mulThreeAddSecond

theorem order40_chiC2C2C2_comp_swap12 :
    order40_chiC2C2C2.comp order88_C2C2C2_swap12.toMonoidHom =
      order40_chiC2C2C2_snd := by
  unfold order40_chiC2C2C2 order40_chiC2C2C2_snd
  rw [MonoidHom.comp_assoc, order88_chiC2C2C2_comp_swap12]

theorem order40_chiC2C2C2_comp_swap13 :
    order40_chiC2C2C2.comp order88_C2C2C2_swap13.toMonoidHom =
      order40_chiC2C2C2_trd := by
  unfold order40_chiC2C2C2 order40_chiC2C2C2_trd
  rw [MonoidHom.comp_assoc, order88_chiC2C2C2_comp_swap13]

theorem order40_chiC2C2C2_comp_shear12 :
    order40_chiC2C2C2.comp order88_C2C2C2_shear12.toMonoidHom =
      order40_chiC2C2C2_fst_snd := by
  unfold order40_chiC2C2C2 order40_chiC2C2C2_fst_snd
  rw [MonoidHom.comp_assoc, order88_chiC2C2C2_comp_shear12]

theorem order40_chiC2C2C2_comp_shear13 :
    order40_chiC2C2C2.comp order88_C2C2C2_shear13.toMonoidHom =
      order40_chiC2C2C2_fst_trd := by
  unfold order40_chiC2C2C2 order40_chiC2C2C2_fst_trd
  rw [MonoidHom.comp_assoc, order88_chiC2C2C2_comp_shear13]

theorem order40_chiC2C2C2_comp_shear23 :
    order40_chiC2C2C2.comp order88_C2C2C2_shear23.toMonoidHom =
      order40_chiC2C2C2_snd_trd := by
  unfold order40_chiC2C2C2 order40_chiC2C2C2_snd_trd
  rw [MonoidHom.comp_assoc, order88_chiC2C2C2_comp_shear23]

theorem order40_chiC2C2C2_comp_shear123 :
    order40_chiC2C2C2.comp order88_C2C2C2_shear123.toMonoidHom =
      order40_chiC2C2C2_fst_snd_trd := by
  unfold order40_chiC2C2C2 order40_chiC2C2C2_fst_snd_trd
  rw [MonoidHom.comp_assoc, order88_chiC2C2C2_comp_shear123]

noncomputable def order40_c2c2c2_snd_equiv :
    order40_SD order40_C2C2C2 order40_chiC2C2C2_snd ≃*
      order40_RI :=
  order40_SD_equiv_of_character_comp order40_chiC2C2C2 order40_chiC2C2C2_snd
    order88_C2C2C2_swap12 order40_chiC2C2C2_comp_swap12

noncomputable def order40_c2c2c2_trd_equiv :
    order40_SD order40_C2C2C2 order40_chiC2C2C2_trd ≃*
      order40_RI :=
  order40_SD_equiv_of_character_comp order40_chiC2C2C2 order40_chiC2C2C2_trd
    order88_C2C2C2_swap13 order40_chiC2C2C2_comp_swap13

noncomputable def order40_c2c2c2_fst_snd_equiv :
    order40_SD order40_C2C2C2 order40_chiC2C2C2_fst_snd ≃*
      order40_RI :=
  order40_SD_equiv_of_character_comp order40_chiC2C2C2 order40_chiC2C2C2_fst_snd
    order88_C2C2C2_shear12 order40_chiC2C2C2_comp_shear12

noncomputable def order40_c2c2c2_fst_trd_equiv :
    order40_SD order40_C2C2C2 order40_chiC2C2C2_fst_trd ≃*
      order40_RI :=
  order40_SD_equiv_of_character_comp order40_chiC2C2C2 order40_chiC2C2C2_fst_trd
    order88_C2C2C2_shear13 order40_chiC2C2C2_comp_shear13

noncomputable def order40_c2c2c2_snd_trd_equiv :
    order40_SD order40_C2C2C2 order40_chiC2C2C2_snd_trd ≃*
      order40_RI :=
  order40_SD_equiv_of_character_comp order40_chiC2C2C2 order40_chiC2C2C2_snd_trd
    order88_C2C2C2_shear23 order40_chiC2C2C2_comp_shear23

noncomputable def order40_c2c2c2_fst_snd_trd_equiv :
    order40_SD order40_C2C2C2 order40_chiC2C2C2_fst_snd_trd ≃*
      order40_RI :=
  order40_SD_equiv_of_character_comp order40_chiC2C2C2 order40_chiC2C2C2_fst_snd_trd
    order88_C2C2C2_shear123 order40_chiC2C2C2_comp_shear123

theorem order40_chiD8_rot_comp_shear :
    order40_chiD8_rot.comp order88_D8_shear.toMonoidHom =
      order40_chiD8_prod := by
  unfold order40_chiD8_rot order40_chiD8_prod
  rw [MonoidHom.comp_assoc, order88_chiD8_rot_comp_shear]

noncomputable def order40_d8_prod_equiv_rot :
    order40_SD order40_D8 order40_chiD8_prod ≃*
      order40_RK :=
  order40_SD_equiv_of_character_comp order40_chiD8_rot order40_chiD8_prod
    order88_D8_shear order40_chiD8_rot_comp_shear

theorem order40_chiQ8_comp_shear :
    order40_chiQ8.comp order88_Q8_shear.toMonoidHom =
      order40_chiQ8_prod := by
  unfold order40_chiQ8 order40_chiQ8_prod
  rw [MonoidHom.comp_assoc, order88_chiQ8_comp_shear]

theorem order40_chiQ8_comp_swap :
    order40_chiQ8.comp order88_Q8_swap.toMonoidHom =
      order40_chiQ8_xa := by
  unfold order40_chiQ8 order40_chiQ8_xa
  rw [MonoidHom.comp_assoc, order88_chiQ8_comp_swap]

noncomputable def order40_q8_prod_equiv_q8 :
    order40_SD order40_Q8 order40_chiQ8_prod ≃*
      order40_RN :=
  order40_SD_equiv_of_character_comp order40_chiQ8 order40_chiQ8_prod
    order88_Q8_shear order40_chiQ8_comp_shear

noncomputable def order40_q8_xa_equiv_q8 :
    order40_SD order40_Q8 order40_chiQ8_xa ≃*
      order40_RN :=
  order40_SD_equiv_of_character_comp order40_chiQ8 order40_chiQ8_xa
    order88_Q8_swap order40_chiQ8_comp_swap

theorem order40_c8_character_semidirect_cases (χ : order40_C8 →* (ZMod 5)ˣ) :
    Nonempty (order40_SD order40_C8 χ ≃* order40_RA) ∨
      Nonempty (order40_SD order40_C8 χ ≃* order40_RB) ∨
      Nonempty (order40_SD order40_C8 χ ≃* order40_RC) := by
  rcases order40_c8_unit_character_cases χ with hχ | hχ | hχ | hχ
  · left
    have haction : order40_action χ = 1 := by
      rw [hχ]
      ext h x
      simp [order40_action]
    exact ⟨(semidirectProductCongr_eq haction).trans SemidirectProduct.mulEquivProd⟩
  · right
    right
    have haction : order40_action χ = order40_action order40_chiC8_four := by
      rw [hχ]
    exact ⟨semidirectProductCongr_eq haction⟩
  · right
    left
    have haction : order40_action χ = order40_action order40_chiC8_two := by
      rw [hχ]
    exact ⟨semidirectProductCongr_eq haction⟩
  · right
    right
    have haction : order40_action χ = order40_action order40_chiC8_four_inv := by
      rw [hχ]
    exact ⟨(semidirectProductCongr_eq haction).trans order40_c8_four_inv_equiv_four⟩

theorem order40_c4c2_character_semidirect_cases (χ : order40_C4C2 →* (ZMod 5)ˣ) :
    Nonempty (order40_SD order40_C4C2 χ ≃* order40_RD) ∨
      Nonempty (order40_SD order40_C4C2 χ ≃* order40_RE) ∨
      Nonempty (order40_SD order40_C4C2 χ ≃* order40_RF) ∨
      Nonempty (order40_SD order40_C4C2 χ ≃* order40_RG) := by
  rcases order40_c4c2_unit_character_cases χ with
    hχ | hχ | hχ | hχ | hχ | hχ | hχ | hχ
  · left
    have haction : order40_action χ = 1 := by
      rw [hχ]
      ext h x
      simp [order40_action]
    exact ⟨(semidirectProductCongr_eq haction).trans SemidirectProduct.mulEquivProd⟩
  · right
    left
    have haction : order40_action χ = order40_action order40_chiC4C2_fst_two := by rw [hχ]
    exact ⟨semidirectProductCongr_eq haction⟩
  · right
    right
    left
    have haction : order40_action χ = order40_action order40_chiC4C2_snd_two := by rw [hχ]
    exact ⟨semidirectProductCongr_eq haction⟩
  · right
    right
    left
    have haction : order40_action χ = order40_action order40_chiC4C2_prod_two := by rw [hχ]
    exact ⟨(semidirectProductCongr_eq haction).trans order40_c4c2_prod_two_equiv_snd⟩
  · right
    right
    right
    have haction : order40_action χ = order40_action order40_chiC4C2_fst_four := by rw [hχ]
    exact ⟨semidirectProductCongr_eq haction⟩
  · right
    right
    right
    have haction : order40_action χ = order40_action order40_chiC4C2_fst_four_snd := by
      rw [hχ]
    exact ⟨(semidirectProductCongr_eq haction).trans order40_c4c2_fst_four_snd_equiv_four⟩
  · right
    right
    right
    have haction : order40_action χ = order40_action order40_chiC4C2_fst_four_inv := by
      rw [hχ]
    exact ⟨(semidirectProductCongr_eq haction).trans order40_c4c2_fst_four_inv_equiv_four⟩
  · right
    right
    right
    have haction : order40_action χ =
        order40_action order40_chiC4C2_fst_four_inv_snd := by rw [hχ]
    exact ⟨(semidirectProductCongr_eq haction).trans
      order40_c4c2_fst_four_inv_snd_equiv_four⟩

theorem order40_c2c2c2_character_semidirect_cases
    (χ : order40_C2C2C2 →* (ZMod 5)ˣ) :
    Nonempty (order40_SD order40_C2C2C2 χ ≃* order40_RH) ∨
      Nonempty (order40_SD order40_C2C2C2 χ ≃* order40_RI) := by
  rcases order40_c2c2c2_unit_character_cases χ with
    hχ | hχ | hχ | hχ | hχ | hχ | hχ | hχ
  · left
    have haction : order40_action χ = 1 := by
      rw [hχ]
      ext h x
      simp [order40_action]
    exact ⟨(semidirectProductCongr_eq haction).trans SemidirectProduct.mulEquivProd⟩
  · right
    have haction : order40_action χ = order40_action order40_chiC2C2C2 := by rw [hχ]
    exact ⟨semidirectProductCongr_eq haction⟩
  · right
    have haction : order40_action χ = order40_action order40_chiC2C2C2_snd := by rw [hχ]
    exact ⟨(semidirectProductCongr_eq haction).trans order40_c2c2c2_snd_equiv⟩
  · right
    have haction : order40_action χ = order40_action order40_chiC2C2C2_trd := by rw [hχ]
    exact ⟨(semidirectProductCongr_eq haction).trans order40_c2c2c2_trd_equiv⟩
  · right
    have haction : order40_action χ = order40_action order40_chiC2C2C2_fst_snd := by rw [hχ]
    exact ⟨(semidirectProductCongr_eq haction).trans order40_c2c2c2_fst_snd_equiv⟩
  · right
    have haction : order40_action χ = order40_action order40_chiC2C2C2_fst_trd := by rw [hχ]
    exact ⟨(semidirectProductCongr_eq haction).trans order40_c2c2c2_fst_trd_equiv⟩
  · right
    have haction : order40_action χ = order40_action order40_chiC2C2C2_snd_trd := by rw [hχ]
    exact ⟨(semidirectProductCongr_eq haction).trans order40_c2c2c2_snd_trd_equiv⟩
  · right
    have haction : order40_action χ =
        order40_action order40_chiC2C2C2_fst_snd_trd := by rw [hχ]
    exact ⟨(semidirectProductCongr_eq haction).trans order40_c2c2c2_fst_snd_trd_equiv⟩

theorem order40_d8_character_semidirect_cases (χ : order40_D8 →* (ZMod 5)ˣ) :
    Nonempty (order40_SD order40_D8 χ ≃* order40_RJ) ∨
      Nonempty (order40_SD order40_D8 χ ≃* order40_RK) ∨
      Nonempty (order40_SD order40_D8 χ ≃* order40_RL) := by
  rcases order40_d8_unit_character_cases χ with hχ | hχ | hχ | hχ
  · left
    have haction : order40_action χ = 1 := by
      rw [hχ]
      ext h x
      simp [order40_action]
    exact ⟨(semidirectProductCongr_eq haction).trans SemidirectProduct.mulEquivProd⟩
  · right
    left
    have haction : order40_action χ = order40_action order40_chiD8_rot := by rw [hχ]
    exact ⟨semidirectProductCongr_eq haction⟩
  · right
    right
    have haction : order40_action χ = order40_action order40_chiD8_ref := by rw [hχ]
    exact ⟨semidirectProductCongr_eq haction⟩
  · right
    left
    have haction : order40_action χ = order40_action order40_chiD8_prod := by rw [hχ]
    exact ⟨(semidirectProductCongr_eq haction).trans order40_d8_prod_equiv_rot⟩

theorem order40_q8_character_semidirect_cases (χ : order40_Q8 →* (ZMod 5)ˣ) :
    Nonempty (order40_SD order40_Q8 χ ≃* order40_RM) ∨
      Nonempty (order40_SD order40_Q8 χ ≃* order40_RN) := by
  rcases order40_q8_unit_character_cases χ with hχ | hχ | hχ | hχ
  · left
    have haction : order40_action χ = 1 := by
      rw [hχ]
      ext h x
      simp [order40_action]
    exact ⟨(semidirectProductCongr_eq haction).trans SemidirectProduct.mulEquivProd⟩
  · right
    have haction : order40_action χ = order40_action order40_chiQ8 := by rw [hχ]
    exact ⟨semidirectProductCongr_eq haction⟩
  · right
    have haction : order40_action χ = order40_action order40_chiQ8_xa := by rw [hχ]
    exact ⟨(semidirectProductCongr_eq haction).trans order40_q8_xa_equiv_q8⟩
  · right
    have haction : order40_action χ = order40_action order40_chiQ8_prod := by rw [hχ]
    exact ⟨(semidirectProductCongr_eq haction).trans order40_q8_prod_equiv_q8⟩

theorem order40_mulAut_sq_eq_one_cases (α : MulAut order40_C5) (hα : α ^ 2 = 1) :
    α = 1 ∨ α = unitAutHom (order40_u4 ^ 2) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨u, hu⟩ := exists_unitAutHom_eq (p := 5) α
  have hu2 : u ^ 2 = 1 := by
    apply unitAutHom_injective (p := 5)
    rw [map_pow, ← hu, hα, map_one]
  rcases order40_unit_sq_eq_one_cases u hu2 with h | h
  · left
    rw [hu, h, map_one]
  · right
    rw [hu, h]

theorem order40_d8_action_rot_sq (φ : order40_D8 →* MulAut order40_C5) :
    φ (DihedralGroup.r (1 : ZMod 4)) ^ 2 = 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let r1 : order40_D8 := DihedralGroup.r (1 : ZMod 4)
  let s0 : order40_D8 := DihedralGroup.sr (0 : ZMod 4)
  obtain ⟨u, hu⟩ := exists_unitAutHom_eq (p := 5) (φ r1)
  obtain ⟨v, hv⟩ := exists_unitAutHom_eq (p := 5) (φ s0)
  have hrel : s0 * r1 = r1⁻¹ * s0 := by
    simp [r1, s0, DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.inv_r]
  have himg : φ (s0 * r1) = φ (r1⁻¹ * s0) := congrArg φ hrel
  rw [map_mul, map_mul, map_inv, hu, hv] at himg
  have huv : v * u = u⁻¹ * v := by
    apply unitAutHom_injective (p := 5)
    simpa [map_mul, map_inv] using himg
  have hu_inv : u = u⁻¹ := by
    have := congrArg (fun x => x * v⁻¹) huv
    simpa [mul_assoc, mul_comm, mul_left_comm] using this
  rw [hu, ← map_pow]
  rw [← map_one (unitAutHom (p := 5))]
  apply congrArg (unitAutHom (p := 5))
  rw [pow_two]
  nth_rw 2 [hu_inv]
  exact mul_inv_cancel _

theorem order40_q8_action_a_sq (φ : order40_Q8 →* MulAut order40_C5) :
    φ (QuaternionGroup.a (1 : ZMod 4)) ^ 2 = 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let a1 : order40_Q8 := QuaternionGroup.a (1 : ZMod 4)
  let x0 : order40_Q8 := QuaternionGroup.xa (0 : ZMod 4)
  obtain ⟨u, hu⟩ := exists_unitAutHom_eq (p := 5) (φ a1)
  obtain ⟨v, hv⟩ := exists_unitAutHom_eq (p := 5) (φ x0)
  have hrel : x0 * a1 = a1⁻¹ * x0 := by decide
  have himg : φ (x0 * a1) = φ (a1⁻¹ * x0) := congrArg φ hrel
  rw [map_mul, map_mul, map_inv, hu, hv] at himg
  have huv : v * u = u⁻¹ * v := by
    apply unitAutHom_injective (p := 5)
    simpa [map_mul, map_inv] using himg
  have hu_inv : u = u⁻¹ := by
    have := congrArg (fun x => x * v⁻¹) huv
    simpa [mul_assoc, mul_comm, mul_left_comm] using this
  rw [hu, ← map_pow]
  rw [← map_one (unitAutHom (p := 5))]
  apply congrArg (unitAutHom (p := 5))
  rw [pow_two]
  nth_rw 2 [hu_inv]
  exact mul_inv_cancel _

theorem order40_q8_action_x_sq (φ : order40_Q8 →* MulAut order40_C5)
    (ha : φ (QuaternionGroup.a (1 : ZMod 4)) ^ 2 = 1) :
    φ (QuaternionGroup.xa (0 : ZMod 4)) ^ 2 = 1 := by
  let a1 : order40_Q8 := QuaternionGroup.a (1 : ZMod 4)
  let x0 : order40_Q8 := QuaternionGroup.xa (0 : ZMod 4)
  have hrel : x0 ^ 2 = a1 ^ 2 := by decide
  have himg : φ (x0 ^ 2) = φ (a1 ^ 2) := congrArg φ hrel
  rw [map_pow, map_pow] at himg
  change φ x0 ^ 2 = 1
  rw [himg]
  exact ha

theorem order40_c4c2_action_cases (φ : order40_C4C2 →* MulAut order40_C5) :
    φ = 1 ∨ φ = order40_action order40_chiC4C2_fst_two ∨
      φ = order40_action order40_chiC4C2_snd_two ∨
      φ = order40_action order40_chiC4C2_prod_two ∨
      φ = order40_action order40_chiC4C2_fst_four ∨
      φ = order40_action order40_chiC4C2_fst_four_snd ∨
      φ = order40_action order40_chiC4C2_fst_four_inv ∨
      φ = order40_action order40_chiC4C2_fst_four_inv_snd := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let g4 : order40_C4C2 := (Multiplicative.ofAdd (1 : ZMod 4), 1)
  let g2 : order40_C4C2 := (1, Multiplicative.ofAdd (1 : ZMod 2))
  obtain ⟨u, hu4⟩ := exists_unitAutHom_eq (p := 5) (φ g4)
  have hsq2 : (φ g2) ^ 2 = 1 := by
    rw [← map_pow, show g2 ^ 2 = 1 by decide, map_one]
  rcases order40_unit_cases u with h4 | h4 | h4 | h4 <;>
    rcases order40_mulAut_sq_eq_one_cases (φ g2) hsq2 with h2 | h2
  · left
    apply order40_c4c2_hom_ext <;>
      simp [g4, g2, hu4, h4, h2]
  · right
    right
    left
    apply order40_c4c2_hom_ext <;>
      simp [g4, g2, hu4, h4, h2]
  · right
    right
    right
    right
    left
    apply order40_c4c2_hom_ext <;>
      simp [g4, g2, hu4, h4, h2]
  · right
    right
    right
    right
    right
    left
    apply order40_c4c2_hom_ext <;>
      simp [g4, g2, hu4, h4, h2]
  · right
    left
    apply order40_c4c2_hom_ext <;>
      simp [g4, g2, hu4, h4, h2]
  · right
    right
    right
    left
    apply order40_c4c2_hom_ext <;>
      simp [g4, g2, hu4, h4, h2]
  · right
    right
    right
    right
    right
    right
    left
    apply order40_c4c2_hom_ext <;>
      simp [g4, g2, hu4, h4, h2]
  · right
    right
    right
    right
    right
    right
    right
    apply order40_c4c2_hom_ext <;>
      simp [g4, g2, hu4, h4, h2]

theorem order40_c2c2c2_action_cases (φ : order40_C2C2C2 →* MulAut order40_C5) :
    φ = 1 ∨ φ = order40_action order40_chiC2C2C2 ∨
      φ = order40_action order40_chiC2C2C2_snd ∨
      φ = order40_action order40_chiC2C2C2_trd ∨
      φ = order40_action order40_chiC2C2C2_fst_snd ∨
      φ = order40_action order40_chiC2C2C2_fst_trd ∨
      φ = order40_action order40_chiC2C2C2_snd_trd ∨
      φ = order40_action order40_chiC2C2C2_fst_snd_trd := by
  let g1 : order40_C2C2C2 := (Multiplicative.ofAdd (1 : ZMod 2), 1)
  let g2 : order40_C2C2C2 := (1, (Multiplicative.ofAdd (1 : ZMod 2), 1))
  let g3 : order40_C2C2C2 := (1, (1, Multiplicative.ofAdd (1 : ZMod 2)))
  have hsq1 : (φ g1) ^ 2 = 1 := by
    rw [← map_pow, show g1 ^ 2 = 1 by decide, map_one]
  have hsq2 : (φ g2) ^ 2 = 1 := by
    rw [← map_pow, show g2 ^ 2 = 1 by decide, map_one]
  have hsq3 : (φ g3) ^ 2 = 1 := by
    rw [← map_pow, show g3 ^ 2 = 1 by decide, map_one]
  rcases order40_mulAut_sq_eq_one_cases (φ g1) hsq1 with h1 | h1 <;>
    rcases order40_mulAut_sq_eq_one_cases (φ g2) hsq2 with h2 | h2 <;>
      rcases order40_mulAut_sq_eq_one_cases (φ g3) hsq3 with h3 | h3
  · left
    apply order40_c2c2c2_hom_ext <;>
      simp [g1, g2, g3, h1, h2, h3]
  · right
    right
    right
    left
    apply order40_c2c2c2_hom_ext <;>
      simp [g1, g2, g3, h1, h2, h3, order40_action, order40_chiC2C2C2_trd,
        order40_c2UnitHom]
  · right
    right
    left
    apply order40_c2c2c2_hom_ext <;>
      simp [g1, g2, g3, h1, h2, h3, order40_action, order40_chiC2C2C2_snd,
        order40_c2UnitHom]
  · right
    right
    right
    right
    right
    right
    left
    apply order40_c2c2c2_hom_ext <;>
      simp [g1, g2, g3, h1, h2, h3, order40_action, order40_chiC2C2C2_snd_trd,
        order40_c2UnitHom]
  · right
    left
    apply order40_c2c2c2_hom_ext <;>
      simp [g1, g2, g3, h1, h2, h3, order40_action, order40_chiC2C2C2,
        order40_c2UnitHom]
  · right
    right
    right
    right
    right
    left
    apply order40_c2c2c2_hom_ext <;>
      simp [g1, g2, g3, h1, h2, h3, order40_action, order40_chiC2C2C2_fst_trd,
        order40_c2UnitHom]
  · right
    right
    right
    right
    left
    apply order40_c2c2c2_hom_ext <;>
      simp [g1, g2, g3, h1, h2, h3, order40_action, order40_chiC2C2C2_fst_snd,
        order40_c2UnitHom]
  · right
    right
    right
    right
    right
    right
    right
    apply order40_c2c2c2_hom_ext <;>
      simp [g1, g2, g3, h1, h2, h3, order40_action,
        order40_chiC2C2C2_fst_snd_trd, order40_c2UnitHom]

theorem order40_d8_action_cases (φ : order40_D8 →* MulAut order40_C5) :
    φ = 1 ∨ φ = order40_action order40_chiD8_rot ∨
      φ = order40_action order40_chiD8_ref ∨
      φ = order40_action order40_chiD8_prod := by
  let r1 : order40_D8 := DihedralGroup.r (1 : ZMod 4)
  let s0 : order40_D8 := DihedralGroup.sr (0 : ZMod 4)
  have hsq_r : (φ r1) ^ 2 = 1 := by
    exact order40_d8_action_rot_sq φ
  have hsq_s : (φ s0) ^ 2 = 1 := by
    rw [← map_pow, show s0 ^ 2 = 1 by decide, map_one]
  rcases order40_mulAut_sq_eq_one_cases (φ r1) hsq_r with hr | hr <;>
    rcases order40_mulAut_sq_eq_one_cases (φ s0) hsq_s with hs | hs
  · left
    apply order40_d8_hom_ext <;>
      simp [r1, s0, hr, hs]
  · right
    right
    left
    apply order40_d8_hom_ext <;>
      simp [r1, s0, hr, hs]
  · right
    left
    apply order40_d8_hom_ext <;>
      simp [r1, s0, hr, hs]
  · right
    right
    right
    apply order40_d8_hom_ext <;>
      simp [r1, s0, hr, hs]

theorem order40_q8_action_cases (φ : order40_Q8 →* MulAut order40_C5) :
    φ = 1 ∨ φ = order40_action order40_chiQ8 ∨
      φ = order40_action order40_chiQ8_xa ∨
      φ = order40_action order40_chiQ8_prod := by
  let a1 : order40_Q8 := QuaternionGroup.a (1 : ZMod 4)
  let x0 : order40_Q8 := QuaternionGroup.xa (0 : ZMod 4)
  have hsq_a : (φ a1) ^ 2 = 1 := by
    exact order40_q8_action_a_sq φ
  have hsq_x : (φ x0) ^ 2 = 1 := by
    exact order40_q8_action_x_sq φ hsq_a
  rcases order40_mulAut_sq_eq_one_cases (φ a1) hsq_a with ha | ha <;>
    rcases order40_mulAut_sq_eq_one_cases (φ x0) hsq_x with hx | hx
  · left
    apply order40_q8_hom_ext <;>
      simp [a1, x0, ha, hx]
  · right
    right
    left
    apply order40_q8_hom_ext <;>
      simp [a1, x0, ha, hx]
  · right
    left
    apply order40_q8_hom_ext <;>
      simp [a1, x0, ha, hx]
  · right
    right
    right
    apply order40_q8_hom_ext <;>
      simp [a1, x0, ha, hx]

theorem order40_c8_action_semidirect_cases (φ : order40_C8 →* MulAut order40_C5) :
    Nonempty (SemidirectProduct order40_C5 order40_C8 φ ≃* order40_RA) ∨
      Nonempty (SemidirectProduct order40_C5 order40_C8 φ ≃* order40_RB) ∨
      Nonempty (SemidirectProduct order40_C5 order40_C8 φ ≃* order40_RC) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let g : order40_C8 := Multiplicative.ofAdd (1 : ZMod 8)
  obtain ⟨u, hu⟩ := exists_unitAutHom_eq (p := 5) (φ g)
  rcases order40_unit_cases u with h | h | h | h
  · left
    have hφ : φ = 1 := by
      apply order40_c8_action_hom_ext
      rw [hu, h]
      exact map_one (unitAutHom (p := 5))
    exact ⟨(semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd⟩
  · right
    right
    have hφ : φ = order40_action order40_chiC8_four := by
      apply order40_c8_action_hom_ext
      rw [hu, h]
      change unitAutHom order40_u4 =
        unitAutHom (order40_chiC8_four (Multiplicative.ofAdd (1 : ZMod 8)))
      rw [order40_chiC8_four_gen]
    exact ⟨semidirectProductCongr_eq hφ⟩
  · right
    left
    have hφ : φ = order40_action order40_chiC8_two := by
      apply order40_c8_action_hom_ext
      rw [hu, h]
      change unitAutHom (order40_u4 ^ 2) =
        unitAutHom (order40_chiC8_two (Multiplicative.ofAdd (1 : ZMod 8)))
      rw [order40_chiC8_two_gen]
    exact ⟨semidirectProductCongr_eq hφ⟩
  · right
    right
    have hφ : φ = order40_action order40_chiC8_four_inv := by
      apply order40_c8_action_hom_ext
      rw [hu, h]
      change unitAutHom (order40_u4 ^ 3) =
        unitAutHom (order40_chiC8_four_inv (Multiplicative.ofAdd (1 : ZMod 8)))
      rw [order40_chiC8_four_inv_gen]
    exact ⟨(semidirectProductCongr_eq hφ).trans order40_c8_four_inv_equiv_four⟩

theorem order40_c4c2_action_semidirect_cases
    (φ : order40_C4C2 →* MulAut order40_C5) :
    Nonempty (SemidirectProduct order40_C5 order40_C4C2 φ ≃* order40_RD) ∨
      Nonempty (SemidirectProduct order40_C5 order40_C4C2 φ ≃* order40_RE) ∨
      Nonempty (SemidirectProduct order40_C5 order40_C4C2 φ ≃* order40_RF) ∨
      Nonempty (SemidirectProduct order40_C5 order40_C4C2 φ ≃* order40_RG) := by
  rcases order40_c4c2_action_cases φ with
    hφ | hφ | hφ | hφ | hφ | hφ | hφ | hφ
  · left
    exact ⟨(semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd⟩
  · right
    left
    exact ⟨semidirectProductCongr_eq hφ⟩
  · right
    right
    left
    exact ⟨semidirectProductCongr_eq hφ⟩
  · right
    right
    left
    exact ⟨(semidirectProductCongr_eq hφ).trans order40_c4c2_prod_two_equiv_snd⟩
  · right
    right
    right
    exact ⟨semidirectProductCongr_eq hφ⟩
  · right
    right
    right
    exact ⟨(semidirectProductCongr_eq hφ).trans order40_c4c2_fst_four_snd_equiv_four⟩
  · right
    right
    right
    exact ⟨(semidirectProductCongr_eq hφ).trans order40_c4c2_fst_four_inv_equiv_four⟩
  · right
    right
    right
    exact ⟨(semidirectProductCongr_eq hφ).trans
      order40_c4c2_fst_four_inv_snd_equiv_four⟩

theorem order40_c2c2c2_action_semidirect_cases
    (φ : order40_C2C2C2 →* MulAut order40_C5) :
    Nonempty (SemidirectProduct order40_C5 order40_C2C2C2 φ ≃* order40_RH) ∨
      Nonempty (SemidirectProduct order40_C5 order40_C2C2C2 φ ≃* order40_RI) := by
  rcases order40_c2c2c2_action_cases φ with
    hφ | hφ | hφ | hφ | hφ | hφ | hφ | hφ
  · left
    exact ⟨(semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd⟩
  · right
    exact ⟨semidirectProductCongr_eq hφ⟩
  · right
    exact ⟨(semidirectProductCongr_eq hφ).trans order40_c2c2c2_snd_equiv⟩
  · right
    exact ⟨(semidirectProductCongr_eq hφ).trans order40_c2c2c2_trd_equiv⟩
  · right
    exact ⟨(semidirectProductCongr_eq hφ).trans order40_c2c2c2_fst_snd_equiv⟩
  · right
    exact ⟨(semidirectProductCongr_eq hφ).trans order40_c2c2c2_fst_trd_equiv⟩
  · right
    exact ⟨(semidirectProductCongr_eq hφ).trans order40_c2c2c2_snd_trd_equiv⟩
  · right
    exact ⟨(semidirectProductCongr_eq hφ).trans order40_c2c2c2_fst_snd_trd_equiv⟩

theorem order40_d8_action_semidirect_cases
    (φ : order40_D8 →* MulAut order40_C5) :
    Nonempty (SemidirectProduct order40_C5 order40_D8 φ ≃* order40_RJ) ∨
      Nonempty (SemidirectProduct order40_C5 order40_D8 φ ≃* order40_RK) ∨
      Nonempty (SemidirectProduct order40_C5 order40_D8 φ ≃* order40_RL) := by
  rcases order40_d8_action_cases φ with hφ | hφ | hφ | hφ
  · left
    exact ⟨(semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd⟩
  · right
    left
    exact ⟨semidirectProductCongr_eq hφ⟩
  · right
    right
    exact ⟨semidirectProductCongr_eq hφ⟩
  · right
    left
    exact ⟨(semidirectProductCongr_eq hφ).trans order40_d8_prod_equiv_rot⟩

theorem order40_q8_action_semidirect_cases
    (φ : order40_Q8 →* MulAut order40_C5) :
    Nonempty (SemidirectProduct order40_C5 order40_Q8 φ ≃* order40_RM) ∨
      Nonempty (SemidirectProduct order40_C5 order40_Q8 φ ≃* order40_RN) := by
  rcases order40_q8_action_cases φ with hφ | hφ | hφ | hφ
  · left
    exact ⟨(semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd⟩
  · right
    exact ⟨semidirectProductCongr_eq hφ⟩
  · right
    exact ⟨(semidirectProductCongr_eq hφ).trans order40_q8_xa_equiv_q8⟩
  · right
    exact ⟨(semidirectProductCongr_eq hφ).trans order40_q8_prod_equiv_q8⟩

/-! ### Exhaustiveness -/

/-- The fourteen representative cases for groups of order `40`. -/
abbrev order40RepCases (G : Type*) [Group G] : Prop :=
  Nonempty (G ≃* order40_RA) ∨ Nonempty (G ≃* order40_RB) ∨
    Nonempty (G ≃* order40_RC) ∨ Nonempty (G ≃* order40_RD) ∨
    Nonempty (G ≃* order40_RE) ∨ Nonempty (G ≃* order40_RF) ∨
    Nonempty (G ≃* order40_RG) ∨ Nonempty (G ≃* order40_RH) ∨
    Nonempty (G ≃* order40_RI) ∨ Nonempty (G ≃* order40_RJ) ∨
    Nonempty (G ≃* order40_RK) ∨ Nonempty (G ≃* order40_RL) ∨
    Nonempty (G ≃* order40_RM) ∨ Nonempty (G ≃* order40_RN)

private theorem order40RepCases_ra {G : Type*} [Group G] (h : Nonempty (G ≃* order40_RA)) :
    order40RepCases G := by
  left
  exact h

private theorem order40RepCases_rb {G : Type*} [Group G] (h : Nonempty (G ≃* order40_RB)) :
    order40RepCases G := by
  right
  left
  exact h

private theorem order40RepCases_rc {G : Type*} [Group G] (h : Nonempty (G ≃* order40_RC)) :
    order40RepCases G := by
  right
  right
  left
  exact h

private theorem order40RepCases_rd {G : Type*} [Group G] (h : Nonempty (G ≃* order40_RD)) :
    order40RepCases G := by
  right
  right
  right
  left
  exact h

private theorem order40RepCases_re {G : Type*} [Group G] (h : Nonempty (G ≃* order40_RE)) :
    order40RepCases G := by
  right
  right
  right
  right
  left
  exact h

private theorem order40RepCases_rf {G : Type*} [Group G] (h : Nonempty (G ≃* order40_RF)) :
    order40RepCases G := by
  right
  right
  right
  right
  right
  left
  exact h

private theorem order40RepCases_rg {G : Type*} [Group G] (h : Nonempty (G ≃* order40_RG)) :
    order40RepCases G := by
  right
  right
  right
  right
  right
  right
  left
  exact h

private theorem order40RepCases_rh {G : Type*} [Group G] (h : Nonempty (G ≃* order40_RH)) :
    order40RepCases G := by
  right
  right
  right
  right
  right
  right
  right
  left
  exact h

private theorem order40RepCases_ri {G : Type*} [Group G] (h : Nonempty (G ≃* order40_RI)) :
    order40RepCases G := by
  right
  right
  right
  right
  right
  right
  right
  right
  left
  exact h

private theorem order40RepCases_rj {G : Type*} [Group G] (h : Nonempty (G ≃* order40_RJ)) :
    order40RepCases G := by
  right
  right
  right
  right
  right
  right
  right
  right
  right
  left
  exact h

private theorem order40RepCases_rk {G : Type*} [Group G] (h : Nonempty (G ≃* order40_RK)) :
    order40RepCases G := by
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  left
  exact h

private theorem order40RepCases_rl {G : Type*} [Group G] (h : Nonempty (G ≃* order40_RL)) :
    order40RepCases G := by
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  left
  exact h

private theorem order40RepCases_rm {G : Type*} [Group G] (h : Nonempty (G ≃* order40_RM)) :
    order40RepCases G := by
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  left
  exact h

private theorem order40RepCases_rn {G : Type*} [Group G] (h : Nonempty (G ≃* order40_RN)) :
    order40RepCases G := by
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  exact h

private theorem order40_classification_of_c8_action {G : Type*} [Group G]
    {φ : order40_C8 →* MulAut order40_C5}
    (e : G ≃* SemidirectProduct order40_C5 order40_C8 φ) :
    order40RepCases G := by
  rcases order40_c8_action_semidirect_cases φ with h | h | h
  · obtain ⟨eh⟩ := h
    exact order40RepCases_ra ⟨e.trans eh⟩
  · obtain ⟨eh⟩ := h
    exact order40RepCases_rb ⟨e.trans eh⟩
  · obtain ⟨eh⟩ := h
    exact order40RepCases_rc ⟨e.trans eh⟩

private theorem order40_classification_of_c4c2_action {G : Type*} [Group G]
    {φ : order40_C4C2 →* MulAut order40_C5}
    (e : G ≃* SemidirectProduct order40_C5 order40_C4C2 φ) :
    order40RepCases G := by
  rcases order40_c4c2_action_semidirect_cases φ with h | h | h | h
  · obtain ⟨eh⟩ := h
    exact order40RepCases_rd ⟨e.trans eh⟩
  · obtain ⟨eh⟩ := h
    exact order40RepCases_re ⟨e.trans eh⟩
  · obtain ⟨eh⟩ := h
    exact order40RepCases_rf ⟨e.trans eh⟩
  · obtain ⟨eh⟩ := h
    exact order40RepCases_rg ⟨e.trans eh⟩

private theorem order40_classification_of_c2c2c2_action {G : Type*} [Group G]
    {φ : order40_C2C2C2 →* MulAut order40_C5}
    (e : G ≃* SemidirectProduct order40_C5 order40_C2C2C2 φ) :
    order40RepCases G := by
  rcases order40_c2c2c2_action_semidirect_cases φ with h | h
  · obtain ⟨eh⟩ := h
    exact order40RepCases_rh ⟨e.trans eh⟩
  · obtain ⟨eh⟩ := h
    exact order40RepCases_ri ⟨e.trans eh⟩

private theorem order40_classification_of_d8_action {G : Type*} [Group G]
    {φ : order40_D8 →* MulAut order40_C5}
    (e : G ≃* SemidirectProduct order40_C5 order40_D8 φ) :
    order40RepCases G := by
  rcases order40_d8_action_semidirect_cases φ with h | h | h
  · obtain ⟨eh⟩ := h
    exact order40RepCases_rj ⟨e.trans eh⟩
  · obtain ⟨eh⟩ := h
    exact order40RepCases_rk ⟨e.trans eh⟩
  · obtain ⟨eh⟩ := h
    exact order40RepCases_rl ⟨e.trans eh⟩

private theorem order40_classification_of_q8_action {G : Type*} [Group G]
    {φ : order40_Q8 →* MulAut order40_C5}
    (e : G ≃* SemidirectProduct order40_C5 order40_Q8 φ) :
    order40RepCases G := by
  rcases order40_q8_action_semidirect_cases φ with h | h
  · obtain ⟨eh⟩ := h
    exact order40RepCases_rm ⟨e.trans eh⟩
  · obtain ⟨eh⟩ := h
    exact order40RepCases_rn ⟨e.trans eh⟩

/-- Every group of order `40` is isomorphic to one of the fourteen displayed representatives. -/
theorem order40_classification [Finite G] (hG : Nat.card G = 40) :
    order40RepCases G := by
  obtain ⟨N, H, φ, _, hcardN, hcardH, ⟨e⟩⟩ := order40_semidirectProduct hG
  obtain ⟨eN⟩ := prime_classification (by norm_num : Nat.Prime 5) hcardN
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Fintype H := Fintype.ofFinite H
  rcases P3Group.classification 2 H (hcardH.trans (by norm_num)) with
    hH | hH | hH | hH | hH | hH | hH
  · change Nonempty (H ≃* order40_C8) at hH
    obtain ⟨eH⟩ := hH
    exact order40_classification_of_c8_action (e.trans (SemidirectProduct.congr' eN eH))
  · change Nonempty (H ≃* order40_C4C2) at hH
    obtain ⟨eH⟩ := hH
    exact order40_classification_of_c4c2_action (e.trans (SemidirectProduct.congr' eN eH))
  · change Nonempty (H ≃* order40_C2C2C2) at hH
    obtain ⟨eH⟩ := hH
    exact order40_classification_of_c2c2c2_action (e.trans (SemidirectProduct.congr' eN eH))
  · exact (hH.1 rfl).elim
  · exact (hH.1 rfl).elim
  · obtain ⟨eH⟩ := hH.2
    exact order40_classification_of_d8_action (e.trans (SemidirectProduct.congr' eN eH))
  · obtain ⟨eH⟩ := hH.2
    exact order40_classification_of_q8_action (e.trans (SemidirectProduct.congr' eN eH))

/-- The fourteen displayed representatives, indexed for the counting framework. -/
noncomputable abbrev order40_reps : Fin 14 → Type
  | 0 => order40_RA
  | 1 => order40_RB
  | 2 => order40_RC
  | 3 => order40_RD
  | 4 => order40_RE
  | 5 => order40_RF
  | 6 => order40_RG
  | 7 => order40_RH
  | 8 => order40_RI
  | 9 => order40_RJ
  | 10 => order40_RK
  | 11 => order40_RL
  | 12 => order40_RM
  | 13 => order40_RN

noncomputable instance instGroupOrder40Reps : ∀ i, Group (order40_reps i)
  | 0 => inferInstanceAs (Group order40_RA)
  | 1 => inferInstanceAs (Group order40_RB)
  | 2 => inferInstanceAs (Group order40_RC)
  | 3 => inferInstanceAs (Group order40_RD)
  | 4 => inferInstanceAs (Group order40_RE)
  | 5 => inferInstanceAs (Group order40_RF)
  | 6 => inferInstanceAs (Group order40_RG)
  | 7 => inferInstanceAs (Group order40_RH)
  | 8 => inferInstanceAs (Group order40_RI)
  | 9 => inferInstanceAs (Group order40_RJ)
  | 10 => inferInstanceAs (Group order40_RK)
  | 11 => inferInstanceAs (Group order40_RL)
  | 12 => inferInstanceAs (Group order40_RM)
  | 13 => inferInstanceAs (Group order40_RN)

/-! ### Cardinalities of the representatives -/

theorem card_order40_C5 : Nat.card order40_C5 = 5 := card_cyclicRep (by norm_num)

theorem card_order40_C8 : Nat.card order40_C8 = 8 := card_cyclicRep (by norm_num)

theorem card_order40_C4C2 : Nat.card order40_C4C2 = 8 := by
  rw [Nat.card_prod]
  norm_num [card_cyclicRep (by norm_num : 4 ≠ 0), card_cyclicRep (by norm_num : 2 ≠ 0)]

theorem card_order40_C2C2C2 : Nat.card order40_C2C2C2 = 8 := by
  rw [Nat.card_prod, Nat.card_prod]
  norm_num [card_cyclicRep (by norm_num : 2 ≠ 0)]

theorem card_order40_D8 : Nat.card order40_D8 = 8 := by
  rw [DihedralGroup.nat_card]

theorem card_order40_Q8 : Nat.card order40_Q8 = 8 := by
  simpa [order40_Q8] using P3Group.card_quaternion8

theorem card_order40_DP {H : Type} [Group H] (hH : Nat.card H = 8) :
    Nat.card (order40_DP H) = 40 := by
  rw [order40_DP, Nat.card_prod, card_order40_C5, hH]

theorem card_order40_SD {H : Type} [Group H] (χ : H →* (ZMod 5)ˣ)
    (hH : Nat.card H = 8) : Nat.card (order40_SD H χ) = 40 := by
  rw [order40_SD, SemidirectProduct.card, card_order40_C5, hH]

theorem card_order40_RA : Nat.card order40_RA = 40 := card_order40_DP card_order40_C8
theorem card_order40_RB : Nat.card order40_RB = 40 :=
  card_order40_SD order40_chiC8_two card_order40_C8
theorem card_order40_RC : Nat.card order40_RC = 40 :=
  card_order40_SD order40_chiC8_four card_order40_C8
theorem card_order40_RD : Nat.card order40_RD = 40 := card_order40_DP card_order40_C4C2
theorem card_order40_RE : Nat.card order40_RE = 40 :=
  card_order40_SD order40_chiC4C2_fst_two card_order40_C4C2
theorem card_order40_RF : Nat.card order40_RF = 40 :=
  card_order40_SD order40_chiC4C2_snd_two card_order40_C4C2
theorem card_order40_RG : Nat.card order40_RG = 40 :=
  card_order40_SD order40_chiC4C2_fst_four card_order40_C4C2
theorem card_order40_RH : Nat.card order40_RH = 40 := card_order40_DP card_order40_C2C2C2
theorem card_order40_RI : Nat.card order40_RI = 40 :=
  card_order40_SD order40_chiC2C2C2 card_order40_C2C2C2
theorem card_order40_RJ : Nat.card order40_RJ = 40 := card_order40_DP card_order40_D8
theorem card_order40_RK : Nat.card order40_RK = 40 :=
  card_order40_SD order40_chiD8_rot card_order40_D8
theorem card_order40_RL : Nat.card order40_RL = 40 :=
  card_order40_SD order40_chiD8_ref card_order40_D8
theorem card_order40_RM : Nat.card order40_RM = 40 := card_order40_DP card_order40_Q8
theorem card_order40_RN : Nat.card order40_RN = 40 :=
  card_order40_SD order40_chiQ8 card_order40_Q8

theorem card_order40_reps (i : Fin 14) : Nat.card (order40_reps i) = 40 := by
  fin_cases i
  · exact card_order40_RA
  · exact card_order40_RB
  · exact card_order40_RC
  · exact card_order40_RD
  · exact card_order40_RE
  · exact card_order40_RF
  · exact card_order40_RG
  · exact card_order40_RH
  · exact card_order40_RI
  · exact card_order40_RJ
  · exact card_order40_RK
  · exact card_order40_RL
  · exact card_order40_RM
  · exact card_order40_RN

/-- The displayed representatives exhaust the groups of order `40`, in `IsClassif` form. -/
theorem order40_complete (G : Type) [Group G] (hG : Nat.card G = 40) :
    ∃ i, Nonempty (G ≃* order40_reps i) := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  rcases order40_classification (G := G) hG with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h
  exacts [⟨0, by simpa [order40_reps] using h⟩,
    ⟨1, by simpa [order40_reps] using h⟩,
    ⟨2, by simpa [order40_reps] using h⟩,
    ⟨3, by simpa [order40_reps] using h⟩,
    ⟨4, by simpa [order40_reps] using h⟩,
    ⟨5, by simpa [order40_reps] using h⟩,
    ⟨6, by simpa [order40_reps] using h⟩,
    ⟨7, by simpa [order40_reps] using h⟩,
    ⟨8, by simpa [order40_reps] using h⟩,
    ⟨9, by simpa [order40_reps] using h⟩,
    ⟨10, by simpa [order40_reps] using h⟩,
    ⟨11, by simpa [order40_reps] using h⟩,
    ⟨12, by simpa [order40_reps] using h⟩,
    ⟨13, by simpa [order40_reps] using h⟩]

end Smallgroups.UsefulTheorems
