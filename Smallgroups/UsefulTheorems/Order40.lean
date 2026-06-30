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

noncomputable abbrev order40_chiQ8 : order40_Q8 →* (ZMod 5)ˣ :=
  order40_c2UnitHom.comp order88_chiQ8

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

end Smallgroups.UsefulTheorems
