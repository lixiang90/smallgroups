/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order56

/-!
# First structural reductions for groups of order 24

This file starts the classification of groups of order `24 = 3 * 8`.

The completed part is the normal Sylow-`3` branch.  If the Sylow `3`-subgroup is
normal, Schur--Zassenhaus writes the group as `C₃ ⋊ H`, where `|H| = 8`.  Since
`Aut(C₃) ≃ C₂`, actions are classified by characters `H → C₂`.  The character
orbit calculations already used for order `56` give twelve representatives.
-/

namespace Smallgroups.UsefulTheorems

open Sylow
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ### Basic Sylow facts -/

/-- In a group of order `24`, the number of Sylow `3`-subgroups is `1` or `4`. -/
theorem card_sylow_3_of_card_24_eq_one_or_four [Finite G] (hG : Nat.card G = 24) :
    Nat.card (Sylow 3 G) = 1 ∨ Nat.card (Sylow 3 G) = 4 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 3 G))
  have hdvd24 : Nat.card (Sylow 3 G) ∣ 24 := by
    rw [← hG]
    exact P0.card_dvd_index.trans (Subgroup.index_dvd_card _)
  have hdvd8_mul : Nat.card (Sylow 3 G) ∣ 8 * 3 := by
    simpa using hdvd24
  have hndvd_3 : ¬ 3 ∣ Nat.card (Sylow 3 G) := not_dvd_card_sylow 3 G
  have hcop : Nat.Coprime (Nat.card (Sylow 3 G)) 3 :=
    ((show Nat.Prime 3 by norm_num).coprime_iff_not_dvd.mpr hndvd_3).symm
  have hdvd8 : Nat.card (Sylow 3 G) ∣ 8 := hcop.dvd_of_dvd_mul_right hdvd8_mul
  have hmod := card_sylow_modEq_one 3 G
  have hle : Nat.card (Sylow 3 G) ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd8
  have hpos : 0 < Nat.card (Sylow 3 G) := Nat.card_pos
  interval_cases h : Nat.card (Sylow 3 G)
  · exact Or.inl rfl
  · unfold Nat.ModEq at hmod; norm_num at hmod
  · norm_num at hdvd8
  · exact Or.inr rfl
  · norm_num at hdvd8
  · norm_num at hdvd8
  · norm_num at hdvd8
  · unfold Nat.ModEq at hmod; norm_num at hmod

/-- If there is a unique Sylow `3`-subgroup, it is normal. -/
theorem sylow_3_normal_of_card_24_of_card_sylow_eq_one [Finite G]
    (hSyl : Nat.card (Sylow 3 G) = 1) (P : Sylow 3 G) :
    (↑P : Subgroup G).Normal := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Subsingleton (Sylow 3 G) := (Nat.card_eq_one_iff_unique.mp hSyl).1
  exact normal_of_subsingleton P

/-- A Sylow `3`-subgroup of a group of order `24` has order `3`. -/
theorem card_sylow_3_subgroup_of_card_24 [Finite G] (hG : Nat.card G = 24)
    (P : Sylow 3 G) : Nat.card (↑P : Subgroup G) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hndvd : ¬ 3 ∣ 8 := by norm_num
  have hfact : (24 : ℕ).factorization 3 = 1 := by
    rw [show 24 = 8 * 3 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hndvd,
      Nat.Prime.factorization_self (by norm_num : Nat.Prime 3), zero_add]
  rw [Sylow.card_eq_multiplicity, hG, hfact, pow_one]

/-- **Schur--Zassenhaus reduction for the normal Sylow-`3` branch of order `24`.** -/
theorem order24_semidirectProduct_of_card_sylow_3_eq_one [Finite G] (hG : Nat.card G = 24)
    (hSyl : Nat.card (Sylow 3 G) = 1) :
    ∃ (N H : Subgroup G) (φ : H →* MulAut N),
      N.Normal ∧ Nat.card N = 3 ∧ Nat.card H = 8 ∧
        Nonempty (G ≃* SemidirectProduct N H φ) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 3 G))
  haveI hnorm : (↑P0 : Subgroup G).Normal :=
    sylow_3_normal_of_card_24_of_card_sylow_eq_one hSyl P0
  have hcardN : Nat.card (↑P0 : Subgroup G) = 3 :=
    card_sylow_3_subgroup_of_card_24 hG P0
  haveI : (↑P0 : Subgroup G).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
  have hcop : Nat.Coprime (Nat.card (↑P0 : Subgroup G)) (↑P0 : Subgroup G).index := by
    rw [hcardN]
    have := P0.not_dvd_index
    exact (show Nat.Prime 3 by norm_num).coprime_iff_not_dvd.mpr this
  obtain ⟨H, φ, ⟨e⟩⟩ := schurZassenhaus_semidirectProduct (↑P0 : Subgroup G) hcop
  have hcardH : Nat.card H = 8 := by
    have h1 : Nat.card G = Nat.card (↑P0 : Subgroup G) * Nat.card H := by
      rw [Nat.card_congr e.toEquiv, Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
    rw [hG, hcardN] at h1
    have h1' : 3 * Nat.card H = 3 * 8 := by omega
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3) h1'
  exact ⟨↑P0, H, φ, hnorm, hcardN, hcardH, ⟨e⟩⟩

/-! ### Representatives for the normal Sylow-`3` branch -/

/-- The cyclic group `C₃`. -/
abbrev order24_C3 : Type := CyclicRep 3

abbrev order24_C8 : Type := order56_C8
abbrev order24_C4C2 : Type := order56_C4C2
abbrev order24_C2C2C2 : Type := order56_C2C2C2
abbrev order24_D8 : Type := order56_D8
abbrev order24_Q8 : Type := order56_Q8

/-- Multiplication by `-1` on `C₃` is inversion. -/
theorem order24_unitAutHom_neg_one :
    unitAutHom (-1 : (ZMod 3)ˣ) = invAut order24_C3 := by
  ext x
  obtain ⟨m, rfl⟩ := Multiplicative.ofAdd.surjective x
  rw [unitAutHom_apply, invAut_apply]
  simp

/-- A unit of `ZMod 3` whose eighth power is `1` is `1` or `-1`. -/
theorem order24_unit_pow8_eq_one (u : (ZMod 3)ˣ) (hu : u ^ 8 = 1) :
    u = 1 ∨ u = -1 := by
  decide +revert

/-- Any automorphism of `C₃` whose eighth power is `1` is trivial or inversion. -/
theorem order24_mulAut_pow8_eq_one_or_inv (α : MulAut order24_C3) (hα : α ^ 8 = 1) :
    α = 1 ∨ α = invAut order24_C3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨u, hu⟩ := exists_unitAutHom_eq (p := 3) α
  have hu8 : u ^ 8 = 1 := by
    apply unitAutHom_injective (p := 3)
    rw [map_pow, ← hu, hα, map_one]
  rcases order24_unit_pow8_eq_one u hu8 with h1 | hneg
  · left
    rw [hu, h1, map_one]
  · right
    rw [hu, hneg, order24_unitAutHom_neg_one]

/-- If `H` has order `8`, every value of an action `H → Aut(C₃)` is trivial or inversion. -/
theorem order24_action_value_eq_one_or_inv {H : Type} [Group H] [Finite H]
    (hH : Nat.card H = 8) (φ : H →* MulAut order24_C3) (h : H) :
    φ h = 1 ∨ φ h = invAut order24_C3 := by
  apply order24_mulAut_pow8_eq_one_or_inv
  have hh8 : h ^ 8 = 1 := by
    simpa [hH] using (pow_card_eq_one' (x := h))
  rw [← map_pow, hh8, map_one]

/-- Inversion is not the identity automorphism of `C₃`. -/
theorem order24_invAut_ne_one : invAut order24_C3 ≠ 1 := by
  haveI : Fact (1 < 3) := ⟨by norm_num⟩
  intro h
  have hx := congrArg
    (fun f : MulAut order24_C3 => f (Multiplicative.ofAdd (1 : ZMod 3))) h
  have hx' : (Multiplicative.ofAdd (1 : ZMod 3))⁻¹ =
      Multiplicative.ofAdd (1 : ZMod 3) := by
    simpa [invAut_apply] using hx
  clear hx
  have hxadd : (-1 : ZMod 3) = 1 := by
    simpa using congrArg Multiplicative.toAdd hx'
  have hv := congrArg ZMod.val hxadd
  rw [ZMod.val_one] at hv
  norm_num at hv

/-- The character `H → C₂` attached to an order-`24` action `H → Aut(C₃)`. -/
noncomputable def order24_actionCharacter {H : Type} [Group H] [Finite H]
    (hH : Nat.card H = 8) (φ : H →* MulAut order24_C3) :
    H →* Multiplicative (ZMod 2) where
  toFun h := by
    classical
    exact if φ h = 1 then 1 else Multiplicative.ofAdd (1 : ZMod 2)
  map_one' := by
    classical
    simp
  map_mul' := by
    classical
    intro a b
    rcases order24_action_value_eq_one_or_inv hH φ a with ha | ha <;>
      rcases order24_action_value_eq_one_or_inv hH φ b with hb | hb
    · have hab : φ (a * b) = 1 := by rw [map_mul, ha, hb, mul_one]
      simp [hab, ha, hb]
    · have hab : φ (a * b) = invAut order24_C3 := by rw [map_mul, ha, hb, one_mul]
      simp [hab, ha, hb, order24_invAut_ne_one]
    · have hab : φ (a * b) = invAut order24_C3 := by rw [map_mul, ha, hb, mul_one]
      simp [hab, ha, hb, order24_invAut_ne_one]
    · have hab : φ (a * b) = 1 := by
        rw [map_mul, ha, hb, ← sq, invAut_sq]
      simp only [hab, ha, hb, order24_invAut_ne_one, if_true, if_false]
      decide

/-- Turn a character `H → C₂` into the corresponding inversion action on `C₃`. -/
noncomputable abbrev order24_action {H : Type} [Group H]
    (χ : H →* Multiplicative (ZMod 2)) : H →* MulAut order24_C3 :=
  (invActionHom order24_C3).comp χ

/-- Precomposing a character by an automorphism precomposes the corresponding action. -/
theorem order24_action_comp {H : Type} [Group H] {χ ψ : H →* Multiplicative (ZMod 2)}
    (σ : H ≃* H) (hχ : χ.comp σ.toMonoidHom = ψ) :
    (order24_action χ).comp σ.toMonoidHom = order24_action ψ := by
  ext h x
  change (invActionHom order24_C3) (χ (σ h)) x = (invActionHom order24_C3) (ψ h) x
  rw [show χ (σ h) = ψ h from congrArg (fun f : H →* Multiplicative (ZMod 2) => f h) hχ]

/-- Every action `H → Aut(C₃)` with `|H| = 8` is induced by its character `H → C₂`. -/
theorem order24_action_eq_actionCharacter {H : Type} [Group H] [Finite H]
    (hH : Nat.card H = 8) (φ : H →* MulAut order24_C3) :
    φ = order24_action (order24_actionCharacter hH φ) := by
  ext h x
  rcases order24_action_value_eq_one_or_inv hH φ h with hh | hh
  · have hchi : order24_actionCharacter hH φ h = 1 := by
      classical
      simp [order24_actionCharacter, hh]
    simp [order24_action, hchi, hh]
  · have hchi : order24_actionCharacter hH φ h = Multiplicative.ofAdd (1 : ZMod 2) := by
      classical
      simp [order24_actionCharacter, hh, order24_invAut_ne_one]
    simp [order24_action, hchi, hh, invActionHom_gen]

theorem order24_c8_action_cases (φ : order24_C8 →* MulAut order24_C3) :
    φ = 1 ∨ φ = order24_action order88_chiC8 := by
  have hcard : Nat.card order24_C8 = 8 := card_cyclicRep (by norm_num)
  have hφ := order24_action_eq_actionCharacter hcard φ
  rcases order88_c8_character_cases (order24_actionCharacter hcard φ) with hχ | hχ
  · left
    rw [hφ, hχ]
    rfl
  · right
    rw [hφ, hχ]

theorem order24_c4c2_action_cases (φ : order24_C4C2 →* MulAut order24_C3) :
    φ = 1 ∨ φ = order24_action order88_chiC4C2_fst ∨
      φ = order24_action order88_chiC4C2_snd ∨
      φ = order24_action order88_chiC4C2_prod := by
  have hcard : Nat.card order24_C4C2 = 8 := by
    rw [Nat.card_prod, card_cyclicRep (by norm_num : 4 ≠ 0),
      card_cyclicRep (by norm_num : 2 ≠ 0)]
  have hφ := order24_action_eq_actionCharacter hcard φ
  rcases order88_c4c2_character_cases (order24_actionCharacter hcard φ) with
    hχ | hχ | hχ | hχ
  · left
    rw [hφ, hχ]
    rfl
  · right; left
    rw [hφ, hχ]
  · right; right; left
    rw [hφ, hχ]
  · right; right; right
    rw [hφ, hχ]

theorem order24_c2c2c2_action_cases (φ : order24_C2C2C2 →* MulAut order24_C3) :
    φ = 1 ∨ φ = order24_action order88_chiC2C2C2 ∨
      φ = order24_action order88_chiC2C2C2_snd ∨
      φ = order24_action order88_chiC2C2C2_trd ∨
      φ = order24_action order88_chiC2C2C2_fst_snd ∨
      φ = order24_action order88_chiC2C2C2_fst_trd ∨
      φ = order24_action order88_chiC2C2C2_snd_trd ∨
      φ = order24_action order88_chiC2C2C2_fst_snd_trd := by
  have hcard : Nat.card order24_C2C2C2 = 8 := by
    rw [Nat.card_prod, Nat.card_prod]
    norm_num [card_cyclicRep (by norm_num : 2 ≠ 0)]
  have hφ := order24_action_eq_actionCharacter hcard φ
  rcases order88_c2c2c2_character_cases (order24_actionCharacter hcard φ) with
    hχ | hχ | hχ | hχ | hχ | hχ | hχ | hχ
  · left
    rw [hφ, hχ]
    rfl
  · right; left
    rw [hφ, hχ]
  · right; right; left
    rw [hφ, hχ]
  · right; right; right; left
    rw [hφ, hχ]
  · right; right; right; right; left
    rw [hφ, hχ]
  · right; right; right; right; right; left
    rw [hφ, hχ]
  · right; right; right; right; right; right; left
    rw [hφ, hχ]
  · right; right; right; right; right; right; right
    rw [hφ, hχ]

theorem order24_d8_action_cases (φ : order24_D8 →* MulAut order24_C3) :
    φ = 1 ∨ φ = order24_action order88_chiD8_rot ∨
      φ = order24_action order88_chiD8_ref ∨
      φ = order24_action order88_chiD8_prod := by
  have hcard : Nat.card order24_D8 = 8 := by rw [DihedralGroup.nat_card]
  have hφ := order24_action_eq_actionCharacter hcard φ
  rcases order88_d8_character_cases (order24_actionCharacter hcard φ) with hχ | hχ | hχ | hχ
  · left
    rw [hφ, hχ]
    rfl
  · right; left
    rw [hφ, hχ]
  · right; right; left
    rw [hφ, hχ]
  · right; right; right
    rw [hφ, hχ]

theorem order24_q8_action_cases (φ : order24_Q8 →* MulAut order24_C3) :
    φ = 1 ∨ φ = order24_action order88_chiQ8 ∨
      φ = order24_action order88_chiQ8_xa ∨
      φ = order24_action order88_chiQ8_prod := by
  have hcard : Nat.card order24_Q8 = 8 := by
    rw [P3Group.card_quaternion8]
    norm_num
  have hφ := order24_action_eq_actionCharacter hcard φ
  rcases order88_q8_character_cases (order24_actionCharacter hcard φ) with hχ | hχ | hχ | hχ
  · left
    rw [hφ, hχ]
    rfl
  · right; left
    rw [hφ, hχ]
  · right; right; left
    rw [hφ, hχ]
  · right; right; right
    rw [hφ, hχ]

/-- Semidirect-product representative attached to a character `χ : H → C₂`. -/
noncomputable abbrev order24_SD (H : Type) [Group H] (χ : H →* Multiplicative (ZMod 2)) :
    Type :=
  SemidirectProduct order24_C3 H (order24_action χ)

noncomputable instance instFintypeOrder24SD {H : Type} [Group H] [Fintype H]
    (χ : H →* Multiplicative (ZMod 2)) : Fintype (order24_SD H χ) :=
  Fintype.ofEquiv (order24_C3 × H) SemidirectProduct.equivProd.symm

/-- Precomposing a character by an automorphism gives an isomorphic semidirect product. -/
noncomputable def order24_SD_equiv_of_character_comp {H : Type} [Group H]
    (χ ψ : H →* Multiplicative (ZMod 2)) (σ : H ≃* H)
    (hχ : χ.comp σ.toMonoidHom = ψ) :
    order24_SD H ψ ≃* order24_SD H χ := by
  have haction :
      (order24_action χ).comp σ.toMonoidHom = order24_action ψ :=
    order24_action_comp σ hχ
  exact (semidirectProductCongr_eq haction.symm).trans
    (semidirectProductCongrAut (N := order24_C3) (φ := order24_action χ) σ)

noncomputable def order24_c4c2_prod_equiv_snd :
    order24_SD order24_C4C2 order88_chiC4C2_prod ≃*
      order24_SD order24_C4C2 order88_chiC4C2_snd := by
  have haction :
      (order24_action order88_chiC4C2_snd).comp order88_C4C2_shear.toMonoidHom =
        order24_action order88_chiC4C2_prod :=
    order24_action_comp order88_C4C2_shear order88_chiC4C2_snd_comp_shear
  exact (semidirectProductCongr_eq haction.symm).trans
    (semidirectProductCongrAut (N := order24_C3)
      (φ := order24_action order88_chiC4C2_snd) order88_C4C2_shear)

noncomputable def order24_d8_prod_equiv_rot :
    order24_SD order24_D8 order88_chiD8_prod ≃*
      order24_SD order24_D8 order88_chiD8_rot := by
  have haction :
      (order24_action order88_chiD8_rot).comp order88_D8_shear.toMonoidHom =
        order24_action order88_chiD8_prod :=
    order24_action_comp order88_D8_shear order88_chiD8_rot_comp_shear
  exact (semidirectProductCongr_eq haction.symm).trans
    (semidirectProductCongrAut (N := order24_C3)
      (φ := order24_action order88_chiD8_rot) order88_D8_shear)

noncomputable def order24_q8_prod_equiv_q8 :
    order24_SD order24_Q8 order88_chiQ8_prod ≃*
      order24_SD order24_Q8 order88_chiQ8 := by
  have haction :
      (order24_action order88_chiQ8).comp order88_Q8_shear.toMonoidHom =
        order24_action order88_chiQ8_prod :=
    order24_action_comp order88_Q8_shear order88_chiQ8_comp_shear
  exact (semidirectProductCongr_eq haction.symm).trans
    (semidirectProductCongrAut (N := order24_C3)
      (φ := order24_action order88_chiQ8) order88_Q8_shear)

noncomputable def order24_q8_xa_equiv_q8 :
    order24_SD order24_Q8 order88_chiQ8_xa ≃*
      order24_SD order24_Q8 order88_chiQ8 := by
  have haction :
      (order24_action order88_chiQ8).comp order88_Q8_swap.toMonoidHom =
        order24_action order88_chiQ8_xa :=
    order24_action_comp order88_Q8_swap order88_chiQ8_comp_swap
  exact (semidirectProductCongr_eq haction.symm).trans
    (semidirectProductCongrAut (N := order24_C3)
      (φ := order24_action order88_chiQ8) order88_Q8_swap)

noncomputable def order24_c2c2c2_snd_equiv :
    order24_SD order24_C2C2C2 order88_chiC2C2C2_snd ≃*
      order24_SD order24_C2C2C2 order88_chiC2C2C2 :=
  order24_SD_equiv_of_character_comp order88_chiC2C2C2 order88_chiC2C2C2_snd
    order88_C2C2C2_swap12 order88_chiC2C2C2_comp_swap12

noncomputable def order24_c2c2c2_trd_equiv :
    order24_SD order24_C2C2C2 order88_chiC2C2C2_trd ≃*
      order24_SD order24_C2C2C2 order88_chiC2C2C2 :=
  order24_SD_equiv_of_character_comp order88_chiC2C2C2 order88_chiC2C2C2_trd
    order88_C2C2C2_swap13 order88_chiC2C2C2_comp_swap13

noncomputable def order24_c2c2c2_fst_snd_equiv :
    order24_SD order24_C2C2C2 order88_chiC2C2C2_fst_snd ≃*
      order24_SD order24_C2C2C2 order88_chiC2C2C2 :=
  order24_SD_equiv_of_character_comp order88_chiC2C2C2 order88_chiC2C2C2_fst_snd
    order88_C2C2C2_shear12 order88_chiC2C2C2_comp_shear12

noncomputable def order24_c2c2c2_fst_trd_equiv :
    order24_SD order24_C2C2C2 order88_chiC2C2C2_fst_trd ≃*
      order24_SD order24_C2C2C2 order88_chiC2C2C2 :=
  order24_SD_equiv_of_character_comp order88_chiC2C2C2 order88_chiC2C2C2_fst_trd
    order88_C2C2C2_shear13 order88_chiC2C2C2_comp_shear13

noncomputable def order24_c2c2c2_snd_trd_equiv :
    order24_SD order24_C2C2C2 order88_chiC2C2C2_snd_trd ≃*
      order24_SD order24_C2C2C2 order88_chiC2C2C2 :=
  order24_SD_equiv_of_character_comp order88_chiC2C2C2 order88_chiC2C2C2_snd_trd
    order88_C2C2C2_shear23 order88_chiC2C2C2_comp_shear23

noncomputable def order24_c2c2c2_fst_snd_trd_equiv :
    order24_SD order24_C2C2C2 order88_chiC2C2C2_fst_snd_trd ≃*
      order24_SD order24_C2C2C2 order88_chiC2C2C2 :=
  order24_SD_equiv_of_character_comp order88_chiC2C2C2 order88_chiC2C2C2_fst_snd_trd
    order88_C2C2C2_shear123 order88_chiC2C2C2_comp_shear123

/-- Direct-product representative with complement `H`. -/
abbrev order24_DP (H : Type) : Type := order24_C3 × H

abbrev order24_RA : Type := order24_DP order24_C8
abbrev order24_RB : Type := order24_DP order24_C4C2
abbrev order24_RC : Type := order24_DP order24_C2C2C2
abbrev order24_RD : Type := order24_DP order24_D8
abbrev order24_RE : Type := order24_DP order24_Q8
noncomputable abbrev order24_RF : Type := order24_SD order24_C8 order88_chiC8
noncomputable abbrev order24_RG : Type := order24_SD order24_C4C2 order88_chiC4C2_fst
noncomputable abbrev order24_RH : Type := order24_SD order24_C4C2 order88_chiC4C2_snd
noncomputable abbrev order24_RI : Type := order24_SD order24_C2C2C2 order88_chiC2C2C2
noncomputable abbrev order24_RJ : Type := order24_SD order24_D8 order88_chiD8_rot
noncomputable abbrev order24_RK : Type := order24_SD order24_D8 order88_chiD8_ref
noncomputable abbrev order24_RL : Type := order24_SD order24_Q8 order88_chiQ8

/-! ### The two extra normal Sylow-`2` representatives -/

/-- A standard order-`3` automorphism of `(C₂)^3`, fixing one factor. -/
def order24_tau3C2C2C2 : MulAut order24_C2C2C2 where
  toFun x := (x.1, (x.2.2, x.2.1 * x.2.2))
  invFun x := (x.1, (x.2.1 * x.2.2, x.2.1))
  left_inv := by
    rintro ⟨a, b, c⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> decide
  right_inv := by
    rintro ⟨a, b, c⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> decide
  map_mul' := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
      fin_cases a' <;> fin_cases b' <;> fin_cases c' <;> decide

theorem order24_tau3C2C2C2_pow_three : order24_tau3C2C2C2 ^ 3 = 1 := by
  apply MulEquiv.ext
  rintro ⟨a, b, c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

theorem order24_tau3C2C2C2_ne_one : order24_tau3C2C2C2 ≠ 1 := by
  intro h
  have hx := congrArg (fun f : MulAut order24_C2C2C2 =>
    f (1, (Multiplicative.ofAdd (1 : ZMod 2), 1))) h
  exact (by decide +kernel :
    order24_tau3C2C2C2 (1, (Multiplicative.ofAdd (1 : ZMod 2), 1)) ≠
      (1 : MulAut order24_C2C2C2) (1, (Multiplicative.ofAdd (1 : ZMod 2), 1))) hx

/-- The standard `C₃`-action on `(C₂)^3`. -/
def order24_c3ActionC2C2C2 : order24_C3 →* MulAut order24_C2C2C2 :=
  MonoidHom.mk' (fun x => order24_tau3C2C2C2 ^ (Multiplicative.toAdd x).val)
    (fun a b => pow_val_add order24_tau3C2C2C2_pow_three a.toAdd b.toAdd)

/-- A standard order-`3` automorphism of `Q₈`. -/
noncomputable abbrev order24_tau3Q8 : MulAut order24_Q8 :=
  order88_Q8_swap * order88_Q8_shear

theorem order24_tau3Q8_pow_three : order24_tau3Q8 ^ 3 = 1 := by
  apply MulEquiv.ext
  rintro (i | i) <;> fin_cases i <;> decide

theorem order24_tau3Q8_ne_one : order24_tau3Q8 ≠ 1 := by
  intro h
  have hx := congrArg (fun f : MulAut order24_Q8 => f (QuaternionGroup.a (1 : ZMod 4))) h
  exact (by decide +kernel :
    order24_tau3Q8 (QuaternionGroup.a (1 : ZMod 4)) ≠
      (1 : MulAut order24_Q8) (QuaternionGroup.a (1 : ZMod 4))) hx

/-- The standard `C₃`-action on `Q₈`. -/
noncomputable def order24_c3ActionQ8 : order24_C3 →* MulAut order24_Q8 :=
  MonoidHom.mk' (fun x => order24_tau3Q8 ^ (Multiplicative.toAdd x).val)
    (fun a b => pow_val_add order24_tau3Q8_pow_three a.toAdd b.toAdd)

abbrev order24_RM : Type :=
  SemidirectProduct order24_C2C2C2 order24_C3 order24_c3ActionC2C2C2

noncomputable abbrev order24_RN : Type :=
  SemidirectProduct order24_Q8 order24_C3 order24_c3ActionQ8

noncomputable instance instFintypeOrder24RM : Fintype order24_RM :=
  Fintype.ofEquiv (order24_C2C2C2 × order24_C3) SemidirectProduct.equivProd.symm

noncomputable instance instFintypeOrder24RN : Fintype order24_RN :=
  Fintype.ofEquiv (order24_Q8 × order24_C3) SemidirectProduct.equivProd.symm

/-- The twelve representatives in the normal Sylow-`3` branch. -/
noncomputable abbrev order24_normalC3_reps : Fin 12 → Type
  | 0 => order24_RA
  | 1 => order24_RB
  | 2 => order24_RC
  | 3 => order24_RD
  | 4 => order24_RE
  | 5 => order24_RF
  | 6 => order24_RG
  | 7 => order24_RH
  | 8 => order24_RI
  | 9 => order24_RJ
  | 10 => order24_RK
  | 11 => order24_RL

/-- The fourteen representatives covered by the normal-Sylow branches, excluding the `S₄` case. -/
noncomputable abbrev order24_nonS4_reps : Fin 14 → Type
  | 0 => order24_RA
  | 1 => order24_RB
  | 2 => order24_RC
  | 3 => order24_RD
  | 4 => order24_RE
  | 5 => order24_RF
  | 6 => order24_RG
  | 7 => order24_RH
  | 8 => order24_RI
  | 9 => order24_RJ
  | 10 => order24_RK
  | 11 => order24_RL
  | 12 => order24_RM
  | 13 => order24_RN

noncomputable instance instGroupOrder24NormalC3Reps : ∀ i, Group (order24_normalC3_reps i)
  | 0 => inferInstanceAs (Group order24_RA)
  | 1 => inferInstanceAs (Group order24_RB)
  | 2 => inferInstanceAs (Group order24_RC)
  | 3 => inferInstanceAs (Group order24_RD)
  | 4 => inferInstanceAs (Group order24_RE)
  | 5 => inferInstanceAs (Group order24_RF)
  | 6 => inferInstanceAs (Group order24_RG)
  | 7 => inferInstanceAs (Group order24_RH)
  | 8 => inferInstanceAs (Group order24_RI)
  | 9 => inferInstanceAs (Group order24_RJ)
  | 10 => inferInstanceAs (Group order24_RK)
  | 11 => inferInstanceAs (Group order24_RL)

noncomputable instance instGroupOrder24NonS4Reps : ∀ i, Group (order24_nonS4_reps i)
  | 0 => inferInstanceAs (Group order24_RA)
  | 1 => inferInstanceAs (Group order24_RB)
  | 2 => inferInstanceAs (Group order24_RC)
  | 3 => inferInstanceAs (Group order24_RD)
  | 4 => inferInstanceAs (Group order24_RE)
  | 5 => inferInstanceAs (Group order24_RF)
  | 6 => inferInstanceAs (Group order24_RG)
  | 7 => inferInstanceAs (Group order24_RH)
  | 8 => inferInstanceAs (Group order24_RI)
  | 9 => inferInstanceAs (Group order24_RJ)
  | 10 => inferInstanceAs (Group order24_RK)
  | 11 => inferInstanceAs (Group order24_RL)
  | 12 => inferInstanceAs (Group order24_RM)
  | 13 => inferInstanceAs (Group order24_RN)

/-! ### Cardinalities -/

theorem card_order24_C3 : Nat.card order24_C3 = 3 := card_cyclicRep (by norm_num)

theorem card_order24_C8 : Nat.card order24_C8 = 8 := card_order56_C8
theorem card_order24_C4C2 : Nat.card order24_C4C2 = 8 := card_order56_C4C2
theorem card_order24_C2C2C2 : Nat.card order24_C2C2C2 = 8 := card_order56_C2C2C2
theorem card_order24_D8 : Nat.card order24_D8 = 8 := card_order56_D8
theorem card_order24_Q8 : Nat.card order24_Q8 = 8 := card_order56_Q8

theorem card_order24_DP {H : Type} [Group H] (hH : Nat.card H = 8) :
    Nat.card (order24_DP H) = 24 := by
  rw [order24_DP, Nat.card_prod, card_order24_C3, hH]

theorem card_order24_SD {H : Type} [Group H] (χ : H →* Multiplicative (ZMod 2))
    (hH : Nat.card H = 8) : Nat.card (order24_SD H χ) = 24 := by
  rw [order24_SD, SemidirectProduct.card, card_order24_C3, hH]

theorem card_order24_RA : Nat.card order24_RA = 24 := card_order24_DP card_order24_C8
theorem card_order24_RB : Nat.card order24_RB = 24 := card_order24_DP card_order24_C4C2
theorem card_order24_RC : Nat.card order24_RC = 24 := card_order24_DP card_order24_C2C2C2
theorem card_order24_RD : Nat.card order24_RD = 24 := card_order24_DP card_order24_D8
theorem card_order24_RE : Nat.card order24_RE = 24 := card_order24_DP card_order24_Q8
theorem card_order24_RF : Nat.card order24_RF = 24 :=
  card_order24_SD order88_chiC8 card_order24_C8
theorem card_order24_RG : Nat.card order24_RG = 24 :=
  card_order24_SD order88_chiC4C2_fst card_order24_C4C2
theorem card_order24_RH : Nat.card order24_RH = 24 :=
  card_order24_SD order88_chiC4C2_snd card_order24_C4C2
theorem card_order24_RI : Nat.card order24_RI = 24 :=
  card_order24_SD order88_chiC2C2C2 card_order24_C2C2C2
theorem card_order24_RJ : Nat.card order24_RJ = 24 :=
  card_order24_SD order88_chiD8_rot card_order24_D8
theorem card_order24_RK : Nat.card order24_RK = 24 :=
  card_order24_SD order88_chiD8_ref card_order24_D8
theorem card_order24_RL : Nat.card order24_RL = 24 :=
  card_order24_SD order88_chiQ8 card_order24_Q8
theorem card_order24_RM : Nat.card order24_RM = 24 := by
  rw [order24_RM, SemidirectProduct.card, card_order24_C2C2C2, card_order24_C3]
theorem card_order24_RN : Nat.card order24_RN = 24 := by
  rw [order24_RN, SemidirectProduct.card, card_order24_Q8, card_order24_C3]

theorem card_order24_normalC3_reps (i : Fin 12) :
    Nat.card (order24_normalC3_reps i) = 24 := by
  fin_cases i
  · exact card_order24_RA
  · exact card_order24_RB
  · exact card_order24_RC
  · exact card_order24_RD
  · exact card_order24_RE
  · exact card_order24_RF
  · exact card_order24_RG
  · exact card_order24_RH
  · exact card_order24_RI
  · exact card_order24_RJ
  · exact card_order24_RK
  · exact card_order24_RL

theorem card_order24_nonS4_reps (i : Fin 14) :
    Nat.card (order24_nonS4_reps i) = 24 := by
  fin_cases i
  · exact card_order24_RA
  · exact card_order24_RB
  · exact card_order24_RC
  · exact card_order24_RD
  · exact card_order24_RE
  · exact card_order24_RF
  · exact card_order24_RG
  · exact card_order24_RH
  · exact card_order24_RI
  · exact card_order24_RJ
  · exact card_order24_RK
  · exact card_order24_RL
  · exact card_order24_RM
  · exact card_order24_RN

/-! ### Actions of `C₃` on groups of order `8` -/

/-- A homomorphism from `C₃` to a finite group whose order is not divisible by `3` is trivial. -/
theorem order24_c3_action_trivial_of_not_dvd_card {A : Type} [Group A] [Finite A]
    (hA : ¬ 3 ∣ Nat.card A) (φ : order24_C3 →* A) : φ = 1 := by
  letI : Fintype A := Fintype.ofFinite A
  apply MonoidHom.ext
  intro x
  apply orderOf_eq_one_iff.mp
  have hx3 : x ^ 3 = 1 := by
    have hx := pow_card_eq_one' (x := x)
    simpa [order24_C3, card_cyclicRep (by norm_num : 3 ≠ 0)] using hx
  have h3 : orderOf (φ x) ∣ 3 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    calc
      φ x ^ 3 = φ (x ^ 3) := by rw [map_pow]
      _ = 1 := by rw [hx3, map_one]
  have hcard : orderOf (φ x) ∣ Nat.card A := by
    rw [Nat.card_eq_fintype_card]
    exact orderOf_dvd_card
  have hcop : Nat.Coprime 3 (Nat.card A) :=
    (show Nat.Prime 3 by norm_num).coprime_iff_not_dvd.mpr hA
  exact Nat.eq_one_of_dvd_coprimes hcop h3 hcard

theorem order24_c3_action_c8_trivial (φ : order24_C3 →* MulAut order24_C8) : φ = 1 :=
  order24_c3_action_trivial_of_not_dvd_card (by rw [order56_card_aut_c8]; norm_num) φ

theorem order24_c3_action_c4c2_trivial (φ : order24_C3 →* MulAut order24_C4C2) : φ = 1 :=
  order24_c3_action_trivial_of_not_dvd_card (by rw [order56_card_aut_c4c2]; norm_num) φ

theorem order24_c3_action_d8_trivial (φ : order24_C3 →* MulAut order24_D8) : φ = 1 :=
  order24_c3_action_trivial_of_not_dvd_card (by rw [order56_card_aut_d8]; norm_num) φ

theorem order24_factorization_card_aut_c2c2c2_at_3 :
    Nat.factorization (Nat.card (MulAut order24_C2C2C2)) 3 = 1 := by
  rw [order56_card_aut_c2c2c2]
  decide +kernel

theorem order24_factorization_card_aut_q8_at_3 :
    Nat.factorization (Nat.card (MulAut order24_Q8)) 3 = 1 := by
  rw [order56_card_aut_q8]
  decide +kernel

theorem order24_tau3C2C2C2_zpow_eq_pow_unit_of_ne_one {k : ℤ}
    (hk : order24_tau3C2C2C2 ^ k ≠ 1) :
    ∃ u : (ZMod 3)ˣ, order24_tau3C2C2C2 ^ k =
      order24_tau3C2C2C2 ^ (u : ZMod 3).val := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have htau_order : orderOf order24_tau3C2C2C2 = 3 :=
    orderOf_eq_prime order24_tau3C2C2C2_pow_three order24_tau3C2C2C2_ne_one
  let r : ℕ := (k : ZMod 3).val
  have hrlt : r < 3 := by simpa [r] using ZMod.val_lt (k : ZMod 3)
  have hrne : r ≠ 0 := by
    intro hr0
    have hkz : (k : ZMod 3) = 0 := by
      rw [← ZMod.natCast_zmod_val (k : ZMod 3)]
      simp [r, hr0]
    have hmod0 : (0 : ℤ) ≡ k [ZMOD (3 : ℤ)] :=
      (ZMod.intCast_eq_intCast_iff 0 k 3).mp (by simp [hkz])
    have hpow : order24_tau3C2C2C2 ^ (0 : ℤ) = order24_tau3C2C2C2 ^ k := by
      rw [zpow_eq_zpow_iff_modEq, htau_order]
      exact hmod0
    exact hk (by simpa using hpow.symm)
  have hcop : Nat.Coprime r 3 := by
    exact ((show Nat.Prime 3 by norm_num).coprime_iff_not_dvd.mpr (by
      intro hd
      have hpos : 0 < r := Nat.pos_of_ne_zero hrne
      have hle : 3 ≤ r := Nat.le_of_dvd hpos hd
      omega)).symm
  refine ⟨ZMod.unitOfCoprime r hcop, ?_⟩
  have huval : ((ZMod.unitOfCoprime r hcop : (ZMod 3)ˣ) : ZMod 3).val = r := by
    have hcoe : ((ZMod.unitOfCoprime r hcop : (ZMod 3)ˣ) : ZMod 3) = (r : ZMod 3) :=
      ZMod.coe_unitOfCoprime r hcop
    rw [hcoe]
    exact ZMod.val_natCast_of_lt hrlt
  rw [huval]
  have hmod : (r : ℤ) ≡ k [ZMOD (3 : ℤ)] :=
    (ZMod.intCast_eq_intCast_iff (r : ℤ) k 3).mp (by simp [r])
  rw [← zpow_natCast]
  rw [zpow_eq_zpow_iff_modEq, htau_order]
  exact hmod.symm

theorem order24_c2c2c2_aut_order3_conj_pow_unit
    (α : MulAut order24_C2C2C2) (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1) :
    ∃ (θ : MulAut order24_C2C2C2) (u : (ZMod 3)ˣ),
      (MulAut.conj θ) α = order24_tau3C2C2C2 ^ (u : ZMod 3).val := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let A := MulAut order24_C2C2C2
  have hfact : Nat.factorization (Nat.card A) 3 = 1 :=
    order24_factorization_card_aut_c2c2c2_at_3
  have hαord : orderOf α = 3 := orderOf_eq_prime hα3 hα1
  have hτord : orderOf order24_tau3C2C2C2 = 3 :=
    orderOf_eq_prime order24_tau3C2C2C2_pow_three order24_tau3C2C2C2_ne_one
  let Pα : Sylow 3 A := Sylow.ofCard (Subgroup.zpowers α) (by
    rw [Nat.card_zpowers, hαord, hfact]
    norm_num)
  let Pτ : Sylow 3 A := Sylow.ofCard (Subgroup.zpowers order24_tau3C2C2C2) (by
    rw [Nat.card_zpowers, hτord, hfact]
    norm_num)
  obtain ⟨θ, hθ⟩ := MulAction.exists_smul_eq A Pα Pτ
  have hPα : (↑Pα : Subgroup A) = Subgroup.zpowers α := Sylow.coe_ofCard _ _
  have hPτ : (↑Pτ : Subgroup A) = Subgroup.zpowers order24_tau3C2C2C2 :=
    Sylow.coe_ofCard _ _
  have hsub : (MulAut.conj θ) • (Subgroup.zpowers α : Subgroup A) =
      Subgroup.zpowers order24_tau3C2C2C2 := by
    rw [← hPα, ← Sylow.coe_subgroup_smul, hθ, hPτ]
  have hmem : (MulAut.conj θ) α ∈ Subgroup.zpowers order24_tau3C2C2C2 := by
    rw [← hsub]
    rw [Subgroup.pointwise_smul_def]
    rw [Subgroup.mem_map]
    exact ⟨α, Subgroup.mem_zpowers α, rfl⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hkne : order24_tau3C2C2C2 ^ k ≠ 1 := by
    intro h1
    have hconj1 : (MulAut.conj θ) α = 1 := by rw [← hk, h1]
    have hα_eq : α = 1 := by
      apply (MulAut.conj θ).injective
      simpa using hconj1
    exact hα1 hα_eq
  obtain ⟨u, hu⟩ := order24_tau3C2C2C2_zpow_eq_pow_unit_of_ne_one hkne
  exact ⟨θ, u, by rw [← hk, hu]⟩

theorem order24_tau3Q8_zpow_eq_pow_unit_of_ne_one {k : ℤ}
    (hk : order24_tau3Q8 ^ k ≠ 1) :
    ∃ u : (ZMod 3)ˣ, order24_tau3Q8 ^ k = order24_tau3Q8 ^ (u : ZMod 3).val := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have htau_order : orderOf order24_tau3Q8 = 3 :=
    orderOf_eq_prime order24_tau3Q8_pow_three order24_tau3Q8_ne_one
  let r : ℕ := (k : ZMod 3).val
  have hrlt : r < 3 := by simpa [r] using ZMod.val_lt (k : ZMod 3)
  have hrne : r ≠ 0 := by
    intro hr0
    have hkz : (k : ZMod 3) = 0 := by
      rw [← ZMod.natCast_zmod_val (k : ZMod 3)]
      simp [r, hr0]
    have hmod0 : (0 : ℤ) ≡ k [ZMOD (3 : ℤ)] :=
      (ZMod.intCast_eq_intCast_iff 0 k 3).mp (by simp [hkz])
    have hpow : order24_tau3Q8 ^ (0 : ℤ) = order24_tau3Q8 ^ k := by
      rw [zpow_eq_zpow_iff_modEq, htau_order]
      exact hmod0
    exact hk (by simpa using hpow.symm)
  have hcop : Nat.Coprime r 3 := by
    exact ((show Nat.Prime 3 by norm_num).coprime_iff_not_dvd.mpr (by
      intro hd
      have hpos : 0 < r := Nat.pos_of_ne_zero hrne
      have hle : 3 ≤ r := Nat.le_of_dvd hpos hd
      omega)).symm
  refine ⟨ZMod.unitOfCoprime r hcop, ?_⟩
  have huval : ((ZMod.unitOfCoprime r hcop : (ZMod 3)ˣ) : ZMod 3).val = r := by
    have hcoe : ((ZMod.unitOfCoprime r hcop : (ZMod 3)ˣ) : ZMod 3) = (r : ZMod 3) :=
      ZMod.coe_unitOfCoprime r hcop
    rw [hcoe]
    exact ZMod.val_natCast_of_lt hrlt
  rw [huval]
  have hmod : (r : ℤ) ≡ k [ZMOD (3 : ℤ)] :=
    (ZMod.intCast_eq_intCast_iff (r : ℤ) k 3).mp (by simp [r])
  rw [← zpow_natCast]
  rw [zpow_eq_zpow_iff_modEq, htau_order]
  exact hmod.symm

theorem order24_q8_aut_order3_conj_pow_unit
    (α : MulAut order24_Q8) (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1) :
    ∃ (θ : MulAut order24_Q8) (u : (ZMod 3)ˣ),
      (MulAut.conj θ) α = order24_tau3Q8 ^ (u : ZMod 3).val := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let A := MulAut order24_Q8
  have hfact : Nat.factorization (Nat.card A) 3 = 1 :=
    order24_factorization_card_aut_q8_at_3
  have hαord : orderOf α = 3 := orderOf_eq_prime hα3 hα1
  have hτord : orderOf order24_tau3Q8 = 3 :=
    orderOf_eq_prime order24_tau3Q8_pow_three order24_tau3Q8_ne_one
  let Pα : Sylow 3 A := Sylow.ofCard (Subgroup.zpowers α) (by
    rw [Nat.card_zpowers, hαord, hfact]
    norm_num)
  let Pτ : Sylow 3 A := Sylow.ofCard (Subgroup.zpowers order24_tau3Q8) (by
    rw [Nat.card_zpowers, hτord, hfact]
    norm_num)
  obtain ⟨θ, hθ⟩ := MulAction.exists_smul_eq A Pα Pτ
  have hPα : (↑Pα : Subgroup A) = Subgroup.zpowers α := Sylow.coe_ofCard _ _
  have hPτ : (↑Pτ : Subgroup A) = Subgroup.zpowers order24_tau3Q8 :=
    Sylow.coe_ofCard _ _
  have hsub : (MulAut.conj θ) • (Subgroup.zpowers α : Subgroup A) =
      Subgroup.zpowers order24_tau3Q8 := by
    rw [← hPα, ← Sylow.coe_subgroup_smul, hθ, hPτ]
  have hmem : (MulAut.conj θ) α ∈ Subgroup.zpowers order24_tau3Q8 := by
    rw [← hsub]
    rw [Subgroup.pointwise_smul_def]
    rw [Subgroup.mem_map]
    exact ⟨α, Subgroup.mem_zpowers α, rfl⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hkne : order24_tau3Q8 ^ k ≠ 1 := by
    intro h1
    have hconj1 : (MulAut.conj θ) α = 1 := by rw [← hk, h1]
    have hα_eq : α = 1 := by
      apply (MulAut.conj θ).injective
      simpa using hconj1
    exact hα1 hα_eq
  obtain ⟨u, hu⟩ := order24_tau3Q8_zpow_eq_pow_unit_of_ne_one hkne
  exact ⟨θ, u, by rw [← hk, hu]⟩

theorem order24_c3_hom_ext {M : Type} [Group M] {φ ψ : order24_C3 →* M}
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

theorem order24_c3_action_c2c2c2_nontrivial_equiv
    (φ : order24_C3 →* MulAut order24_C2C2C2) (hφ : φ ≠ 1) :
    Nonempty (SemidirectProduct order24_C2C2C2 order24_C3 φ ≃* order24_RM) := by
  let g : order24_C3 := Multiplicative.ofAdd (1 : ZMod 3)
  have hg3 : g ^ 3 = 1 := by decide
  have hα3 : φ g ^ 3 = 1 := by
    calc
      φ g ^ 3 = φ (g ^ 3) := by rw [map_pow]
      _ = 1 := by rw [hg3, map_one]
  have hα1 : φ g ≠ 1 := by
    intro hgen
    apply hφ
    apply order24_c3_hom_ext
    simpa using hgen
  obtain ⟨θ, u, hθu⟩ := order24_c2c2c2_aut_order3_conj_pow_unit (φ g) hα3 hα1
  have hgen_eq : (((MulAut.conj θ).toMonoidHom.comp φ)
        (Multiplicative.ofAdd (1 : ZMod 3))) =
      (order24_c3ActionC2C2C2.comp (unitAutHom u).toMonoidHom)
        (Multiplicative.ofAdd (1 : ZMod 3)) := by
    change (MulAut.conj θ) (φ g) = order24_tau3C2C2C2 ^
      (Multiplicative.toAdd ((unitAutHom u) g)).val
    rw [hθu]
    have htoadd : Multiplicative.toAdd ((unitAutHom u) g) = (u : ZMod 3) := by
      simp [g, unitAutHom_apply]
    rw [htoadd]
  have haction : ((MulAut.conj θ).toMonoidHom.comp φ) =
      order24_c3ActionC2C2C2.comp (unitAutHom u).toMonoidHom :=
    order24_c3_hom_ext hgen_eq
  exact ⟨(semidirectProductCongrConj θ).trans
    ((semidirectProductCongr_eq haction).trans (semidirectProductCongrAut (unitAutHom u)))⟩

theorem order24_c3_action_q8_nontrivial_equiv
    (φ : order24_C3 →* MulAut order24_Q8) (hφ : φ ≠ 1) :
    Nonempty (SemidirectProduct order24_Q8 order24_C3 φ ≃* order24_RN) := by
  let g : order24_C3 := Multiplicative.ofAdd (1 : ZMod 3)
  have hg3 : g ^ 3 = 1 := by decide
  have hα3 : φ g ^ 3 = 1 := by
    calc
      φ g ^ 3 = φ (g ^ 3) := by rw [map_pow]
      _ = 1 := by rw [hg3, map_one]
  have hα1 : φ g ≠ 1 := by
    intro hgen
    apply hφ
    apply order24_c3_hom_ext
    simpa using hgen
  obtain ⟨θ, u, hθu⟩ := order24_q8_aut_order3_conj_pow_unit (φ g) hα3 hα1
  have hgen_eq : (((MulAut.conj θ).toMonoidHom.comp φ)
        (Multiplicative.ofAdd (1 : ZMod 3))) =
      (order24_c3ActionQ8.comp (unitAutHom u).toMonoidHom)
        (Multiplicative.ofAdd (1 : ZMod 3)) := by
    change (MulAut.conj θ) (φ g) = order24_tau3Q8 ^
      (Multiplicative.toAdd ((unitAutHom u) g)).val
    rw [hθu]
    have htoadd : Multiplicative.toAdd ((unitAutHom u) g) = (u : ZMod 3) := by
      simp [g, unitAutHom_apply]
    rw [htoadd]
  have haction : ((MulAut.conj θ).toMonoidHom.comp φ) =
      order24_c3ActionQ8.comp (unitAutHom u).toMonoidHom :=
    order24_c3_hom_ext hgen_eq
  exact ⟨(semidirectProductCongrConj θ).trans
    ((semidirectProductCongr_eq haction).trans (semidirectProductCongrAut (unitAutHom u)))⟩

/-! ### Normal Sylow-`3` branch exhaustiveness -/

private theorem order24_classification_of_c8_action {G : Type*} [Group G]
    {φ : order24_C8 →* MulAut order24_C3}
    (e : G ≃* SemidirectProduct order24_C3 order24_C8 φ) :
    ∃ i, Nonempty (G ≃* order24_normalC3_reps i) := by
  rcases order24_c8_action_cases φ with hφ | hφ
  · exact ⟨0, by
      simpa [order24_normalC3_reps] using
        (⟨e.trans ((semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd)⟩ :
          Nonempty (G ≃* order24_RA))⟩
  · exact ⟨5, by simpa [order24_normalC3_reps] using
      (⟨e.trans (semidirectProductCongr_eq hφ)⟩ : Nonempty (G ≃* order24_RF))⟩

private theorem order24_classification_of_c4c2_action {G : Type*} [Group G]
    {φ : order24_C4C2 →* MulAut order24_C3}
    (e : G ≃* SemidirectProduct order24_C3 order24_C4C2 φ) :
    ∃ i, Nonempty (G ≃* order24_normalC3_reps i) := by
  rcases order24_c4c2_action_cases φ with hφ | hφ | hφ | hφ
  · exact ⟨1, by
      simpa [order24_normalC3_reps] using
        (⟨e.trans ((semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd)⟩ :
          Nonempty (G ≃* order24_RB))⟩
  · exact ⟨6, by simpa [order24_normalC3_reps] using
      (⟨e.trans (semidirectProductCongr_eq hφ)⟩ : Nonempty (G ≃* order24_RG))⟩
  · exact ⟨7, by simpa [order24_normalC3_reps] using
      (⟨e.trans (semidirectProductCongr_eq hφ)⟩ : Nonempty (G ≃* order24_RH))⟩
  · exact ⟨7, by simpa [order24_normalC3_reps] using
      (⟨e.trans ((semidirectProductCongr_eq hφ).trans order24_c4c2_prod_equiv_snd)⟩ :
        Nonempty (G ≃* order24_RH))⟩

private theorem order24_classification_of_c2c2c2_action {G : Type*} [Group G]
    {φ : order24_C2C2C2 →* MulAut order24_C3}
    (e : G ≃* SemidirectProduct order24_C3 order24_C2C2C2 φ) :
    ∃ i, Nonempty (G ≃* order24_normalC3_reps i) := by
  rcases order24_c2c2c2_action_cases φ with
    hφ | hφ | hφ | hφ | hφ | hφ | hφ | hφ
  · exact ⟨2, by
      simpa [order24_normalC3_reps] using
        (⟨e.trans ((semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd)⟩ :
          Nonempty (G ≃* order24_RC))⟩
  · exact ⟨8, by simpa [order24_normalC3_reps] using
      (⟨e.trans (semidirectProductCongr_eq hφ)⟩ : Nonempty (G ≃* order24_RI))⟩
  · exact ⟨8, by simpa [order24_normalC3_reps] using
      (⟨e.trans ((semidirectProductCongr_eq hφ).trans order24_c2c2c2_snd_equiv)⟩ :
        Nonempty (G ≃* order24_RI))⟩
  · exact ⟨8, by simpa [order24_normalC3_reps] using
      (⟨e.trans ((semidirectProductCongr_eq hφ).trans order24_c2c2c2_trd_equiv)⟩ :
        Nonempty (G ≃* order24_RI))⟩
  · exact ⟨8, by simpa [order24_normalC3_reps] using
      (⟨e.trans ((semidirectProductCongr_eq hφ).trans order24_c2c2c2_fst_snd_equiv)⟩ :
        Nonempty (G ≃* order24_RI))⟩
  · exact ⟨8, by simpa [order24_normalC3_reps] using
      (⟨e.trans ((semidirectProductCongr_eq hφ).trans order24_c2c2c2_fst_trd_equiv)⟩ :
        Nonempty (G ≃* order24_RI))⟩
  · exact ⟨8, by simpa [order24_normalC3_reps] using
      (⟨e.trans ((semidirectProductCongr_eq hφ).trans order24_c2c2c2_snd_trd_equiv)⟩ :
        Nonempty (G ≃* order24_RI))⟩
  · exact ⟨8, by simpa [order24_normalC3_reps] using
      (⟨e.trans ((semidirectProductCongr_eq hφ).trans order24_c2c2c2_fst_snd_trd_equiv)⟩ :
        Nonempty (G ≃* order24_RI))⟩

private theorem order24_classification_of_d8_action {G : Type*} [Group G]
    {φ : order24_D8 →* MulAut order24_C3}
    (e : G ≃* SemidirectProduct order24_C3 order24_D8 φ) :
    ∃ i, Nonempty (G ≃* order24_normalC3_reps i) := by
  rcases order24_d8_action_cases φ with hφ | hφ | hφ | hφ
  · exact ⟨3, by
      simpa [order24_normalC3_reps] using
        (⟨e.trans ((semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd)⟩ :
          Nonempty (G ≃* order24_RD))⟩
  · exact ⟨9, by simpa [order24_normalC3_reps] using
      (⟨e.trans (semidirectProductCongr_eq hφ)⟩ : Nonempty (G ≃* order24_RJ))⟩
  · exact ⟨10, by simpa [order24_normalC3_reps] using
      (⟨e.trans (semidirectProductCongr_eq hφ)⟩ : Nonempty (G ≃* order24_RK))⟩
  · exact ⟨9, by simpa [order24_normalC3_reps] using
      (⟨e.trans ((semidirectProductCongr_eq hφ).trans order24_d8_prod_equiv_rot)⟩ :
        Nonempty (G ≃* order24_RJ))⟩

private theorem order24_classification_of_q8_action {G : Type*} [Group G]
    {φ : order24_Q8 →* MulAut order24_C3}
    (e : G ≃* SemidirectProduct order24_C3 order24_Q8 φ) :
    ∃ i, Nonempty (G ≃* order24_normalC3_reps i) := by
  rcases order24_q8_action_cases φ with hφ | hφ | hφ | hφ
  · exact ⟨4, by
      simpa [order24_normalC3_reps] using
        (⟨e.trans ((semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd)⟩ :
          Nonempty (G ≃* order24_RE))⟩
  · exact ⟨11, by simpa [order24_normalC3_reps] using
      (⟨e.trans (semidirectProductCongr_eq hφ)⟩ : Nonempty (G ≃* order24_RL))⟩
  · exact ⟨11, by simpa [order24_normalC3_reps] using
      (⟨e.trans ((semidirectProductCongr_eq hφ).trans order24_q8_xa_equiv_q8)⟩ :
        Nonempty (G ≃* order24_RL))⟩
  · exact ⟨11, by simpa [order24_normalC3_reps] using
      (⟨e.trans ((semidirectProductCongr_eq hφ).trans order24_q8_prod_equiv_q8)⟩ :
        Nonempty (G ≃* order24_RL))⟩

/-- If the Sylow `3`-subgroup is normal, the group lies among the twelve displayed
`C₃ ⋊ H` representatives. -/
theorem order24_classification_of_card_sylow_3_eq_one [Finite G] (hG : Nat.card G = 24)
    (hSyl : Nat.card (Sylow 3 G) = 1) :
    ∃ i, Nonempty (G ≃* order24_normalC3_reps i) := by
  obtain ⟨N, H, φ, _, hcardN, hcardH, ⟨e⟩⟩ :=
    order24_semidirectProduct_of_card_sylow_3_eq_one hG hSyl
  obtain ⟨eN⟩ := prime_classification (by norm_num : Nat.Prime 3) hcardN
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Fintype H := Fintype.ofFinite H
  rcases P3Group.classification 2 H (hcardH.trans (by norm_num)) with
    hH | hH | hH | hH | hH | hH | hH
  · change Nonempty (H ≃* order24_C8) at hH
    obtain ⟨eH⟩ := hH
    exact order24_classification_of_c8_action (e.trans (SemidirectProduct.congr' eN eH))
  · change Nonempty (H ≃* order24_C4C2) at hH
    obtain ⟨eH⟩ := hH
    exact order24_classification_of_c4c2_action (e.trans (SemidirectProduct.congr' eN eH))
  · change Nonempty (H ≃* order24_C2C2C2) at hH
    obtain ⟨eH⟩ := hH
    exact order24_classification_of_c2c2c2_action (e.trans (SemidirectProduct.congr' eN eH))
  · exact (hH.1 rfl).elim
  · exact (hH.1 rfl).elim
  · obtain ⟨eH⟩ := hH.2
    exact order24_classification_of_d8_action (e.trans (SemidirectProduct.congr' eN eH))
  · obtain ⟨eH⟩ := hH.2
    exact order24_classification_of_q8_action (e.trans (SemidirectProduct.congr' eN eH))

/-! ### Normal Sylow-`2` branch exhaustiveness -/

/-- In a group of order `24`, the number of Sylow `2`-subgroups is `1` or `3`. -/
theorem card_sylow_2_of_card_24_eq_one_or_three [Finite G] (hG : Nat.card G = 24) :
    Nat.card (Sylow 2 G) = 1 ∨ Nat.card (Sylow 2 G) = 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 2 G))
  have hndvd_2 : ¬ 2 ∣ Nat.card (Sylow 2 G) := not_dvd_card_sylow 2 G
  have hdvd24 : Nat.card (Sylow 2 G) ∣ 24 := by
    rw [← hG]
    exact P0.card_dvd_index.trans (Subgroup.index_dvd_card _)
  have h24 : 24 = 3 * 2 ^ 3 := by norm_num
  have hdvd3_mul : Nat.card (Sylow 2 G) ∣ 3 * 2 ^ 3 := by
    simpa [h24] using hdvd24
  have hcop : Nat.Coprime (Nat.card (Sylow 2 G)) (2 ^ 3) :=
    (show Nat.Prime 2 by norm_num).coprime_pow_of_not_dvd hndvd_2
  have hdvd3 : Nat.card (Sylow 2 G) ∣ 3 := hcop.dvd_of_dvd_mul_right hdvd3_mul
  have hmod := card_sylow_modEq_one 2 G
  have hle : Nat.card (Sylow 2 G) ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd3
  have hpos : 0 < Nat.card (Sylow 2 G) := Nat.card_pos
  interval_cases h : Nat.card (Sylow 2 G)
  · exact Or.inl rfl
  · unfold Nat.ModEq at hmod; norm_num at hmod
  · exact Or.inr rfl

/-- If there is a unique Sylow `2`-subgroup, it is normal. -/
theorem sylow_2_normal_of_card_24_of_card_sylow_eq_one [Finite G]
    (hSyl : Nat.card (Sylow 2 G) = 1) (P : Sylow 2 G) :
    (↑P : Subgroup G).Normal := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Subsingleton (Sylow 2 G) := (Nat.card_eq_one_iff_unique.mp hSyl).1
  exact normal_of_subsingleton P

/-- A Sylow `2`-subgroup of a group of order `24` has order `8`. -/
theorem card_sylow_2_subgroup_of_card_24 [Finite G] (hG : Nat.card G = 24)
    (P : Sylow 2 G) : Nat.card (↑P : Subgroup G) = 8 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hfact : (24 : ℕ).factorization 2 = 3 := by
    decide +kernel
  rw [Sylow.card_eq_multiplicity, hG, hfact]
  norm_num

/-- **Schur--Zassenhaus reduction for the normal Sylow-`2` branch of order `24`.** -/
theorem order24_semidirectProduct_of_card_sylow_2_eq_one [Finite G] (hG : Nat.card G = 24)
    (hSyl : Nat.card (Sylow 2 G) = 1) :
    ∃ (N H : Subgroup G) (φ : H →* MulAut N),
      N.Normal ∧ Nat.card N = 8 ∧ Nat.card H = 3 ∧
        Nonempty (G ≃* SemidirectProduct N H φ) := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 2 G))
  haveI hnorm : (↑P0 : Subgroup G).Normal :=
    sylow_2_normal_of_card_24_of_card_sylow_eq_one hSyl P0
  have hcardN : Nat.card (↑P0 : Subgroup G) = 8 :=
    card_sylow_2_subgroup_of_card_24 hG P0
  haveI : (↑P0 : Subgroup G).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
  have hcop : Nat.Coprime (Nat.card (↑P0 : Subgroup G)) (↑P0 : Subgroup G).index := by
    rw [hcardN]
    have := P0.not_dvd_index
    simpa using ((show Nat.Prime 2 by norm_num).coprime_pow_of_not_dvd (m := 3) this).symm
  obtain ⟨H, φ, ⟨e⟩⟩ := schurZassenhaus_semidirectProduct (↑P0 : Subgroup G) hcop
  have hcardH : Nat.card H = 3 := by
    have h1 : Nat.card G = Nat.card (↑P0 : Subgroup G) * Nat.card H := by
      rw [Nat.card_congr e.toEquiv, Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
    rw [hG, hcardN] at h1
    have h1' : 8 * Nat.card H = 8 * 3 := by omega
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 8) h1'
  exact ⟨↑P0, H, φ, hnorm, hcardN, hcardH, ⟨e⟩⟩

private theorem order24_classification_of_c3_action_on_c8 {G : Type*} [Group G]
    {φ : order24_C3 →* MulAut order24_C8}
    (e : G ≃* SemidirectProduct order24_C8 order24_C3 φ) :
    ∃ i, Nonempty (G ≃* order24_nonS4_reps i) := by
  have hφ : φ = 1 := order24_c3_action_c8_trivial φ
  exact ⟨0, by
    simpa [order24_nonS4_reps, order24_RA, order24_DP] using
      (⟨e.trans ((semidirectProductCongr_eq hφ).trans
        (SemidirectProduct.mulEquivProd.trans
          (MulEquiv.prodComm : order24_C8 × order24_C3 ≃* order24_C3 × order24_C8)))⟩ :
        Nonempty (G ≃* order24_RA))⟩

private theorem order24_classification_of_c3_action_on_c4c2 {G : Type*} [Group G]
    {φ : order24_C3 →* MulAut order24_C4C2}
    (e : G ≃* SemidirectProduct order24_C4C2 order24_C3 φ) :
    ∃ i, Nonempty (G ≃* order24_nonS4_reps i) := by
  have hφ : φ = 1 := order24_c3_action_c4c2_trivial φ
  exact ⟨1, by
    simpa [order24_nonS4_reps, order24_RB, order24_DP] using
      (⟨e.trans ((semidirectProductCongr_eq hφ).trans
        (SemidirectProduct.mulEquivProd.trans
          (MulEquiv.prodComm : order24_C4C2 × order24_C3 ≃* order24_C3 × order24_C4C2)))⟩ :
        Nonempty (G ≃* order24_RB))⟩

private theorem order24_classification_of_trivial_c3_action_on_c2c2c2 {G : Type*} [Group G]
    {φ : order24_C3 →* MulAut order24_C2C2C2} (hφ : φ = 1)
    (e : G ≃* SemidirectProduct order24_C2C2C2 order24_C3 φ) :
    ∃ i, Nonempty (G ≃* order24_nonS4_reps i) := by
  exact ⟨2, by
    simpa [order24_nonS4_reps, order24_RC, order24_DP] using
      (⟨e.trans ((semidirectProductCongr_eq hφ).trans
        (SemidirectProduct.mulEquivProd.trans
          (MulEquiv.prodComm :
            order24_C2C2C2 × order24_C3 ≃* order24_C3 × order24_C2C2C2)))⟩ :
        Nonempty (G ≃* order24_RC))⟩

private theorem order24_classification_of_c3_action_on_c2c2c2 {G : Type*} [Group G]
    {φ : order24_C3 →* MulAut order24_C2C2C2}
    (e : G ≃* SemidirectProduct order24_C2C2C2 order24_C3 φ) :
    ∃ i, Nonempty (G ≃* order24_nonS4_reps i) := by
  by_cases hφ : φ = 1
  · exact order24_classification_of_trivial_c3_action_on_c2c2c2 hφ e
  · obtain ⟨eRM⟩ := order24_c3_action_c2c2c2_nontrivial_equiv φ hφ
    exact ⟨12, by simpa [order24_nonS4_reps] using
      (⟨e.trans eRM⟩ : Nonempty (G ≃* order24_RM))⟩

private theorem order24_classification_of_c3_action_on_d8 {G : Type*} [Group G]
    {φ : order24_C3 →* MulAut order24_D8}
    (e : G ≃* SemidirectProduct order24_D8 order24_C3 φ) :
    ∃ i, Nonempty (G ≃* order24_nonS4_reps i) := by
  have hφ : φ = 1 := order24_c3_action_d8_trivial φ
  exact ⟨3, by
    simpa [order24_nonS4_reps, order24_RD, order24_DP] using
      (⟨e.trans ((semidirectProductCongr_eq hφ).trans
        (SemidirectProduct.mulEquivProd.trans
          (MulEquiv.prodComm : order24_D8 × order24_C3 ≃* order24_C3 × order24_D8)))⟩ :
        Nonempty (G ≃* order24_RD))⟩

private theorem order24_classification_of_trivial_c3_action_on_q8 {G : Type*} [Group G]
    {φ : order24_C3 →* MulAut order24_Q8} (hφ : φ = 1)
    (e : G ≃* SemidirectProduct order24_Q8 order24_C3 φ) :
    ∃ i, Nonempty (G ≃* order24_nonS4_reps i) := by
  exact ⟨4, by
    simpa [order24_nonS4_reps, order24_RE, order24_DP] using
      (⟨e.trans ((semidirectProductCongr_eq hφ).trans
        (SemidirectProduct.mulEquivProd.trans
          (MulEquiv.prodComm : order24_Q8 × order24_C3 ≃* order24_C3 × order24_Q8)))⟩ :
        Nonempty (G ≃* order24_RE))⟩

private theorem order24_classification_of_c3_action_on_q8 {G : Type*} [Group G]
    {φ : order24_C3 →* MulAut order24_Q8}
    (e : G ≃* SemidirectProduct order24_Q8 order24_C3 φ) :
    ∃ i, Nonempty (G ≃* order24_nonS4_reps i) := by
  by_cases hφ : φ = 1
  · exact order24_classification_of_trivial_c3_action_on_q8 hφ e
  · obtain ⟨eRN⟩ := order24_c3_action_q8_nontrivial_equiv φ hφ
    exact ⟨13, by simpa [order24_nonS4_reps] using
      (⟨e.trans eRN⟩ : Nonempty (G ≃* order24_RN))⟩

/-- If the Sylow `2`-subgroup is normal, the group lies among the fourteen displayed
non-`S₄` representatives. -/
theorem order24_classification_of_card_sylow_2_eq_one [Finite G] (hG : Nat.card G = 24)
    (hSyl : Nat.card (Sylow 2 G) = 1) :
    ∃ i, Nonempty (G ≃* order24_nonS4_reps i) := by
  obtain ⟨N, H, φ, _, hcardN, hcardH, ⟨e⟩⟩ :=
    order24_semidirectProduct_of_card_sylow_2_eq_one hG hSyl
  obtain ⟨eH⟩ := prime_classification (by norm_num : Nat.Prime 3) hcardH
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Fintype N := Fintype.ofFinite N
  rcases P3Group.classification 2 N (hcardN.trans (by norm_num)) with
    hN | hN | hN | hN | hN | hN | hN
  · change Nonempty (N ≃* order24_C8) at hN
    obtain ⟨eN⟩ := hN
    exact order24_classification_of_c3_action_on_c8 (e.trans (SemidirectProduct.congr' eN eH))
  · change Nonempty (N ≃* order24_C4C2) at hN
    obtain ⟨eN⟩ := hN
    exact order24_classification_of_c3_action_on_c4c2
      (e.trans (SemidirectProduct.congr' eN eH))
  · change Nonempty (N ≃* order24_C2C2C2) at hN
    obtain ⟨eN⟩ := hN
    exact order24_classification_of_c3_action_on_c2c2c2
      (e.trans (SemidirectProduct.congr' eN eH))
  · exact (hN.1 rfl).elim
  · exact (hN.1 rfl).elim
  · obtain ⟨eN⟩ := hN.2
    exact order24_classification_of_c3_action_on_d8 (e.trans (SemidirectProduct.congr' eN eH))
  · obtain ⟨eN⟩ := hN.2
    exact order24_classification_of_c3_action_on_q8 (e.trans (SemidirectProduct.congr' eN eH))

end Smallgroups.UsefulTheorems
