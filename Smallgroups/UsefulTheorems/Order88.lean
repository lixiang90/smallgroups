/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order2PSq
import Smallgroups.UsefulTheorems.P3Group
import Smallgroups.UsefulTheorems.SchurZassenhaus
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic.NormNum.Prime

/-!
# First reductions for groups of order 88

Since `88 = 8 * 11`, the Sylow `11`-subgroup is normal.  Thus every group of
order `88` splits as `C₁₁ ⋊ H`, where `H` is a group of order `8`.

This file records that reduction and the twelve expected semidirect-product
representatives.  The remaining classification work is the orbit calculation
for homomorphisms `H → Aut(C₁₁)`.
-/

namespace Smallgroups.UsefulTheorems

open Sylow

variable {G : Type*} [Group G]

/-! ### Sylow-11 normality and semidirect-product reduction -/

/-- The Sylow `11`-subgroup is unique in a group of order `88`. -/
theorem card_sylow_11_eq_one_of_card_88 [Finite G] (hG : Nat.card G = 88) :
    Nat.card (Sylow 11 G) = 1 := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 11 G))
  have hndvd_11 : ¬ 11 ∣ Nat.card (Sylow 11 G) := not_dvd_card_sylow 11 G
  have hdvd88 : Nat.card (Sylow 11 G) ∣ 88 := by
    rw [← hG]
    exact P0.card_dvd_index.trans (Subgroup.index_dvd_card _)
  have h88 : 88 = 8 * 11 := by norm_num
  have hdvd8_mul : Nat.card (Sylow 11 G) ∣ 8 * 11 := by
    simpa [h88] using hdvd88
  have hp11 : Nat.Prime 11 := by norm_num
  have hcop : Nat.Coprime (Nat.card (Sylow 11 G)) 11 :=
    (hp11.coprime_iff_not_dvd.mpr hndvd_11).symm
  have hdvd8 : Nat.card (Sylow 11 G) ∣ 8 := hcop.dvd_of_dvd_mul_right hdvd8_mul
  have hmod := card_sylow_modEq_one 11 G
  have hle : Nat.card (Sylow 11 G) ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd8
  have hpos : 0 < Nat.card (Sylow 11 G) := Nat.card_pos
  have hlt : Nat.card (Sylow 11 G) < 11 := by omega
  unfold Nat.ModEq at hmod
  rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 1 < 11)] at hmod
  exact hmod

/-- The Sylow `11`-subgroup of a group of order `88` is normal. -/
theorem sylow_11_normal_of_card_88 [Finite G] (hG : Nat.card G = 88) (P : Sylow 11 G) :
    (↑P : Subgroup G).Normal := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  haveI : Subsingleton (Sylow 11 G) :=
    (Nat.card_eq_one_iff_unique.mp (card_sylow_11_eq_one_of_card_88 hG)).1
  exact normal_of_subsingleton P

/-- The Sylow `11`-subgroup of a group of order `88` has order `11`. -/
theorem card_sylow_11_subgroup_of_card_88 [Finite G] (hG : Nat.card G = 88)
    (P : Sylow 11 G) : Nat.card (↑P : Subgroup G) = 11 := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hndvd : ¬ 11 ∣ 8 := by norm_num
  have hfact : (88 : ℕ).factorization 11 = 1 := by
    rw [show 88 = 8 * 11 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hndvd,
      Nat.Prime.factorization_self (by norm_num : Nat.Prime 11), zero_add]
  rw [Sylow.card_eq_multiplicity, hG, hfact, pow_one]

/-- **Schur-Zassenhaus reduction for order `88`.**
Every group of order `88` is a semidirect product `N ⋊[φ] H`, where
`N` has order `11` and `H` has order `8`. -/
theorem order88_semidirectProduct [Finite G] (hG : Nat.card G = 88) :
    ∃ (N H : Subgroup G) (φ : H →* MulAut N),
      N.Normal ∧ Nat.card N = 11 ∧ Nat.card H = 8 ∧
        Nonempty (G ≃* SemidirectProduct N H φ) := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 11 G))
  haveI hnorm : (↑P0 : Subgroup G).Normal := sylow_11_normal_of_card_88 hG P0
  have hcardN : Nat.card (↑P0 : Subgroup G) = 11 :=
    card_sylow_11_subgroup_of_card_88 hG P0
  haveI : (↑P0 : Subgroup G).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
  have hcop : Nat.Coprime (Nat.card (↑P0 : Subgroup G)) (↑P0 : Subgroup G).index := by
    rw [hcardN]
    have := P0.not_dvd_index
    exact (show Nat.Prime 11 by norm_num).coprime_iff_not_dvd.mpr this
  obtain ⟨H, φ, ⟨e⟩⟩ := schurZassenhaus_semidirectProduct (↑P0 : Subgroup G) hcop
  have hcardH : Nat.card H = 8 := by
    have h1 : Nat.card G = Nat.card (↑P0 : Subgroup G) * Nat.card H := by
      rw [Nat.card_congr e.toEquiv, Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
    rw [hG, hcardN] at h1
    have h1' : 11 * Nat.card H = 11 * 8 := by omega
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 11) h1'
  exact ⟨↑P0, H, φ, hnorm, hcardN, hcardH, ⟨e⟩⟩

/-! ### Candidate representatives -/

/-- The normal subgroup in the order-`88` representatives. -/
abbrev order88_C11 : Type := CyclicRep 11

/-- `C₈`. -/
abbrev order88_C8 : Type := Multiplicative (ZMod 8)
/-- `C₄ × C₂`. -/
abbrev order88_C4C2 : Type := Multiplicative (ZMod 4) × Multiplicative (ZMod 2)
/-- `C₂ × C₂ × C₂`. -/
abbrev order88_C2C2C2 : Type :=
  Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)
/-- The dihedral group of order `8`. -/
abbrev order88_D8 : Type := DihedralGroup 4
/-- The quaternion group of order `8`. -/
abbrev order88_Q8 : Type := QuaternionGroup 2

/-- The reduction map `ZMod n → ZMod m`, viewed multiplicatively. -/
noncomputable def zmodCastMulHom {m n : ℕ} (h : m ∣ n) :
    Multiplicative (ZMod n) →* Multiplicative (ZMod m) :=
  AddMonoidHom.toMultiplicative (ZMod.castHom h (ZMod m)).toAddMonoidHom

/-! ### Automorphisms of `C₁₁` with 8-power equal to one -/

/-- The standard map from units of `ZMod 11` to automorphisms of `C₁₁` is injective. -/
theorem order88_unitAutHom_injective :
    Function.Injective (unitAutHom (p := 11)) := by
  intro u v h
  have h1 : unitAutHom u (Multiplicative.ofAdd (1 : ZMod 11)) =
      unitAutHom v (Multiplicative.ofAdd (1 : ZMod 11)) := by rw [h]
  simp only [unitAutHom_apply, mul_one, EmbeddingLike.apply_eq_iff_eq] at h1
  exact Units.ext h1

/-- Every automorphism of `C₁₁` is multiplication by a unit of `ZMod 11`. -/
theorem order88_mulAut_eq_unitAutHom (σ : MulAut order88_C11) :
    ∃ u : (ZMod 11)ˣ, σ = unitAutHom u := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  let u_val : ZMod 11 := (σ (Multiplicative.ofAdd (1 : ZMod 11))).toAdd
  have hu_ne_zero : u_val ≠ 0 := by
    intro hz
    have h0 : σ (Multiplicative.ofAdd (0 : ZMod 11)) = Multiplicative.ofAdd (0 : ZMod 11) := by
      calc
        σ (Multiplicative.ofAdd (0 : ZMod 11)) = σ 1 := by simp
        _ = 1 := map_one σ
        _ = Multiplicative.ofAdd (0 : ZMod 11) := by simp
    have h1 : σ (Multiplicative.ofAdd (1 : ZMod 11)) = Multiplicative.ofAdd (0 : ZMod 11) := by
      calc
        σ (Multiplicative.ofAdd (1 : ZMod 11)) = Multiplicative.ofAdd u_val := rfl
        _ = Multiplicative.ofAdd (0 : ZMod 11) := by rw [hz]
    have h01 : Multiplicative.ofAdd (0 : ZMod 11) ≠ Multiplicative.ofAdd (1 : ZMod 11) := by
      intro h
      apply_fun Multiplicative.toAdd at h
      simp at h
    apply h01
    exact σ.injective (h0.trans h1.symm)
  have h_inv : u_val⁻¹ * u_val = 1 := inv_mul_cancel₀ hu_ne_zero
  have h_mul : u_val * u_val⁻¹ = 1 := mul_inv_cancel₀ hu_ne_zero
  let u : (ZMod 11)ˣ := Units.mk u_val (u_val⁻¹) h_mul h_inv
  refine ⟨u, ?_⟩
  apply MulEquiv.ext
  intro x
  let n := Multiplicative.toAdd x
  have hx : Multiplicative.ofAdd n = x := ofAdd_toAdd x
  rw [← hx]
  calc
    σ (Multiplicative.ofAdd n) = σ ((Multiplicative.ofAdd (1 : ZMod 11)) ^ n.val) := by
      rw [show (Multiplicative.ofAdd n : Multiplicative (ZMod 11)) =
          (Multiplicative.ofAdd (1 : ZMod 11)) ^ n.val from by
        calc
          Multiplicative.ofAdd n = Multiplicative.ofAdd ((n.val : ZMod 11)) := by
            rw [ZMod.natCast_zmod_val]
          _ = Multiplicative.ofAdd (n.val • (1 : ZMod 11)) := by simp
          _ = (Multiplicative.ofAdd (1 : ZMod 11)) ^ n.val := by
            rw [ofAdd_nsmul]]
    _ = (σ (Multiplicative.ofAdd (1 : ZMod 11))) ^ n.val := by rw [map_pow]
    _ = (Multiplicative.ofAdd u_val) ^ n.val := rfl
    _ = Multiplicative.ofAdd (n.val • u_val) := by rw [← ofAdd_nsmul]
    _ = Multiplicative.ofAdd (u_val * (n.val : ZMod 11)) := by
      rw [nsmul_eq_mul, mul_comm]
    _ = Multiplicative.ofAdd (u_val * n) := by rw [ZMod.natCast_zmod_val]
    _ = unitAutHom u (Multiplicative.ofAdd n) := by rw [unitAutHom_apply]

/-- Multiplication by `-1` on `C₁₁` is inversion. -/
theorem order88_unitAutHom_neg_one :
    unitAutHom (-1 : (ZMod 11)ˣ) = invAut order88_C11 := by
  ext x
  obtain ⟨m, rfl⟩ := Multiplicative.ofAdd.surjective x
  rw [unitAutHom_apply, invAut_apply]
  simp

/-- A unit of `ZMod 11` whose eighth power is `1` is `1` or `-1`. -/
theorem order88_unit_pow8_eq_one (u : (ZMod 11)ˣ) (hu : u ^ 8 = 1) :
    u = 1 ∨ u = -1 := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have horder_dvd8 : orderOf u ∣ 8 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    exact hu
  have horder_dvd10 : orderOf u ∣ 10 := by
    have h := orderOf_dvd_card (x := u)
    rw [ZMod.card_units 11] at h
    norm_num at h ⊢
    exact h
  have horder_dvd2 : orderOf u ∣ 2 := by
    exact Nat.dvd_gcd horder_dvd8 horder_dvd10
  have horder_pos : 0 < orderOf u := orderOf_pos u
  have horder_cases : orderOf u = 1 ∨ orderOf u = 2 := by
    have hle : orderOf u ≤ 2 := Nat.le_of_dvd (by norm_num) horder_dvd2
    omega
  rcases horder_cases with h1 | h2
  · exact Or.inl (orderOf_eq_one_iff.mp h1)
  · right
    have hu2 : u ^ 2 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, h2]
    have hval_sq : ((u : ZMod 11) ^ 2) = 1 := by
      exact congrArg Units.val hu2
    have hprod : ((u : ZMod 11) - 1) * ((u : ZMod 11) + 1) = 0 := by
      calc
        ((u : ZMod 11) - 1) * ((u : ZMod 11) + 1) = (u : ZMod 11) ^ 2 - 1 := by ring
        _ = 0 := by rw [hval_sq]; ring
    rcases mul_eq_zero.mp hprod with hu_one | hu_neg
    · have : u = 1 := Units.ext (sub_eq_zero.mp hu_one)
      have hnot : orderOf u ≠ 1 := by omega
      exact (hnot (by rw [this]; simp)).elim
    · exact Units.ext (eq_neg_of_add_eq_zero_left hu_neg)

/-- Any automorphism of `C₁₁` whose eighth power is `1` is trivial or inversion. -/
theorem order88_mulAut_pow8_eq_one_or_inv (α : MulAut order88_C11) (hα : α ^ 8 = 1) :
    α = 1 ∨ α = invAut order88_C11 := by
  obtain ⟨u, hu⟩ := order88_mulAut_eq_unitAutHom α
  have hu8 : u ^ 8 = 1 := by
    apply order88_unitAutHom_injective
    rw [map_pow, ← hu, hα, map_one]
  rcases order88_unit_pow8_eq_one u hu8 with h1 | hneg
  · left
    rw [hu, h1, map_one]
  · right
    rw [hu, hneg, order88_unitAutHom_neg_one]

/-- If `H` has order `8`, every value of an action `H → Aut(C₁₁)` is trivial or inversion. -/
theorem order88_action_value_eq_one_or_inv {H : Type} [Group H] [Finite H]
    (hH : Nat.card H = 8) (φ : H →* MulAut order88_C11) (h : H) :
    φ h = 1 ∨ φ h = invAut order88_C11 := by
  apply order88_mulAut_pow8_eq_one_or_inv
  have hh8 : h ^ 8 = 1 := by
    simpa [hH] using (pow_card_eq_one' (x := h))
  rw [← map_pow, hh8, map_one]

/-- Inversion is not the identity automorphism of `C₁₁`. -/
theorem order88_invAut_ne_one : invAut order88_C11 ≠ 1 := by
  haveI : Fact (1 < 11) := ⟨by norm_num⟩
  intro h
  have hx := congrArg
    (fun f : MulAut order88_C11 => f (Multiplicative.ofAdd (1 : ZMod 11))) h
  have hx' : (Multiplicative.ofAdd (1 : ZMod 11))⁻¹ =
      Multiplicative.ofAdd (1 : ZMod 11) := by
    simpa [invAut_apply] using hx
  clear hx
  have hxadd : (-1 : ZMod 11) = 1 := by
    simpa using congrArg Multiplicative.toAdd hx'
  have hv := congrArg ZMod.val hxadd
  rw [ZMod.val_one] at hv
  norm_num at hv

/-- The character `H → C₂` attached to an order-`88` action `H → Aut(C₁₁)`. -/
noncomputable def order88_actionCharacter {H : Type} [Group H] [Finite H]
    (hH : Nat.card H = 8) (φ : H →* MulAut order88_C11) :
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
    rcases order88_action_value_eq_one_or_inv hH φ a with ha | ha <;>
      rcases order88_action_value_eq_one_or_inv hH φ b with hb | hb
    · have hab : φ (a * b) = 1 := by rw [map_mul, ha, hb, mul_one]
      simp [hab, ha, hb]
    · have hab : φ (a * b) = invAut order88_C11 := by rw [map_mul, ha, hb, one_mul]
      simp [hab, ha, hb, order88_invAut_ne_one]
    · have hab : φ (a * b) = invAut order88_C11 := by rw [map_mul, ha, hb, mul_one]
      simp [hab, ha, hb, order88_invAut_ne_one]
    · have hab : φ (a * b) = 1 := by
        rw [map_mul, ha, hb, ← sq, invAut_sq]
      simp only [hab, ha, hb, order88_invAut_ne_one, if_true, if_false]
      decide

/-- The unique non-trivial `C₈ → C₂` character, up to automorphism of `C₈`. -/
noncomputable abbrev order88_chiC8 : order88_C8 →* Multiplicative (ZMod 2) :=
  zmodCastMulHom (by norm_num : 2 ∣ 8)

/-- The `C₄ × C₂ → C₂` character non-trivial on the `C₄` factor. -/
noncomputable abbrev order88_chiC4C2_fst : order88_C4C2 →* Multiplicative (ZMod 2) :=
  (zmodCastMulHom (by norm_num : 2 ∣ 4)).comp
    (MonoidHom.fst (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2)))

/-- The `C₄ × C₂ → C₂` character non-trivial on the `C₂` factor. -/
noncomputable abbrev order88_chiC4C2_snd : order88_C4C2 →* Multiplicative (ZMod 2) :=
  MonoidHom.snd (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2))

/-- A representative non-trivial `C₂³ → C₂` character. -/
noncomputable abbrev order88_chiC2C2C2 : order88_C2C2C2 →* Multiplicative (ZMod 2) :=
  MonoidHom.fst (Multiplicative (ZMod 2))
    (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))

/-- The `D₈ → C₂` character non-trivial on rotations. -/
noncomputable def order88_chiD8_rot : order88_D8 →* Multiplicative (ZMod 2) where
  toFun
    | DihedralGroup.r i => Multiplicative.ofAdd ((ZMod.castHom (by norm_num : 2 ∣ 4)
        (ZMod 2)) i)
    | DihedralGroup.sr i => Multiplicative.ofAdd ((ZMod.castHom (by norm_num : 2 ∣ 4)
        (ZMod 2)) i)
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j)
    · simp [DihedralGroup.r_mul_r, map_add, ofAdd_add]
    · simp only [DihedralGroup.r_mul_sr]
      apply_fun Multiplicative.toAdd
      simp [toAdd_mul, sub_eq_add_neg, CharTwo.neg_eq]
      ac_rfl
    · simp [DihedralGroup.sr_mul_r, map_add, ofAdd_add]
    · simp only [DihedralGroup.sr_mul_sr]
      apply_fun Multiplicative.toAdd
      simp [toAdd_mul, sub_eq_add_neg, CharTwo.neg_eq]
      ac_rfl

/-- The `D₈ → C₂` character non-trivial on reflections. -/
noncomputable def order88_chiD8_ref : order88_D8 →* Multiplicative (ZMod 2) where
  toFun
    | DihedralGroup.r _ => 1
    | DihedralGroup.sr _ => Multiplicative.ofAdd (1 : ZMod 2)
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j)
    · rfl
    · rfl
    · rfl
    · simp only [DihedralGroup.sr_mul_sr]
      decide

/-- A representative non-trivial `Q₈ → C₂` character. -/
noncomputable def order88_chiQ8 : order88_Q8 →* Multiplicative (ZMod 2) where
  toFun
    | QuaternionGroup.a i => Multiplicative.ofAdd ((ZMod.castHom (by norm_num : 2 ∣ 4)
        (ZMod 2)) i)
    | QuaternionGroup.xa i => Multiplicative.ofAdd ((ZMod.castHom (by norm_num : 2 ∣ 4)
        (ZMod 2)) i)
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j)
    · simp [QuaternionGroup.a_mul_a, map_add, ofAdd_add]
    · simp only [QuaternionGroup.a_mul_xa]
      apply_fun Multiplicative.toAdd
      simp [toAdd_mul, sub_eq_add_neg, CharTwo.neg_eq]
      ac_rfl
    · simp [QuaternionGroup.xa_mul_a, map_add, ofAdd_add]
    · simp only [QuaternionGroup.xa_mul_xa]
      apply_fun Multiplicative.toAdd
      simp [toAdd_mul, sub_eq_add_neg, CharTwo.neg_eq]
      ac_rfl

/-- Turn a character `H → C₂` into the corresponding inversion action on `C₁₁`. -/
noncomputable abbrev order88_action {H : Type} [Group H]
    (χ : H →* Multiplicative (ZMod 2)) : H →* MulAut order88_C11 :=
  (invActionHom order88_C11).comp χ

/-- Every action `H → Aut(C₁₁)` with `|H| = 8` is induced by its character `H → C₂`. -/
theorem order88_action_eq_actionCharacter {H : Type} [Group H] [Finite H]
    (hH : Nat.card H = 8) (φ : H →* MulAut order88_C11) :
    φ = order88_action (order88_actionCharacter hH φ) := by
  ext h x
  rcases order88_action_value_eq_one_or_inv hH φ h with hh | hh
  · have hchi : order88_actionCharacter hH φ h = 1 := by
      classical
      simp [order88_actionCharacter, hh]
    simp [order88_action, hchi, hh]
  · have hchi : order88_actionCharacter hH φ h = Multiplicative.ofAdd (1 : ZMod 2) := by
      classical
      simp [order88_actionCharacter, hh, order88_invAut_ne_one]
    simp [order88_action, hchi, hh, invActionHom_gen]

/-- Semidirect-product representative attached to a character `χ : H → C₂`. -/
noncomputable abbrev order88_SD (H : Type) [Group H] (χ : H →* Multiplicative (ZMod 2)) :
    Type :=
  SemidirectProduct order88_C11 H (order88_action χ)

/-- Direct-product representative with complement `H`. -/
abbrev order88_DP (H : Type) : Type := order88_C11 × H

abbrev order88_RA : Type := order88_DP order88_C8
abbrev order88_RB : Type := order88_DP order88_C4C2
abbrev order88_RC : Type := order88_DP order88_C2C2C2
abbrev order88_RD : Type := order88_DP order88_D8
abbrev order88_RE : Type := order88_DP order88_Q8
noncomputable abbrev order88_RF : Type := order88_SD order88_C8 order88_chiC8
noncomputable abbrev order88_RG : Type := order88_SD order88_C4C2 order88_chiC4C2_fst
noncomputable abbrev order88_RH : Type := order88_SD order88_C4C2 order88_chiC4C2_snd
noncomputable abbrev order88_RI : Type := order88_SD order88_C2C2C2 order88_chiC2C2C2
noncomputable abbrev order88_RJ : Type := order88_SD order88_D8 order88_chiD8_rot
noncomputable abbrev order88_RK : Type := order88_SD order88_D8 order88_chiD8_ref
noncomputable abbrev order88_RL : Type := order88_SD order88_Q8 order88_chiQ8

/-! ### Cardinalities of the representatives -/

theorem card_order88_C11 : Nat.card order88_C11 = 11 := card_cyclicRep (by norm_num)

theorem card_order88_C8 : Nat.card order88_C8 = 8 := card_cyclicRep (by norm_num)

theorem card_order88_C4C2 : Nat.card order88_C4C2 = 8 := by
  rw [Nat.card_prod, card_cyclicRep (by norm_num : 4 ≠ 0),
    card_cyclicRep (by norm_num : 2 ≠ 0)]

theorem card_order88_C2C2C2 : Nat.card order88_C2C2C2 = 8 := by
  rw [Nat.card_prod, Nat.card_prod]
  norm_num [card_cyclicRep (by norm_num : 2 ≠ 0)]

theorem card_order88_D8 : Nat.card order88_D8 = 8 := by
  rw [DihedralGroup.nat_card]

theorem card_order88_Q8 : Nat.card order88_Q8 = 8 := by
  rw [P3Group.card_quaternion8]
  norm_num

theorem card_order88_DP {H : Type} [Group H] (hH : Nat.card H = 8) :
    Nat.card (order88_DP H) = 88 := by
  rw [order88_DP, Nat.card_prod, card_order88_C11, hH]

theorem card_order88_SD {H : Type} [Group H] (χ : H →* Multiplicative (ZMod 2))
    (hH : Nat.card H = 8) : Nat.card (order88_SD H χ) = 88 := by
  rw [order88_SD, SemidirectProduct.card, card_order88_C11, hH]

theorem card_order88_RA : Nat.card order88_RA = 88 := card_order88_DP card_order88_C8
theorem card_order88_RB : Nat.card order88_RB = 88 := card_order88_DP card_order88_C4C2
theorem card_order88_RC : Nat.card order88_RC = 88 := card_order88_DP card_order88_C2C2C2
theorem card_order88_RD : Nat.card order88_RD = 88 := card_order88_DP card_order88_D8
theorem card_order88_RE : Nat.card order88_RE = 88 := card_order88_DP card_order88_Q8
theorem card_order88_RF : Nat.card order88_RF = 88 :=
  card_order88_SD order88_chiC8 card_order88_C8
theorem card_order88_RG : Nat.card order88_RG = 88 :=
  card_order88_SD order88_chiC4C2_fst card_order88_C4C2
theorem card_order88_RH : Nat.card order88_RH = 88 :=
  card_order88_SD order88_chiC4C2_snd card_order88_C4C2
theorem card_order88_RI : Nat.card order88_RI = 88 :=
  card_order88_SD order88_chiC2C2C2 card_order88_C2C2C2
theorem card_order88_RJ : Nat.card order88_RJ = 88 :=
  card_order88_SD order88_chiD8_rot card_order88_D8
theorem card_order88_RK : Nat.card order88_RK = 88 :=
  card_order88_SD order88_chiD8_ref card_order88_D8
theorem card_order88_RL : Nat.card order88_RL = 88 :=
  card_order88_SD order88_chiQ8 card_order88_Q8

end Smallgroups.UsefulTheorems
