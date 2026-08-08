/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.Sylow
import Smallgroups.UsefulTheorems.Order80.UniqueSylowFive

/-!
# Groups of order 48 with a unique Sylow-3 subgroup: general machinery

This file handles the first branch of `order48_sylow_trichotomy`
(`Order48/Sylow.lean`): if a group `G` of order `48` has `n₃ = 1`, its unique
Sylow `3`-subgroup `N` is normal, and since `Nat.Coprime 3 16` the
Schur–Zassenhaus theorem splits `G` as a semidirect product `N ⋊[φ] K` with
`Nat.card N = 3` and `Nat.card K = 16`.

Compared with the order-`80` analogue (`Order80/UniqueSylowFive.lean`), the
situation is simpler in one key respect: `Aut(C₃) ≅ (ZMod 3)ˣ` has order `2`,
so every character `χ : K →* (ZMod 3)ˣ` is `±1`-valued, i.e. determined by an
index-`≤2` subgroup of `K` (its kernel).  The classification over each of the
fourteen order-`16` complement types (`order16_wild_reps`) is therefore an
orbit computation on index-`2` subgroups under `Aut K`.

* `order48_semidirectProduct_of_sylow_three_normal`: the reduction;
* `zmod3_unit_eq_one_or_neg`, `multiplicative_zmod_hom_ext`: the
  `(ZMod 3)ˣ`-character toolkit;
* `order48_signC2` / `order48_signC8` with their `_cases` lemmas: the
  nontrivial characters on the `C₂`- and `C₈`-factors;
* `order48_classify_G2` / `order48_classify_G3` / `order48_classify_G4`: the
  first per-kernel exhaustiveness step for the `C₈`-extension family
  (`SD₁₆`, `M₁₆`, `D₁₆`), in the same shape as `order80_classify_G*`; the
  orbit merges (`Aut K`-equivalent characters) are handled in the per-kernel
  files.
-/

namespace Smallgroups.UsefulTheorems

open Sylow

variable {G : Type*} [Group G]

/-- **Semidirect-product reduction for order `48` with a unique Sylow-`3`
subgroup.** If `G` has order `48` and its Sylow `3`-subgroup is normal, then
`G` is a semidirect product `N ⋊[φ] K`, where `N` has order `3` and `K` has
order `16`. -/
theorem order48_semidirectProduct_of_sylow_three_normal [Finite G] (hG : Nat.card G = 48)
    (hSyl : Nat.card (Sylow 3 G) = 1) :
    ∃ (N K : Subgroup G) (φ : K →* MulAut N),
      N.Normal ∧ Nat.card N = 3 ∧ Nat.card K = 16 ∧
        Nonempty (G ≃* SemidirectProduct N K φ) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 3 G))
  haveI hnorm : (↑P0 : Subgroup G).Normal := sylow_three_normal_of_card_sylow_three_eq_one hSyl P0
  have hcardN : Nat.card (↑P0 : Subgroup G) = 3 := card_sylow_three_subgroup_of_card_48 hG P0
  haveI : (↑P0 : Subgroup G).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
  have hcop : Nat.Coprime (Nat.card (↑P0 : Subgroup G)) (↑P0 : Subgroup G).index := by
    rw [hcardN]
    have := P0.not_dvd_index
    exact (show Nat.Prime 3 by norm_num).coprime_iff_not_dvd.mpr this
  obtain ⟨K, φ, ⟨e⟩⟩ := schurZassenhaus_semidirectProduct (↑P0 : Subgroup G) hcop
  have hcardK : Nat.card K = 16 := by
    have h1 : Nat.card G = Nat.card (↑P0 : Subgroup G) * Nat.card K := by
      rw [Nat.card_congr e.toEquiv, Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
    rw [hG, hcardN] at h1
    have h1' : 3 * Nat.card K = 3 * 16 := by omega
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3) h1'
  exact ⟨↑P0, K, φ, hnorm, hcardN, hcardK, ⟨e⟩⟩

/-! ### The `(ZMod 3)ˣ` character toolkit

Since `(ZMod 3)ˣ = {1, -1}`, every character of a group into `(ZMod 3)ˣ` is
`±1`-valued, hence determined by its values on generators. -/

/-- The units of `ZMod 3` are exactly `1` and `-1`. -/
theorem zmod3_unit_eq_one_or_neg (u : (ZMod 3)ˣ) : u = 1 ∨ u = -1 := by
  revert u; decide

/-- Homomorphisms out of `Multiplicative (ZMod n)` are determined by the value
on the additive generator `ofAdd 1`. -/
theorem multiplicative_zmod_hom_ext {n : ℕ} [NeZero n] {M : Type*} [Monoid M]
    {χ ψ : Multiplicative (ZMod n) →* M}
    (hgen : χ (Multiplicative.ofAdd (1 : ZMod n)) = ψ (Multiplicative.ofAdd (1 : ZMod n))) :
    χ = ψ := by
  apply MonoidHom.ext
  intro x
  rw [← ofAdd_one_pow_val x, map_pow, map_pow, hgen]

/-- The sign character `C₂ →* (ZMod 3)ˣ`, sending the generator to `-1`. -/
noncomputable abbrev order48_signC2 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ :=
  powHom (p := 3) (q := 2) (-1) (by decide)

@[simp]
theorem order48_signC2_gen : order48_signC2 (Multiplicative.ofAdd (1 : ZMod 2)) = -1 := by
  decide

/-- Characters `Multiplicative (ZMod 2) → (ZMod 3)ˣ` are trivial or `order48_signC2`. -/
theorem c2_zmod3_character_cases (χ : Multiplicative (ZMod 2) →* (ZMod 3)ˣ) :
    χ = 1 ∨ χ = order48_signC2 := by
  rcases zmod3_unit_eq_one_or_neg (χ (Multiplicative.ofAdd (1 : ZMod 2))) with h | h
  · exact Or.inl (c2_hom_ext (by simp [h]))
  · exact Or.inr (c2_hom_ext (by rw [h, order48_signC2_gen]))

/-- The sign character `C₄ →* (ZMod 3)ˣ`, sending the generator to `-1`. -/
noncomputable abbrev order48_signC4 : Multiplicative (ZMod 4) →* (ZMod 3)ˣ :=
  powHom (p := 3) (q := 4) (-1) (by decide)

@[simp]
theorem order48_signC4_gen : order48_signC4 (Multiplicative.ofAdd (1 : ZMod 4)) = -1 := by
  decide

/-- Characters `C₄ → (ZMod 3)ˣ` are trivial or `order48_signC4`. -/
theorem c4_zmod3_character_cases (χ : Multiplicative (ZMod 4) →* (ZMod 3)ˣ) :
    χ = 1 ∨ χ = order48_signC4 := by
  rcases zmod3_unit_eq_one_or_neg (χ (Multiplicative.ofAdd (1 : ZMod 4))) with h | h
  · exact Or.inl (multiplicative_zmod_hom_ext (by simp [h]))
  · exact Or.inr (multiplicative_zmod_hom_ext (by rw [h, order48_signC4_gen]))

/-- The sign character `C₈ →* (ZMod 3)ˣ`, sending the generator to `-1`. -/
noncomputable abbrev order48_signC8 : C8g →* (ZMod 3)ˣ :=
  powHom (p := 3) (q := 8) (-1) (by decide)

@[simp]
theorem order48_signC8_gen : order48_signC8 (Multiplicative.ofAdd (1 : ZMod 8)) = -1 := by
  decide

/-- Characters `C₈ → (ZMod 3)ˣ` are trivial or `order48_signC8`. -/
theorem c8_zmod3_character_cases (χ : C8g →* (ZMod 3)ˣ) :
    χ = 1 ∨ χ = order48_signC8 := by
  rcases zmod3_unit_eq_one_or_neg (χ (Multiplicative.ofAdd (1 : ZMod 8))) with h | h
  · exact Or.inl (multiplicative_zmod_hom_ext (by simp [h]))
  · exact Or.inr (multiplicative_zmod_hom_ext (by rw [h, order48_signC8_gen]))

/-- Turn a unit-valued character into the corresponding action on `C₃`. -/
noncomputable abbrev order48_action {H : Type*} [Group H] (χ : H →* (ZMod 3)ˣ) :
    H →* MulAut (Multiplicative (ZMod 3)) :=
  unitAutHom.comp χ

/-- Homomorphisms out of a direct product are determined by their values on
the two factor inclusions. -/
theorem prod_hom_ext {A B M : Type*} [Group A] [Group B] [Group M]
    {χ ψ : A × B →* M}
    (h1 : ∀ a, χ (a, 1) = ψ (a, 1)) (h2 : ∀ b, χ (1, b) = ψ (1, b)) :
    χ = ψ := by
  apply MonoidHom.ext
  rintro ⟨a, b⟩
  rw [show (a, b) = (a, 1) * (1, b) from by simp, map_mul, map_mul, h1, h2]

/-- An `Aut K`-precomposition of `(ZMod 3)ˣ`-valued characters yields
isomorphic semidirect products (the `(ZMod 3)ˣ` analogue of
`semidirectProduct_of_comp_eq`). -/
theorem order48_semidirectProduct_of_comp_eq {K : Type*} [Group K] {χ χ' : K →* (ZMod 3)ˣ}
    (σ : K ≃* K) (hχ : χ.comp σ.toMonoidHom = χ') :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) K (order48_action χ) ≃*
      SemidirectProduct (Multiplicative (ZMod 3)) K (order48_action χ')) := by
  have h : (order48_action χ).comp σ.toMonoidHom = order48_action χ' := by
    rw [order48_action, order48_action, MonoidHom.comp_assoc, hχ]
  exact ⟨(semidirectProductCongrAut σ).symm.trans (semidirectProductCongr_eq h)⟩

/-! ### The `C₈`-extension family (`G₂ = SD₁₆`, `G₃ = M₁₆`, `G₄ = D₁₆`)

For all three kernels, the relation `b a b⁻¹ = a^m` with `m` odd imposes no
constraint on a `±1`-valued character: `χ(a)^m = χ(a)` holds automatically
since `χ(a)² = 1`.  Hence every character is an independent choice of a sign
on the `C₈`-part and a sign on the `C₂`-part.  (The orbit structure differs
per kernel — e.g. `SD₁₆` has all three index-`2` subgroups characteristic,
while `D₁₆`'s two dihedral index-`2` subgroups are `Aut`-conjugate — and is
handled in the per-kernel reduced theorems.) -/

/-- **Exhaustiveness for `K = SD₁₆` (`G₂`, action `φ₂ : x ↦ x³`).** -/
theorem order48_classify_G2 (φ' : order16_wild_G2 →* MulAut (Multiplicative (ZMod 3))) :
    ∃ χ : order16_wild_G2 →* (ZMod 3)ˣ,
      (χ.comp SemidirectProduct.inl = 1 ∨ χ.comp SemidirectProduct.inl = order48_signC8) ∧
      (χ.comp SemidirectProduct.inr = 1 ∨ χ.comp SemidirectProduct.inr = order48_signC2) ∧
      Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G2 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G2 (order48_action χ)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨ψ, hψ⟩ := exists_unitAutHom_comp_eq φ'
  exact ⟨ψ, c8_zmod3_character_cases _, c2_zmod3_character_cases _,
    ⟨semidirectProductCongr_eq hψ⟩⟩

/-- **Exhaustiveness for `K = M₁₆` (`G₃`, action `φ₃ : x ↦ x⁵`).** -/
theorem order48_classify_G3 (φ' : order16_wild_G3 →* MulAut (Multiplicative (ZMod 3))) :
    ∃ χ : order16_wild_G3 →* (ZMod 3)ˣ,
      (χ.comp SemidirectProduct.inl = 1 ∨ χ.comp SemidirectProduct.inl = order48_signC8) ∧
      (χ.comp SemidirectProduct.inr = 1 ∨ χ.comp SemidirectProduct.inr = order48_signC2) ∧
      Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G3 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G3 (order48_action χ)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨ψ, hψ⟩ := exists_unitAutHom_comp_eq φ'
  exact ⟨ψ, c8_zmod3_character_cases _, c2_zmod3_character_cases _,
    ⟨semidirectProductCongr_eq hψ⟩⟩

/-- **Exhaustiveness for `K = D₁₆` (`G₄`, action `φ₄ : x ↦ x⁷`, inversion).** -/
theorem order48_classify_G4 (φ' : order16_wild_G4 →* MulAut (Multiplicative (ZMod 3))) :
    ∃ χ : order16_wild_G4 →* (ZMod 3)ˣ,
      (χ.comp SemidirectProduct.inl = 1 ∨ χ.comp SemidirectProduct.inl = order48_signC8) ∧
      (χ.comp SemidirectProduct.inr = 1 ∨ χ.comp SemidirectProduct.inr = order48_signC2) ∧
      Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G4 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G4 (order48_action χ)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨ψ, hψ⟩ := exists_unitAutHom_comp_eq φ'
  exact ⟨ψ, c8_zmod3_character_cases _, c2_zmod3_character_cases _,
    ⟨semidirectProductCongr_eq hψ⟩⟩

end Smallgroups.UsefulTheorems
