/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order88

/-!
# First reductions for groups of order 56

Since `56 = 8 * 7`, either the Sylow `7`-subgroup is normal, giving
`C₇ ⋊ H` with `|H| = 8`, or the Sylow `2`-subgroup is normal.  The normal
Sylow `7` branch is parallel to the order-`88` classification.  The remaining
branch contributes the extra representative `(C₂)^3 ⋊ C₇`.
-/

namespace Smallgroups.UsefulTheorems

open Sylow
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ### Sylow-7 normal branch -/

/-- In a group of order `56`, the number of Sylow `7`-subgroups is `1` or `8`. -/
theorem card_sylow_7_eq_one_or_eight_of_card_56 [Finite G] (hG : Nat.card G = 56) :
    Nat.card (Sylow 7 G) = 1 ∨ Nat.card (Sylow 7 G) = 8 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 7 G))
  have hndvd_7 : ¬ 7 ∣ Nat.card (Sylow 7 G) := not_dvd_card_sylow 7 G
  have hdvd56 : Nat.card (Sylow 7 G) ∣ 56 := by
    rw [← hG]
    exact P0.card_dvd_index.trans (Subgroup.index_dvd_card _)
  have h56 : 56 = 8 * 7 := by norm_num
  have hdvd8_mul : Nat.card (Sylow 7 G) ∣ 8 * 7 := by
    simpa [h56] using hdvd56
  have hp7 : Nat.Prime 7 := by norm_num
  have hcop : Nat.Coprime (Nat.card (Sylow 7 G)) 7 :=
    (hp7.coprime_iff_not_dvd.mpr hndvd_7).symm
  have hdvd8 : Nat.card (Sylow 7 G) ∣ 8 := hcop.dvd_of_dvd_mul_right hdvd8_mul
  have hmod := card_sylow_modEq_one 7 G
  have hle : Nat.card (Sylow 7 G) ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd8
  have hpos : 0 < Nat.card (Sylow 7 G) := Nat.card_pos
  interval_cases h : Nat.card (Sylow 7 G)
  · exact Or.inl rfl
  · unfold Nat.ModEq at hmod; norm_num at hmod
  · norm_num at hdvd8
  · unfold Nat.ModEq at hmod; norm_num at hmod
  · norm_num at hdvd8
  · norm_num at hdvd8
  · norm_num at hdvd8
  · exact Or.inr rfl

/-- If there is a unique Sylow `7`-subgroup, it is normal. -/
theorem sylow_7_normal_of_card_56_of_card_sylow_eq_one [Finite G]
    (hSyl : Nat.card (Sylow 7 G) = 1) (P : Sylow 7 G) :
    (↑P : Subgroup G).Normal := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Subsingleton (Sylow 7 G) := (Nat.card_eq_one_iff_unique.mp hSyl).1
  exact normal_of_subsingleton P

/-- A Sylow `7`-subgroup of a group of order `56` has order `7`. -/
theorem card_sylow_7_subgroup_of_card_56 [Finite G] (hG : Nat.card G = 56)
    (P : Sylow 7 G) : Nat.card (↑P : Subgroup G) = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hndvd : ¬ 7 ∣ 8 := by norm_num
  have hfact : (56 : ℕ).factorization 7 = 1 := by
    rw [show 56 = 8 * 7 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hndvd,
      Nat.Prime.factorization_self (by norm_num : Nat.Prime 7), zero_add]
  rw [Sylow.card_eq_multiplicity, hG, hfact, pow_one]

/-- **Schur-Zassenhaus reduction for the normal Sylow-`7` branch of order `56`.** -/
theorem order56_semidirectProduct_of_card_sylow_7_eq_one [Finite G] (hG : Nat.card G = 56)
    (hSyl : Nat.card (Sylow 7 G) = 1) :
    ∃ (N H : Subgroup G) (φ : H →* MulAut N),
      N.Normal ∧ Nat.card N = 7 ∧ Nat.card H = 8 ∧
        Nonempty (G ≃* SemidirectProduct N H φ) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 7 G))
  haveI hnorm : (↑P0 : Subgroup G).Normal :=
    sylow_7_normal_of_card_56_of_card_sylow_eq_one hSyl P0
  have hcardN : Nat.card (↑P0 : Subgroup G) = 7 :=
    card_sylow_7_subgroup_of_card_56 hG P0
  haveI : (↑P0 : Subgroup G).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
  have hcop : Nat.Coprime (Nat.card (↑P0 : Subgroup G)) (↑P0 : Subgroup G).index := by
    rw [hcardN]
    have := P0.not_dvd_index
    exact (show Nat.Prime 7 by norm_num).coprime_iff_not_dvd.mpr this
  obtain ⟨H, φ, ⟨e⟩⟩ := schurZassenhaus_semidirectProduct (↑P0 : Subgroup G) hcop
  have hcardH : Nat.card H = 8 := by
    have h1 : Nat.card G = Nat.card (↑P0 : Subgroup G) * Nat.card H := by
      rw [Nat.card_congr e.toEquiv, Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
    rw [hG, hcardN] at h1
    have h1' : 7 * Nat.card H = 7 * 8 := by omega
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 7) h1'
  exact ⟨↑P0, H, φ, hnorm, hcardN, hcardH, ⟨e⟩⟩

/-! ### The non-normal Sylow-`7` branch begins as a faithful permutation action -/

/-- If there are eight Sylow `7`-subgroups, each Sylow `7`-subgroup is self-normalizing. -/
theorem sylow_7_eq_normalizer_of_card_56_of_card_sylow_7_eq_eight [Finite G]
    (hG : Nat.card G = 56) (hSyl : Nat.card (Sylow 7 G) = 8) (P : Sylow 7 G) :
    (↑P : Subgroup G) = Subgroup.normalizer (P : Set G) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hcardP : Nat.card (↑P : Subgroup G) = 7 :=
    card_sylow_7_subgroup_of_card_56 hG P
  have hidx : (Subgroup.normalizer (P : Set G)).index = 8 := by
    rwa [← Sylow.card_eq_index_normalizer P]
  have hcardNorm : Nat.card (Subgroup.normalizer (P : Set G)) = 7 := by
    have := (Subgroup.normalizer (P : Set G)).card_mul_index
    rw [hidx, hG] at this
    omega
  exact Subgroup.eq_of_le_of_card_ge Subgroup.le_normalizer (by rw [hcardNorm, hcardP])

/-- If there are eight Sylow `7`-subgroups, the conjugation action on them is faithful. -/
theorem sylow_7_conj_action_injective_of_card_56_of_card_sylow_7_eq_eight [Finite G]
    (hG : Nat.card G = 56) (hSyl : Nat.card (Sylow 7 G) = 8) :
    Function.Injective (MulAction.toPermHom G (Sylow 7 G)) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 7 G))
  rw [← MonoidHom.ker_eq_bot_iff]
  have hP_eq_norm :
      (↑P0 : Subgroup G) = Subgroup.normalizer (P0 : Set G) :=
    sylow_7_eq_normalizer_of_card_56_of_card_sylow_7_eq_eight hG hSyl P0
  have hker_le : (MulAction.toPermHom G (Sylow 7 G)).ker ≤ ↑P0 := by
    intro g hg
    rw [hP_eq_norm]
    have hg_ker := MonoidHom.mem_ker.mp hg
    rw [← Sylow.stabilizer_eq_normalizer]
    rw [MulAction.mem_stabilizer_iff]
    exact Equiv.Perm.ext_iff.mp hg_ker P0
  by_contra hker
  have hcardP : Nat.card (↑P0 : Subgroup G) = 7 :=
    card_sylow_7_subgroup_of_card_56 hG P0
  have hker_card_dvd : Nat.card (MulAction.toPermHom G (Sylow 7 G)).ker ∣
      Nat.card (↑P0 : Subgroup G) :=
    Subgroup.card_dvd_of_le hker_le
  rw [hcardP] at hker_card_dvd
  have hker_card_gt : 1 < Nat.card (MulAction.toPermHom G (Sylow 7 G)).ker :=
    (Subgroup.one_lt_card_iff_ne_bot _).mpr hker
  have hker_card : Nat.card (MulAction.toPermHom G (Sylow 7 G)).ker = 7 := by
    have hle := Nat.le_of_dvd (by omega) hker_card_dvd
    have : Nat.card (MulAction.toPermHom G (Sylow 7 G)).ker = 2 ∨
        Nat.card (MulAction.toPermHom G (Sylow 7 G)).ker = 3 ∨
        Nat.card (MulAction.toPermHom G (Sylow 7 G)).ker = 4 ∨
        Nat.card (MulAction.toPermHom G (Sylow 7 G)).ker = 5 ∨
        Nat.card (MulAction.toPermHom G (Sylow 7 G)).ker = 6 ∨
        Nat.card (MulAction.toPermHom G (Sylow 7 G)).ker = 7 := by
      omega
    rcases this with h | h | h | h | h | h
    · exact absurd (h ▸ hker_card_dvd) (by norm_num)
    · exact absurd (h ▸ hker_card_dvd) (by norm_num)
    · exact absurd (h ▸ hker_card_dvd) (by norm_num)
    · exact absurd (h ▸ hker_card_dvd) (by norm_num)
    · exact absurd (h ▸ hker_card_dvd) (by norm_num)
    · exact h
  have hker_eq : (MulAction.toPermHom G (Sylow 7 G)).ker = ↑P0 :=
    Subgroup.eq_of_le_of_card_ge hker_le (by rw [hcardP, hker_card])
  haveI : (↑P0 : Subgroup G).Normal :=
    hker_eq ▸ MonoidHom.normal_ker (MulAction.toPermHom G (Sylow 7 G))
  haveI := Sylow.unique_of_normal P0 (by assumption)
  have : Nat.card (Sylow 7 G) = 1 := Nat.card_unique
  omega

theorem sylow_7_normalizer_le_centralizer_of_card_56_of_card_sylow_7_eq_eight [Finite G]
    (hG : Nat.card G = 56) (hSyl : Nat.card (Sylow 7 G) = 8) (P : Sylow 7 G) :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.centralizer (P : Set G) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hnorm :
      (↑P : Subgroup G) = Subgroup.normalizer (P : Set G) :=
    sylow_7_eq_normalizer_of_card_56_of_card_sylow_7_eq_eight hG hSyl P
  have hcardP : Nat.card (↑P : Subgroup G) = 7 :=
    card_sylow_7_subgroup_of_card_56 hG P
  have hcyc : IsCyclic (↑P : Subgroup G) := isCyclic_of_prime_card hcardP
  letI : CommGroup (↑P : Subgroup G) := IsCyclic.commGroup
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hgP : g ∈ (↑P : Subgroup G) := by
    rw [hnorm]
    exact hg
  have hcomm := mul_comm (⟨y, hy⟩ : (↑P : Subgroup G)) ⟨g, hgP⟩
  simpa using congrArg Subtype.val hcomm

/-- If there are eight Sylow `7`-subgroups, Burnside transfer gives a normal `7`-complement. -/
theorem order56_normal_7_complement_of_card_sylow_7_eq_eight [Finite G]
    (hG : Nat.card G = 56) (hSyl : Nat.card (Sylow 7 G) = 8) :
    ∃ (N H : Subgroup G), N.Normal ∧ N.IsComplement' H ∧ Nat.card N = 8 ∧ Nat.card H = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 7 G))
  let hcent : Subgroup.normalizer (P0 : Set G) ≤ Subgroup.centralizer (P0 : Set G) :=
    sylow_7_normalizer_le_centralizer_of_card_56_of_card_sylow_7_eq_eight hG hSyl P0
  let N : Subgroup G := (MonoidHom.transferSylow P0 hcent).ker
  haveI : N.Normal := MonoidHom.normal_ker (MonoidHom.transferSylow P0 hcent)
  have hcomp : N.IsComplement' (↑P0 : Subgroup G) :=
    MonoidHom.ker_transferSylow_isComplement' P0 hcent
  have hcardH : Nat.card (↑P0 : Subgroup G) = 7 :=
    card_sylow_7_subgroup_of_card_56 hG P0
  have hcardN : Nat.card N = 8 := by
    have hmul := hcomp.card_mul
    rw [hcardH, hG] at hmul
    omega
  exact ⟨N, ↑P0, inferInstance, hcomp, hcardN, hcardH⟩

/-- **Semidirect-product reduction for the non-normal Sylow-`7` branch of order `56`.** -/
theorem order56_semidirectProduct_of_card_sylow_7_eq_eight [Finite G]
    (hG : Nat.card G = 56) (hSyl : Nat.card (Sylow 7 G) = 8) :
    ∃ (N H : Subgroup G) (φ : H →* MulAut N),
      N.Normal ∧ Nat.card N = 8 ∧ Nat.card H = 7 ∧
        Nonempty (G ≃* SemidirectProduct N H φ) := by
  obtain ⟨N, H, hN, hcomp, hcardN, hcardH⟩ :=
    order56_normal_7_complement_of_card_sylow_7_eq_eight hG hSyl
  haveI : N.Normal := hN
  exact ⟨N, H, _, hN, hcardN, hcardH, ⟨(SemidirectProduct.mulEquivSubgroup hcomp).symm⟩⟩

/-! ### Candidate representatives -/

/-- The cyclic group `C₇`. -/
abbrev order56_C7 : Type := CyclicRep 7

abbrev order56_C8 : Type := order88_C8
abbrev order56_C4C2 : Type := order88_C4C2
abbrev order56_C2C2C2 : Type := order88_C2C2C2
abbrev order56_D8 : Type := order88_D8
abbrev order56_Q8 : Type := order88_Q8

/-! ### Automorphisms of `C₇` with 8-power equal to one -/

/-- Multiplication by `-1` on `C₇` is inversion. -/
theorem order56_unitAutHom_neg_one :
    unitAutHom (-1 : (ZMod 7)ˣ) = invAut order56_C7 := by
  ext x
  obtain ⟨m, rfl⟩ := Multiplicative.ofAdd.surjective x
  rw [unitAutHom_apply, invAut_apply]
  simp

/-- A unit of `ZMod 7` whose eighth power is `1` is `1` or `-1`. -/
theorem order56_unit_pow8_eq_one (u : (ZMod 7)ˣ) (hu : u ^ 8 = 1) :
    u = 1 ∨ u = -1 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have horder_dvd8 : orderOf u ∣ 8 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    exact hu
  have horder_dvd6 : orderOf u ∣ 6 := by
    have h := orderOf_dvd_card (x := u)
    rw [ZMod.card_units 7] at h
    norm_num at h ⊢
    exact h
  have horder_dvd2 : orderOf u ∣ 2 := by
    exact Nat.dvd_gcd horder_dvd8 horder_dvd6
  have horder_pos : 0 < orderOf u := orderOf_pos u
  have horder_cases : orderOf u = 1 ∨ orderOf u = 2 := by
    have hle : orderOf u ≤ 2 := Nat.le_of_dvd (by norm_num) horder_dvd2
    omega
  rcases horder_cases with h1 | h2
  · exact Or.inl (orderOf_eq_one_iff.mp h1)
  · right
    have hu2 : u ^ 2 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, h2]
    have hval_sq : ((u : ZMod 7) ^ 2) = 1 := congrArg Units.val hu2
    have hprod : ((u : ZMod 7) - 1) * ((u : ZMod 7) + 1) = 0 := by
      calc
        ((u : ZMod 7) - 1) * ((u : ZMod 7) + 1) = (u : ZMod 7) ^ 2 - 1 := by ring
        _ = 0 := by rw [hval_sq]; ring
    rcases mul_eq_zero.mp hprod with hu_one | hu_neg
    · have : u = 1 := Units.ext (sub_eq_zero.mp hu_one)
      have hnot : orderOf u ≠ 1 := by omega
      exact (hnot (by rw [this]; simp)).elim
    · exact Units.ext (eq_neg_of_add_eq_zero_left hu_neg)

/-- Any automorphism of `C₇` whose eighth power is `1` is trivial or inversion. -/
theorem order56_mulAut_pow8_eq_one_or_inv (α : MulAut order56_C7) (hα : α ^ 8 = 1) :
    α = 1 ∨ α = invAut order56_C7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨u, hu⟩ := exists_unitAutHom_eq (p := 7) α
  have hu8 : u ^ 8 = 1 := by
    apply unitAutHom_injective (p := 7)
    rw [map_pow, ← hu, hα, map_one]
  rcases order56_unit_pow8_eq_one u hu8 with h1 | hneg
  · left
    rw [hu, h1, map_one]
  · right
    rw [hu, hneg, order56_unitAutHom_neg_one]

/-- If `H` has order `8`, every value of an action `H → Aut(C₇)` is trivial or inversion. -/
theorem order56_action_value_eq_one_or_inv {H : Type} [Group H] [Finite H]
    (hH : Nat.card H = 8) (φ : H →* MulAut order56_C7) (h : H) :
    φ h = 1 ∨ φ h = invAut order56_C7 := by
  apply order56_mulAut_pow8_eq_one_or_inv
  have hh8 : h ^ 8 = 1 := by
    simpa [hH] using (pow_card_eq_one' (x := h))
  rw [← map_pow, hh8, map_one]

/-- Inversion is not the identity automorphism of `C₇`. -/
theorem order56_invAut_ne_one : invAut order56_C7 ≠ 1 := by
  haveI : Fact (1 < 7) := ⟨by norm_num⟩
  intro h
  have hx := congrArg
    (fun f : MulAut order56_C7 => f (Multiplicative.ofAdd (1 : ZMod 7))) h
  have hx' : (Multiplicative.ofAdd (1 : ZMod 7))⁻¹ =
      Multiplicative.ofAdd (1 : ZMod 7) := by
    simpa [invAut_apply] using hx
  clear hx
  have hxadd : (-1 : ZMod 7) = 1 := by
    simpa using congrArg Multiplicative.toAdd hx'
  have hv := congrArg ZMod.val hxadd
  rw [ZMod.val_one] at hv
  norm_num at hv

/-- The character `H → C₂` attached to an order-`56` action `H → Aut(C₇)`. -/
noncomputable def order56_actionCharacter {H : Type} [Group H] [Finite H]
    (hH : Nat.card H = 8) (φ : H →* MulAut order56_C7) :
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
    rcases order56_action_value_eq_one_or_inv hH φ a with ha | ha <;>
      rcases order56_action_value_eq_one_or_inv hH φ b with hb | hb
    · have hab : φ (a * b) = 1 := by rw [map_mul, ha, hb, mul_one]
      simp [hab, ha, hb]
    · have hab : φ (a * b) = invAut order56_C7 := by rw [map_mul, ha, hb, one_mul]
      simp [hab, ha, hb, order56_invAut_ne_one]
    · have hab : φ (a * b) = invAut order56_C7 := by rw [map_mul, ha, hb, mul_one]
      simp [hab, ha, hb, order56_invAut_ne_one]
    · have hab : φ (a * b) = 1 := by
        rw [map_mul, ha, hb, ← sq, invAut_sq]
      simp only [hab, ha, hb, order56_invAut_ne_one, if_true, if_false]
      decide

/-- Turn a character `H → C₂` into the corresponding inversion action on `C₇`. -/
noncomputable abbrev order56_action {H : Type} [Group H]
    (χ : H →* Multiplicative (ZMod 2)) : H →* MulAut order56_C7 :=
  (invActionHom order56_C7).comp χ

/-- Precomposing a character by an automorphism precomposes the corresponding action. -/
theorem order56_action_comp {H : Type} [Group H] {χ ψ : H →* Multiplicative (ZMod 2)}
    (σ : H ≃* H) (hχ : χ.comp σ.toMonoidHom = ψ) :
    (order56_action χ).comp σ.toMonoidHom = order56_action ψ := by
  ext h x
  change (invActionHom order56_C7) (χ (σ h)) x = (invActionHom order56_C7) (ψ h) x
  rw [show χ (σ h) = ψ h from congrArg (fun f : H →* Multiplicative (ZMod 2) => f h) hχ]

/-- Every action `H → Aut(C₇)` with `|H| = 8` is induced by its character `H → C₂`. -/
theorem order56_action_eq_actionCharacter {H : Type} [Group H] [Finite H]
    (hH : Nat.card H = 8) (φ : H →* MulAut order56_C7) :
    φ = order56_action (order56_actionCharacter hH φ) := by
  ext h x
  rcases order56_action_value_eq_one_or_inv hH φ h with hh | hh
  · have hchi : order56_actionCharacter hH φ h = 1 := by
      classical
      simp [order56_actionCharacter, hh]
    simp [order56_action, hchi, hh]
  · have hchi : order56_actionCharacter hH φ h = Multiplicative.ofAdd (1 : ZMod 2) := by
      classical
      simp [order56_actionCharacter, hh, order56_invAut_ne_one]
    simp [order56_action, hchi, hh, invActionHom_gen]

theorem order56_c8_action_cases (φ : order56_C8 →* MulAut order56_C7) :
    φ = 1 ∨ φ = order56_action order88_chiC8 := by
  have hcard : Nat.card order56_C8 = 8 := card_cyclicRep (by norm_num)
  have hφ := order56_action_eq_actionCharacter hcard φ
  rcases order88_c8_character_cases (order56_actionCharacter hcard φ) with hχ | hχ
  · left
    rw [hφ, hχ]
    rfl
  · right
    rw [hφ, hχ]

theorem order56_c4c2_action_cases (φ : order56_C4C2 →* MulAut order56_C7) :
    φ = 1 ∨ φ = order56_action order88_chiC4C2_fst ∨
      φ = order56_action order88_chiC4C2_snd ∨
      φ = order56_action order88_chiC4C2_prod := by
  have hcard : Nat.card order56_C4C2 = 8 := by
    rw [Nat.card_prod, card_cyclicRep (by norm_num : 4 ≠ 0),
      card_cyclicRep (by norm_num : 2 ≠ 0)]
  have hφ := order56_action_eq_actionCharacter hcard φ
  rcases order88_c4c2_character_cases (order56_actionCharacter hcard φ) with
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

theorem order56_c2c2c2_action_cases (φ : order56_C2C2C2 →* MulAut order56_C7) :
    φ = 1 ∨ φ = order56_action order88_chiC2C2C2 ∨
      φ = order56_action order88_chiC2C2C2_snd ∨
      φ = order56_action order88_chiC2C2C2_trd ∨
      φ = order56_action order88_chiC2C2C2_fst_snd ∨
      φ = order56_action order88_chiC2C2C2_fst_trd ∨
      φ = order56_action order88_chiC2C2C2_snd_trd ∨
      φ = order56_action order88_chiC2C2C2_fst_snd_trd := by
  have hcard : Nat.card order56_C2C2C2 = 8 := by
    rw [Nat.card_prod, Nat.card_prod]
    norm_num [card_cyclicRep (by norm_num : 2 ≠ 0)]
  have hφ := order56_action_eq_actionCharacter hcard φ
  rcases order88_c2c2c2_character_cases (order56_actionCharacter hcard φ) with
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

theorem order56_d8_action_cases (φ : order56_D8 →* MulAut order56_C7) :
    φ = 1 ∨ φ = order56_action order88_chiD8_rot ∨
      φ = order56_action order88_chiD8_ref ∨
      φ = order56_action order88_chiD8_prod := by
  have hcard : Nat.card order56_D8 = 8 := by rw [DihedralGroup.nat_card]
  have hφ := order56_action_eq_actionCharacter hcard φ
  rcases order88_d8_character_cases (order56_actionCharacter hcard φ) with hχ | hχ | hχ | hχ
  · left
    rw [hφ, hχ]
    rfl
  · right; left
    rw [hφ, hχ]
  · right; right; left
    rw [hφ, hχ]
  · right; right; right
    rw [hφ, hχ]

theorem order56_q8_action_cases (φ : order56_Q8 →* MulAut order56_C7) :
    φ = 1 ∨ φ = order56_action order88_chiQ8 ∨
      φ = order56_action order88_chiQ8_xa ∨
      φ = order56_action order88_chiQ8_prod := by
  have hcard : Nat.card order56_Q8 = 8 := by
    rw [P3Group.card_quaternion8]
    norm_num
  have hφ := order56_action_eq_actionCharacter hcard φ
  rcases order88_q8_character_cases (order56_actionCharacter hcard φ) with hχ | hχ | hχ | hχ
  · left
    rw [hφ, hχ]
    rfl
  · right; left
    rw [hφ, hχ]
  · right; right; left
    rw [hφ, hχ]
  · right; right; right
    rw [hφ, hχ]

/-! ### Displayed representatives -/

/-- Semidirect-product representative attached to a character `χ : H → C₂`. -/
noncomputable abbrev order56_SD (H : Type) [Group H] (χ : H →* Multiplicative (ZMod 2)) :
    Type :=
  SemidirectProduct order56_C7 H (order56_action χ)

noncomputable instance instFintypeOrder56SD {H : Type} [Group H] [Fintype H]
    (χ : H →* Multiplicative (ZMod 2)) : Fintype (order56_SD H χ) :=
  Fintype.ofEquiv (order56_C7 × H) SemidirectProduct.equivProd.symm

/-- Precomposing a character by an automorphism gives an isomorphic semidirect product. -/
noncomputable def order56_SD_equiv_of_character_comp {H : Type} [Group H]
    (χ ψ : H →* Multiplicative (ZMod 2)) (σ : H ≃* H)
    (hχ : χ.comp σ.toMonoidHom = ψ) :
    order56_SD H ψ ≃* order56_SD H χ := by
  have haction :
      (order56_action χ).comp σ.toMonoidHom = order56_action ψ :=
    order56_action_comp σ hχ
  exact (semidirectProductCongr_eq haction.symm).trans
    (semidirectProductCongrAut (N := order56_C7) (φ := order56_action χ) σ)

noncomputable def order56_c4c2_prod_equiv_snd :
    order56_SD order56_C4C2 order88_chiC4C2_prod ≃*
      order56_SD order56_C4C2 order88_chiC4C2_snd := by
  have haction :
      (order56_action order88_chiC4C2_snd).comp order88_C4C2_shear.toMonoidHom =
        order56_action order88_chiC4C2_prod :=
    order56_action_comp order88_C4C2_shear order88_chiC4C2_snd_comp_shear
  exact (semidirectProductCongr_eq haction.symm).trans
    (semidirectProductCongrAut (N := order56_C7)
      (φ := order56_action order88_chiC4C2_snd) order88_C4C2_shear)

noncomputable def order56_d8_prod_equiv_rot :
    order56_SD order56_D8 order88_chiD8_prod ≃*
      order56_SD order56_D8 order88_chiD8_rot := by
  have haction :
      (order56_action order88_chiD8_rot).comp order88_D8_shear.toMonoidHom =
        order56_action order88_chiD8_prod :=
    order56_action_comp order88_D8_shear order88_chiD8_rot_comp_shear
  exact (semidirectProductCongr_eq haction.symm).trans
    (semidirectProductCongrAut (N := order56_C7)
      (φ := order56_action order88_chiD8_rot) order88_D8_shear)

noncomputable def order56_q8_prod_equiv_q8 :
    order56_SD order56_Q8 order88_chiQ8_prod ≃*
      order56_SD order56_Q8 order88_chiQ8 := by
  have haction :
      (order56_action order88_chiQ8).comp order88_Q8_shear.toMonoidHom =
        order56_action order88_chiQ8_prod :=
    order56_action_comp order88_Q8_shear order88_chiQ8_comp_shear
  exact (semidirectProductCongr_eq haction.symm).trans
    (semidirectProductCongrAut (N := order56_C7)
      (φ := order56_action order88_chiQ8) order88_Q8_shear)

noncomputable def order56_q8_xa_equiv_q8 :
    order56_SD order56_Q8 order88_chiQ8_xa ≃*
      order56_SD order56_Q8 order88_chiQ8 := by
  have haction :
      (order56_action order88_chiQ8).comp order88_Q8_swap.toMonoidHom =
        order56_action order88_chiQ8_xa :=
    order56_action_comp order88_Q8_swap order88_chiQ8_comp_swap
  exact (semidirectProductCongr_eq haction.symm).trans
    (semidirectProductCongrAut (N := order56_C7)
      (φ := order56_action order88_chiQ8) order88_Q8_swap)

noncomputable def order56_c2c2c2_snd_equiv :
    order56_SD order56_C2C2C2 order88_chiC2C2C2_snd ≃*
      order56_SD order56_C2C2C2 order88_chiC2C2C2 :=
  order56_SD_equiv_of_character_comp order88_chiC2C2C2 order88_chiC2C2C2_snd
    order88_C2C2C2_swap12 order88_chiC2C2C2_comp_swap12

noncomputable def order56_c2c2c2_trd_equiv :
    order56_SD order56_C2C2C2 order88_chiC2C2C2_trd ≃*
      order56_SD order56_C2C2C2 order88_chiC2C2C2 :=
  order56_SD_equiv_of_character_comp order88_chiC2C2C2 order88_chiC2C2C2_trd
    order88_C2C2C2_swap13 order88_chiC2C2C2_comp_swap13

noncomputable def order56_c2c2c2_fst_snd_equiv :
    order56_SD order56_C2C2C2 order88_chiC2C2C2_fst_snd ≃*
      order56_SD order56_C2C2C2 order88_chiC2C2C2 :=
  order56_SD_equiv_of_character_comp order88_chiC2C2C2 order88_chiC2C2C2_fst_snd
    order88_C2C2C2_shear12 order88_chiC2C2C2_comp_shear12

noncomputable def order56_c2c2c2_fst_trd_equiv :
    order56_SD order56_C2C2C2 order88_chiC2C2C2_fst_trd ≃*
      order56_SD order56_C2C2C2 order88_chiC2C2C2 :=
  order56_SD_equiv_of_character_comp order88_chiC2C2C2 order88_chiC2C2C2_fst_trd
    order88_C2C2C2_shear13 order88_chiC2C2C2_comp_shear13

noncomputable def order56_c2c2c2_snd_trd_equiv :
    order56_SD order56_C2C2C2 order88_chiC2C2C2_snd_trd ≃*
      order56_SD order56_C2C2C2 order88_chiC2C2C2 :=
  order56_SD_equiv_of_character_comp order88_chiC2C2C2 order88_chiC2C2C2_snd_trd
    order88_C2C2C2_shear23 order88_chiC2C2C2_comp_shear23

noncomputable def order56_c2c2c2_fst_snd_trd_equiv :
    order56_SD order56_C2C2C2 order88_chiC2C2C2_fst_snd_trd ≃*
      order56_SD order56_C2C2C2 order88_chiC2C2C2 :=
  order56_SD_equiv_of_character_comp order88_chiC2C2C2 order88_chiC2C2C2_fst_snd_trd
    order88_C2C2C2_shear123 order88_chiC2C2C2_comp_shear123

/-- Direct-product representative with complement `H`. -/
abbrev order56_DP (H : Type) : Type := order56_C7 × H

abbrev order56_RA : Type := order56_DP order56_C8
abbrev order56_RB : Type := order56_DP order56_C4C2
abbrev order56_RC : Type := order56_DP order56_C2C2C2
abbrev order56_RD : Type := order56_DP order56_D8
abbrev order56_RE : Type := order56_DP order56_Q8
noncomputable abbrev order56_RF : Type := order56_SD order56_C8 order88_chiC8
noncomputable abbrev order56_RG : Type := order56_SD order56_C4C2 order88_chiC4C2_fst
noncomputable abbrev order56_RH : Type := order56_SD order56_C4C2 order88_chiC4C2_snd
noncomputable abbrev order56_RI : Type := order56_SD order56_C2C2C2 order88_chiC2C2C2
noncomputable abbrev order56_RJ : Type := order56_SD order56_D8 order88_chiD8_rot
noncomputable abbrev order56_RK : Type := order56_SD order56_D8 order88_chiD8_ref
noncomputable abbrev order56_RL : Type := order56_SD order56_Q8 order88_chiQ8

/-! ### The extra non-normal Sylow-7 representative -/

/-- A standard order-`7` automorphism of `(C₂)^3`. -/
def order56_tau7 : MulAut order56_C2C2C2 where
  toFun x := (x.2.1, (x.2.2, x.1 * x.2.1))
  invFun x := (x.2.2 * x.1, (x.1, x.2.1))
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

theorem order56_tau7_pow_seven : order56_tau7 ^ 7 = 1 := by
  apply MulEquiv.ext
  rintro ⟨a, b, c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

theorem order56_tau7_ne_one : order56_tau7 ≠ 1 := by
  intro h
  have hx := congrArg (fun f : MulAut order56_C2C2C2 =>
    f (Multiplicative.ofAdd (1 : ZMod 2), (1, 1))) h
  exact (by decide : order56_tau7 (Multiplicative.ofAdd (1 : ZMod 2), (1, 1)) ≠
    (1 : MulAut order56_C2C2C2) (Multiplicative.ofAdd (1 : ZMod 2), (1, 1))) hx

/-- The standard `C₇`-action on `(C₂)^3`. -/
def order56_c7ActionC2C2C2 : order56_C7 →* MulAut order56_C2C2C2 :=
  MonoidHom.mk' (fun x => order56_tau7 ^ (Multiplicative.toAdd x).val)
    (fun a b => pow_val_add order56_tau7_pow_seven a.toAdd b.toAdd)

abbrev order56_RM : Type :=
  SemidirectProduct order56_C2C2C2 order56_C7 order56_c7ActionC2C2C2

noncomputable instance instFintypeOrder56RM : Fintype order56_RM :=
  Fintype.ofEquiv (order56_C2C2C2 × order56_C7) SemidirectProduct.equivProd.symm

/-! ### Actions of `C₇` on groups of order `8` -/

/-- A homomorphism from `C₇` to a finite group whose order is not divisible by `7` is trivial. -/
theorem order56_c7_action_trivial_of_not_dvd_card {A : Type} [Group A] [Finite A]
    (hA : ¬ 7 ∣ Nat.card A) (φ : order56_C7 →* A) : φ = 1 := by
  letI : Fintype A := Fintype.ofFinite A
  apply MonoidHom.ext
  intro x
  apply orderOf_eq_one_iff.mp
  have hx7 : x ^ 7 = 1 := by
    have hx := pow_card_eq_one' (x := x)
    simpa [order56_C7, card_cyclicRep (by norm_num : 7 ≠ 0)] using hx
  have h7 : orderOf (φ x) ∣ 7 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    calc
      φ x ^ 7 = φ (x ^ 7) := by rw [map_pow]
      _ = 1 := by rw [hx7, map_one]
  have hcard : orderOf (φ x) ∣ Nat.card A := by
    rw [Nat.card_eq_fintype_card]
    exact orderOf_dvd_card
  have hcop : Nat.Coprime 7 (Nat.card A) :=
    (show Nat.Prime 7 by norm_num).coprime_iff_not_dvd.mpr hA
  exact Nat.eq_one_of_dvd_coprimes hcop h7 hcard

/-- Multiplication by units embeds into the automorphism group of `C₈`. -/
theorem order56_unitAutHom8_injective : Function.Injective (unitAutHom (p := 8)) := by
  intro u v h
  have h1 : unitAutHom u (Multiplicative.ofAdd (1 : ZMod 8)) =
      unitAutHom v (Multiplicative.ofAdd (1 : ZMod 8)) := by rw [h]
  simp only [unitAutHom_apply, mul_one, EmbeddingLike.apply_eq_iff_eq] at h1
  exact Units.ext (congrArg Multiplicative.toAdd h1)

/-- Every automorphism of `C₈` is multiplication by a unit of `ZMod 8`. -/
theorem order56_mulAut_c8_eq_unitAutHom (σ : MulAut order56_C8) :
    ∃ u : (ZMod 8)ˣ, σ = unitAutHom u := by
  let f : AddAut (ZMod 8) := Multiplicative.toAdd ((MulAutMultiplicative (ZMod 8)) σ)
  let u : (ZMod 8)ˣ := Additive.toMul ((ZMod.AddAutEquivUnits 8) f)
  refine ⟨u, ?_⟩
  ext x
  obtain ⟨m, rfl⟩ := Multiplicative.ofAdd.surjective x
  change Multiplicative.ofAdd (f m) = unitAutHom u (Multiplicative.ofAdd m)
  have hu : Additive.ofMul u = (ZMod.AddAutEquivUnits 8) f := by simp [u]
  have hf : f = (ZMod.AddAutEquivUnits 8).symm (Additive.ofMul u) := by
    symm
    rw [hu]
    exact AddEquiv.symm_apply_apply (ZMod.AddAutEquivUnits 8) f
  rw [hf, unitAutHom_apply]
  simp [ZMod.AddAutEquivUnits_symm_apply, Units.smul_def]

theorem order56_card_aut_c8 : Nat.card (MulAut order56_C8) = 4 := by
  let e : (ZMod 8)ˣ ≃ MulAut order56_C8 :=
    Equiv.ofBijective (unitAutHom (p := 8)) ⟨
      order56_unitAutHom8_injective,
      fun σ => by
        obtain ⟨u, hu⟩ := order56_mulAut_c8_eq_unitAutHom σ
        exact ⟨u, hu.symm⟩⟩
  rw [Nat.card_eq_fintype_card]
  change Fintype.card (MulAut order56_C8) = 4
  rw [← Fintype.card_congr e]
  decide +kernel

/-- The natural lift `ZMod 2 → ZMod 4` used to write endomorphisms of `C₄ × C₂`. -/
abbrev order56_zmod2To4 (b : ZMod 2) : ZMod 4 := (b.val : ZMod 4)

/-- The natural reduction `ZMod 4 → ZMod 2` used to write endomorphisms of `C₄ × C₂`. -/
abbrev order56_zmod4To2 (a : ZMod 4) : ZMod 2 := (a.val : ZMod 2)

abbrev order56_c4c2_e1 : order56_C4C2 := (Multiplicative.ofAdd (1 : ZMod 4), 1)

abbrev order56_c4c2_e2 : order56_C4C2 := (1, Multiplicative.ofAdd (1 : ZMod 2))

/--
The automorphism of `C₄ × C₂` with parameters
`u : (ZMod 4)ˣ`, `t : ZMod 2`, and `w : ZMod 2`.

It sends the standard generators to `(u, t)` and `(2w, 1)`.
-/
def order56_c4c2Map (u : (ZMod 4)ˣ) (t w : ZMod 2)
    (x : order56_C4C2) : order56_C4C2 :=
  (Multiplicative.ofAdd
      ((u : ZMod 4) * x.1.toAdd +
        (2 : ZMod 4) * order56_zmod2To4 w * order56_zmod2To4 x.2.toAdd),
    Multiplicative.ofAdd (order56_zmod4To2 x.1.toAdd * t + x.2.toAdd))

def order56_c4c2Inv (u : (ZMod 4)ˣ) (t w : ZMod 2)
    (y : order56_C4C2) : order56_C4C2 :=
  let b : ZMod 2 := y.2.toAdd - order56_zmod4To2 y.1.toAdd * t
  (Multiplicative.ofAdd
      ((↑u⁻¹ : ZMod 4) *
        (y.1.toAdd - (2 : ZMod 4) * order56_zmod2To4 w * order56_zmod2To4 b)),
    Multiplicative.ofAdd b)

noncomputable def order56_c4c2Aut (u : (ZMod 4)ˣ) (t w : ZMod 2) :
    MulAut order56_C4C2 where
  toFun := order56_c4c2Map u t w
  invFun := order56_c4c2Inv u t w
  left_inv := by
    intro x
    rcases x with ⟨a, b⟩
    fin_cases u <;> fin_cases t <;> fin_cases w <;> fin_cases a <;> fin_cases b <;>
      decide
  right_inv := by
    intro x
    rcases x with ⟨a, b⟩
    fin_cases u <;> fin_cases t <;> fin_cases w <;> fin_cases a <;> fin_cases b <;>
      decide
  map_mul' := by
    intro x y
    rcases x with ⟨a, b⟩
    rcases y with ⟨c, d⟩
    fin_cases u <;> fin_cases t <;> fin_cases w <;>
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide

/-- Homomorphisms out of `C₄ × C₂` are determined by the two standard generators. -/
theorem order56_c4c2_hom_ext {M : Type} [Group M] {χ ψ : order56_C4C2 →* M}
    (h1 : χ order56_c4c2_e1 = ψ order56_c4c2_e1)
    (h2 : χ order56_c4c2_e2 = ψ order56_c4c2_e2) : χ = ψ := by
  apply MonoidHom.ext
  rintro ⟨x4, x2⟩
  obtain ⟨a, rfl⟩ := Multiplicative.ofAdd.surjective x4
  obtain ⟨b, rfl⟩ := Multiplicative.ofAdd.surjective x2
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
  have hx : (Multiplicative.ofAdd a, Multiplicative.ofAdd b) =
      order56_c4c2_e1 ^ a.val * order56_c4c2_e2 ^ b.val := by
    simp [order56_c4c2_e1, order56_c4c2_e2, Prod.pow_mk, ha, hb]
  rw [hx, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, h1, h2]

theorem order56_c4c2_mulAut_ext {α β : MulAut order56_C4C2}
    (h1 : α order56_c4c2_e1 = β order56_c4c2_e1)
    (h2 : α order56_c4c2_e2 = β order56_c4c2_e2) : α = β := by
  apply DFunLike.ext
  intro x
  exact congrFun (congrArg DFunLike.coe
    (order56_c4c2_hom_ext (χ := α.toMonoidHom) (ψ := β.toMonoidHom) h1 h2)) x

theorem order56_c4c2Aut_injective :
    Function.Injective
      (fun p : (ZMod 4)ˣ × ZMod 2 × ZMod 2 => order56_c4c2Aut p.1 p.2.1 p.2.2) := by
  rintro ⟨u, t, w⟩ ⟨u', t', w'⟩ h
  have h1 := congrArg (fun α : MulAut order56_C4C2 => α order56_c4c2_e1) h
  have h2 := congrArg (fun α : MulAut order56_C4C2 => α order56_c4c2_e2) h
  have h1' : (u : ZMod 4) = (u' : ZMod 4) ∧ t = t' := by
    simpa [order56_c4c2Aut, order56_c4c2Map, order56_c4c2_e1,
      order56_zmod2To4, order56_zmod4To2] using h1
  have h2' : (2 : ZMod 4) * order56_zmod2To4 w * order56_zmod2To4 (1 : ZMod 2) =
      (2 : ZMod 4) * order56_zmod2To4 w' * order56_zmod2To4 (1 : ZMod 2) := by
    simpa [order56_c4c2Aut, order56_c4c2Map, order56_c4c2_e2,
      order56_zmod2To4, order56_zmod4To2] using h2
  have hu : u = u' := Units.ext h1'.1
  have ht : t = t' := h1'.2
  have hw : w = w' := by
    fin_cases w <;> fin_cases w'
    · rfl
    · exfalso
      exact (by decide :
        ¬ ((2 : ZMod 4) * order56_zmod2To4 (0 : ZMod 2) *
            order56_zmod2To4 (1 : ZMod 2) =
          (2 : ZMod 4) * order56_zmod2To4 (1 : ZMod 2) *
            order56_zmod2To4 (1 : ZMod 2))) h2'
    · exfalso
      exact (by decide :
        ¬ ((2 : ZMod 4) * order56_zmod2To4 (1 : ZMod 2) *
            order56_zmod2To4 (1 : ZMod 2) =
          (2 : ZMod 4) * order56_zmod2To4 (0 : ZMod 2) *
            order56_zmod2To4 (1 : ZMod 2))) h2'
    · rfl
  simp [hu, ht, hw]

theorem order56_c4c2_aut_e1_eq (α : MulAut order56_C4C2) :
    ∃ (u : (ZMod 4)ˣ) (t : ZMod 2),
      α order56_c4c2_e1 = (Multiplicative.ofAdd (u : ZMod 4), Multiplicative.ofAdd t) := by
  have hsq_ne : (α order56_c4c2_e1) ^ 2 ≠ 1 := by
    intro h
    have hpre : order56_c4c2_e1 ^ 2 = 1 := by
      have hmap : α (order56_c4c2_e1 ^ 2) = α 1 := by
        rw [map_pow]
        simpa using h
      exact α.injective hmap
    exact (by decide : order56_c4c2_e1 ^ 2 ≠ 1) hpre
  rcases h : α order56_c4c2_e1 with ⟨a, b⟩
  fin_cases a <;> fin_cases b
  · exfalso
    apply hsq_ne
    rw [h]
    decide
  · exfalso
    apply hsq_ne
    rw [h]
    decide
  · refine ⟨1, 0, ?_⟩
    rfl
  · refine ⟨1, 1, ?_⟩
    rfl
  · exfalso
    apply hsq_ne
    rw [h]
    decide
  · exfalso
    apply hsq_ne
    rw [h]
    decide
  · refine ⟨-1, 0, ?_⟩
    decide
  · refine ⟨-1, 1, ?_⟩
    decide

theorem order56_c4c2_aut_e2_eq (α : MulAut order56_C4C2) (u : (ZMod 4)ˣ)
    (t : ZMod 2)
    (hu : α order56_c4c2_e1 =
      (Multiplicative.ofAdd (u : ZMod 4), Multiplicative.ofAdd t)) :
    ∃ w : ZMod 2,
      α order56_c4c2_e2 =
        (Multiplicative.ofAdd ((2 : ZMod 4) * order56_zmod2To4 w),
          Multiplicative.ofAdd (1 : ZMod 2)) := by
  have hsq : (α order56_c4c2_e2) ^ 2 = 1 := by
    rw [← map_pow]
    rw [show order56_c4c2_e2 ^ 2 = 1 by decide]
    simp
  have hne_one : α order56_c4c2_e2 ≠ 1 := by
    intro h
    have hmap : α order56_c4c2_e2 = α 1 := by
      rw [h]
      simp
    have hpre : order56_c4c2_e2 = 1 := α.injective hmap
    exact (by decide : order56_c4c2_e2 ≠ 1) hpre
  have hne_sq : α order56_c4c2_e2 ≠ (α order56_c4c2_e1) ^ 2 := by
    intro h
    have hmap : α order56_c4c2_e2 = α (order56_c4c2_e1 ^ 2) := by
      rw [map_pow]
      exact h
    have hpre : order56_c4c2_e2 = order56_c4c2_e1 ^ 2 := α.injective hmap
    exact (by decide : order56_c4c2_e2 ≠ order56_c4c2_e1 ^ 2) hpre
  rcases h : α order56_c4c2_e2 with ⟨a, b⟩
  fin_cases a <;> fin_cases b
  · exfalso
    apply hne_one
    rw [h]
    rfl
  · refine ⟨0, ?_⟩
    rfl
  · exfalso
    have hbad := congrArg Prod.fst hsq
    rw [h] at hbad
    exact (by decide : ¬ ((Multiplicative.ofAdd (1 : ZMod 4)) ^ 2 = 1)) hbad
  · exfalso
    have hbad := congrArg Prod.fst hsq
    rw [h] at hbad
    exact (by decide : ¬ ((Multiplicative.ofAdd (1 : ZMod 4)) ^ 2 = 1)) hbad
  · exfalso
    apply hne_sq
    rw [h, hu]
    fin_cases u <;> fin_cases t <;> decide
  · refine ⟨1, ?_⟩
    decide
  · exfalso
    have hbad := congrArg Prod.fst hsq
    rw [h] at hbad
    exact (by decide : ¬ ((Multiplicative.ofAdd (3 : ZMod 4)) ^ 2 = 1)) hbad
  · exfalso
    have hbad := congrArg Prod.fst hsq
    rw [h] at hbad
    exact (by decide : ¬ ((Multiplicative.ofAdd (3 : ZMod 4)) ^ 2 = 1)) hbad

theorem order56_c4c2Aut_surjective :
    Function.Surjective
      (fun p : (ZMod 4)ˣ × ZMod 2 × ZMod 2 => order56_c4c2Aut p.1 p.2.1 p.2.2) := by
  intro α
  obtain ⟨u, t, hu⟩ := order56_c4c2_aut_e1_eq α
  obtain ⟨w, hw⟩ := order56_c4c2_aut_e2_eq α u t hu
  refine ⟨(u, t, w), ?_⟩
  apply order56_c4c2_mulAut_ext
  · simpa [order56_c4c2Aut, order56_c4c2Map, order56_c4c2_e1, order56_zmod2To4,
      order56_zmod4To2] using hu.symm
  · have hmap : order56_c4c2Aut u t w order56_c4c2_e2 =
        (Multiplicative.ofAdd ((2 : ZMod 4) * order56_zmod2To4 w),
          Multiplicative.ofAdd (1 : ZMod 2)) := by
      change order56_c4c2Map u t w order56_c4c2_e2 =
        (Multiplicative.ofAdd ((2 : ZMod 4) * order56_zmod2To4 w),
          Multiplicative.ofAdd (1 : ZMod 2))
      fin_cases w <;> norm_num [order56_c4c2Map, order56_zmod2To4, order56_zmod4To2] <;>
        decide
    rw [hw]
    exact hmap

theorem order56_card_aut_c4c2 : Nat.card (MulAut order56_C4C2) = 8 := by
  let e : (ZMod 4)ˣ × ZMod 2 × ZMod 2 ≃ MulAut order56_C4C2 :=
    Equiv.ofBijective
      (fun p : (ZMod 4)ˣ × ZMod 2 × ZMod 2 => order56_c4c2Aut p.1 p.2.1 p.2.2)
      ⟨order56_c4c2Aut_injective, order56_c4c2Aut_surjective⟩
  rw [Nat.card_eq_fintype_card]
  change Fintype.card (MulAut order56_C4C2) = 8
  rw [← Fintype.card_congr e]
  decide +kernel

set_option linter.style.nativeDecide false in
theorem order56_card_aut_c2c2c2 : Nat.card (MulAut order56_C2C2C2) = 168 := by
  rw [Nat.card_eq_fintype_card]
  native_decide

/-- The automorphism of `D₈` sending `r i` to `r (u * i)` and `sr i` to `sr (v + u * i)`. -/
noncomputable def order56_d8Aut (u : (ZMod 4)ˣ) (v : ZMod 4) : MulAut order56_D8 where
  toFun
    | DihedralGroup.r i => DihedralGroup.r ((u : ZMod 4) * i)
    | DihedralGroup.sr i => DihedralGroup.sr (v + (u : ZMod 4) * i)
  invFun
    | DihedralGroup.r i => DihedralGroup.r ((↑u⁻¹ : ZMod 4) * i)
    | DihedralGroup.sr i => DihedralGroup.sr ((↑u⁻¹ : ZMod 4) * (i - v))
  left_inv := by
    intro x
    rcases x with i | i <;> simp [sub_eq_add_neg]
  right_inv := by
    intro x
    rcases x with i | i <;> simp [sub_eq_add_neg, mul_add]
  map_mul' := by
    intro x y
    rcases x with i | i <;> rcases y with j | j <;>
      simp [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
        DihedralGroup.sr_mul_sr, mul_add, add_comm, add_assoc, sub_eq_add_neg]; abel

/-- Homomorphisms out of `D₈` are determined by a rotation and a reflection. -/
theorem order56_d8_hom_ext {M : Type} [Group M] {χ ψ : order56_D8 →* M}
    (hr : χ (DihedralGroup.r (1 : ZMod 4)) = ψ (DihedralGroup.r (1 : ZMod 4)))
    (hs : χ (DihedralGroup.sr (0 : ZMod 4)) = ψ (DihedralGroup.sr (0 : ZMod 4))) :
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

theorem order56_d8_mulAut_ext {α β : MulAut order56_D8}
    (hr : α (DihedralGroup.r (1 : ZMod 4)) = β (DihedralGroup.r (1 : ZMod 4)))
    (hs : α (DihedralGroup.sr (0 : ZMod 4)) = β (DihedralGroup.sr (0 : ZMod 4))) :
    α = β := by
  ext x
  exact congrFun (congrArg DFunLike.coe
    (order56_d8_hom_ext (χ := α.toMonoidHom) (ψ := β.toMonoidHom) hr hs)) x

theorem order56_d8Aut_injective :
    Function.Injective (fun p : (ZMod 4)ˣ × ZMod 4 => order56_d8Aut p.1 p.2) := by
  rintro ⟨u, v⟩ ⟨u', v'⟩ h
  have hr := congrArg (fun α : MulAut order56_D8 => α (DihedralGroup.r (1 : ZMod 4))) h
  have hs := congrArg (fun α : MulAut order56_D8 => α (DihedralGroup.sr (0 : ZMod 4))) h
  change DihedralGroup.r ((u : ZMod 4) * (1 : ZMod 4)) =
    DihedralGroup.r ((u' : ZMod 4) * (1 : ZMod 4)) at hr
  change DihedralGroup.sr (v + (u : ZMod 4) * (0 : ZMod 4)) =
    DihedralGroup.sr (v' + (u' : ZMod 4) * (0 : ZMod 4)) at hs
  have hu : u = u' := Units.ext (by simpa using DihedralGroup.r.inj hr)
  have hv : v = v' := by
    have hidx := DihedralGroup.sr.inj hs
    simpa [hu] using hidx
  simp [hu, hv]

theorem order56_d8_aut_r_eq (α : MulAut order56_D8) :
    ∃ u : (ZMod 4)ˣ, α (DihedralGroup.r (1 : ZMod 4)) = DihedralGroup.r (u : ZMod 4) := by
  let r1 : order56_D8 := DihedralGroup.r (1 : ZMod 4)
  have horder : orderOf (α r1) = 4 := by
    rw [MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
  rcases h : α r1 with i | i
  · fin_cases i
    · exfalso
      rw [h] at horder
      rw [DihedralGroup.orderOf_r] at horder
      exact (by decide +kernel : ¬ 4 / Nat.gcd 4 (ZMod.val (0 : ZMod 4)) = 4) horder
    · exact ⟨1, congrArg (fun z : ZMod 4 => DihedralGroup.r z) rfl⟩
    · exfalso
      rw [h] at horder
      rw [DihedralGroup.orderOf_r] at horder
      exact (by decide +kernel : ¬ 4 / Nat.gcd 4 (ZMod.val (2 : ZMod 4)) = 4) horder
    · exact ⟨-1, congrArg (fun z : ZMod 4 => DihedralGroup.r z)
        (by decide +kernel : (3 : ZMod 4) = (-1 : ZMod 4))⟩
  · fin_cases i
    · exfalso
      rw [h] at horder
      rw [DihedralGroup.orderOf_sr] at horder
      norm_num at horder
    · exfalso
      rw [h] at horder
      rw [DihedralGroup.orderOf_sr] at horder
      norm_num at horder
    · exfalso
      rw [h] at horder
      rw [DihedralGroup.orderOf_sr] at horder
      norm_num at horder
    · exfalso
      rw [h] at horder
      rw [DihedralGroup.orderOf_sr] at horder
      norm_num at horder

theorem order56_d8_aut_s_eq (α : MulAut order56_D8) (u : (ZMod 4)ˣ)
    (hu : α (DihedralGroup.r (1 : ZMod 4)) = DihedralGroup.r (u : ZMod 4)) :
    ∃ v : ZMod 4, α (DihedralGroup.sr (0 : ZMod 4)) = DihedralGroup.sr v := by
  let r1 : order56_D8 := DihedralGroup.r (1 : ZMod 4)
  let s0 : order56_D8 := DihedralGroup.sr (0 : ZMod 4)
  have horder : orderOf (α s0) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact DihedralGroup.orderOf_sr 0
  have hrel : α s0 * α r1 = (α r1)⁻¹ * α s0 := by
    have rel : s0 * r1 = r1⁻¹ * s0 := by
      simp [r1, s0, DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.inv_r]
    simpa [map_mul, map_inv] using congrArg α rel
  rcases h : α s0 with i | i
  · fin_cases i
    · exfalso
      rw [h] at horder
      rw [DihedralGroup.orderOf_r] at horder
      exact (by decide +kernel : ¬ 4 / Nat.gcd 4 (ZMod.val (0 : ZMod 4)) = 2) horder
    · exfalso
      rw [h] at horder
      rw [DihedralGroup.orderOf_r] at horder
      exact (by decide +kernel : ¬ 4 / Nat.gcd 4 (ZMod.val (1 : ZMod 4)) = 2) horder
    · exfalso
      rw [h, hu] at hrel
      fin_cases u
      · rw [DihedralGroup.r_mul_r, DihedralGroup.inv_r, DihedralGroup.r_mul_r] at hrel
        exact (by decide +kernel : ¬ ((2 : ZMod 4) + 1 = -1 + (2 : ZMod 4)))
          (DihedralGroup.r.inj hrel)
      · rw [DihedralGroup.r_mul_r, DihedralGroup.inv_r, DihedralGroup.r_mul_r] at hrel
        exact (by decide +kernel : ¬ ((2 : ZMod 4) + 3 = -3 + (2 : ZMod 4)))
          (DihedralGroup.r.inj hrel)
    · exfalso
      rw [h] at horder
      rw [DihedralGroup.orderOf_r] at horder
      exact (by decide +kernel : ¬ 4 / Nat.gcd 4 (ZMod.val (3 : ZMod 4)) = 2) horder
  · exact ⟨i, rfl⟩

theorem order56_d8Aut_surjective :
    Function.Surjective (fun p : (ZMod 4)ˣ × ZMod 4 => order56_d8Aut p.1 p.2) := by
  intro α
  obtain ⟨u, hu⟩ := order56_d8_aut_r_eq α
  obtain ⟨v, hv⟩ := order56_d8_aut_s_eq α u hu
  refine ⟨(u, v), ?_⟩
  apply order56_d8_mulAut_ext
  · simpa [order56_d8Aut] using hu.symm
  · simpa [order56_d8Aut] using hv.symm

theorem order56_card_aut_d8 : Nat.card (MulAut order56_D8) = 8 := by
  let e : (ZMod 4)ˣ × ZMod 4 ≃ MulAut order56_D8 :=
    Equiv.ofBijective (fun p : (ZMod 4)ˣ × ZMod 4 => order56_d8Aut p.1 p.2)
      ⟨order56_d8Aut_injective, order56_d8Aut_surjective⟩
  rw [Nat.card_eq_fintype_card]
  change Fintype.card (MulAut order56_D8) = 8
  rw [← Fintype.card_congr e]
  decide +kernel

abbrev order56_q8_a1 : order56_Q8 := QuaternionGroup.a (1 : ZMod 4)

abbrev order56_q8_x0 : order56_Q8 := QuaternionGroup.xa (0 : ZMod 4)

abbrev order56_q8_a2 : order56_Q8 := QuaternionGroup.a (2 : ZMod 4)

/-- Homomorphisms out of `Q₈` are determined by the two displayed four-order generators. -/
theorem order56_q8_hom_ext {M : Type} [Group M] {χ ψ : order56_Q8 →* M}
    (ha : χ order56_q8_a1 = ψ order56_q8_a1)
    (hx : χ order56_q8_x0 = ψ order56_q8_x0) :
    χ = ψ := by
  apply MonoidHom.ext
  intro x
  rcases x with i | i
  · have hi : QuaternionGroup.a i = order56_q8_a1 ^ i.val := by
      calc
        QuaternionGroup.a i = QuaternionGroup.a ((i.val : ZMod 4)) := by
          rw [ZMod.natCast_zmod_val]
        _ = order56_q8_a1 ^ i.val := by
          rw [QuaternionGroup.a_one_pow]
    rw [hi, map_pow, map_pow, ha]
  · have hai : QuaternionGroup.a i = order56_q8_a1 ^ i.val := by
      calc
        QuaternionGroup.a i = QuaternionGroup.a ((i.val : ZMod 4)) := by
          rw [ZMod.natCast_zmod_val]
        _ = order56_q8_a1 ^ i.val := by
          rw [QuaternionGroup.a_one_pow]
    have hi : QuaternionGroup.xa i = order56_q8_x0 * order56_q8_a1 ^ i.val := by
      rw [← hai]
      simp [order56_q8_x0, QuaternionGroup.xa_mul_a]
    rw [hi, map_mul, map_mul, map_pow, map_pow, hx, ha]

theorem order56_q8_mulAut_ext {α β : MulAut order56_Q8}
    (ha : α order56_q8_a1 = β order56_q8_a1)
    (hx : α order56_q8_x0 = β order56_q8_x0) : α = β := by
  apply DFunLike.ext
  intro x
  exact congrFun (congrArg DFunLike.coe
    (order56_q8_hom_ext (χ := α.toMonoidHom) (ψ := β.toMonoidHom) ha hx)) x

theorem order56_q8_sq_eq_a2_of_sq_ne_one (x : order56_Q8) (hx : x ^ 2 ≠ 1) :
    x ^ 2 = order56_q8_a2 := by
  rcases x with i | i <;> fin_cases i
  · exfalso
    exact hx (by decide +kernel)
  · decide +kernel
  · exfalso
    exact hx (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem order56_q8_aut_sq_a1 (α : MulAut order56_Q8) :
    (α order56_q8_a1) ^ 2 = order56_q8_a2 := by
  apply order56_q8_sq_eq_a2_of_sq_ne_one
  intro h
  have hpre : order56_q8_a1 ^ 2 = 1 := by
    have hmap : α (order56_q8_a1 ^ 2) = α 1 := by
      rw [map_pow]
      simpa using h
    exact α.injective hmap
  exact (by decide +kernel : order56_q8_a1 ^ 2 ≠ 1) hpre

theorem order56_q8_aut_sq_x0 (α : MulAut order56_Q8) :
    (α order56_q8_x0) ^ 2 = order56_q8_a2 := by
  apply order56_q8_sq_eq_a2_of_sq_ne_one
  intro h
  have hpre : order56_q8_x0 ^ 2 = 1 := by
    have hmap : α (order56_q8_x0 ^ 2) = α 1 := by
      rw [map_pow]
      simpa using h
    exact α.injective hmap
  exact (by decide +kernel : order56_q8_x0 ^ 2 ≠ 1) hpre

abbrev order56_q8Pair : Type :=
  {p : order56_Q8 × order56_Q8 //
    p.1 ^ 2 = order56_q8_a2 ∧ p.2 ^ 2 = order56_q8_a2 ∧
      p.2 ≠ p.1 ∧ p.2 ≠ p.1⁻¹}

theorem order56_q8Pair_card : Fintype.card order56_q8Pair = 24 := by
  decide +kernel

def order56_q8AutPair (α : MulAut order56_Q8) : order56_q8Pair :=
  ⟨(α order56_q8_a1, α order56_q8_x0),
    order56_q8_aut_sq_a1 α,
    order56_q8_aut_sq_x0 α,
    by
      intro h
      have hpre : order56_q8_x0 = order56_q8_a1 := α.injective h
      exact (by decide +kernel : order56_q8_x0 ≠ order56_q8_a1) hpre,
    by
      intro h
      have hmap : α order56_q8_x0 = α order56_q8_a1⁻¹ := by
        rw [map_inv]
        exact h
      have hpre : order56_q8_x0 = order56_q8_a1⁻¹ := α.injective hmap
      exact (by decide +kernel : order56_q8_x0 ≠ order56_q8_a1⁻¹) hpre⟩

theorem order56_q8AutPair_injective :
    Function.Injective order56_q8AutPair := by
  intro α β h
  apply order56_q8_mulAut_ext
  · exact congrArg (fun p : order56_q8Pair => p.1.1) h
  · exact congrArg (fun p : order56_q8Pair => p.1.2) h

def order56_q8ParamA : Fin 6 → order56_Q8
  | 0 => QuaternionGroup.a (1 : ZMod 4)
  | 1 => QuaternionGroup.a (3 : ZMod 4)
  | 2 => QuaternionGroup.xa (0 : ZMod 4)
  | 3 => QuaternionGroup.xa (1 : ZMod 4)
  | 4 => QuaternionGroup.xa (2 : ZMod 4)
  | 5 => QuaternionGroup.xa (3 : ZMod 4)

def order56_q8ParamX : Fin 6 → Fin 4 → order56_Q8
  | 0, 0 => QuaternionGroup.xa (0 : ZMod 4)
  | 0, 1 => QuaternionGroup.xa (1 : ZMod 4)
  | 0, 2 => QuaternionGroup.xa (2 : ZMod 4)
  | 0, 3 => QuaternionGroup.xa (3 : ZMod 4)
  | 1, 0 => QuaternionGroup.xa (0 : ZMod 4)
  | 1, 1 => QuaternionGroup.xa (1 : ZMod 4)
  | 1, 2 => QuaternionGroup.xa (2 : ZMod 4)
  | 1, 3 => QuaternionGroup.xa (3 : ZMod 4)
  | 2, 0 => QuaternionGroup.a (1 : ZMod 4)
  | 2, 1 => QuaternionGroup.a (3 : ZMod 4)
  | 2, 2 => QuaternionGroup.xa (1 : ZMod 4)
  | 2, 3 => QuaternionGroup.xa (3 : ZMod 4)
  | 3, 0 => QuaternionGroup.a (1 : ZMod 4)
  | 3, 1 => QuaternionGroup.a (3 : ZMod 4)
  | 3, 2 => QuaternionGroup.xa (0 : ZMod 4)
  | 3, 3 => QuaternionGroup.xa (2 : ZMod 4)
  | 4, 0 => QuaternionGroup.a (1 : ZMod 4)
  | 4, 1 => QuaternionGroup.a (3 : ZMod 4)
  | 4, 2 => QuaternionGroup.xa (1 : ZMod 4)
  | 4, 3 => QuaternionGroup.xa (3 : ZMod 4)
  | 5, 0 => QuaternionGroup.a (1 : ZMod 4)
  | 5, 1 => QuaternionGroup.a (3 : ZMod 4)
  | 5, 2 => QuaternionGroup.xa (0 : ZMod 4)
  | 5, 3 => QuaternionGroup.xa (2 : ZMod 4)

def order56_q8ParamMap (i : Fin 6) (j : Fin 4) : order56_Q8 → order56_Q8
  | QuaternionGroup.a k => order56_q8ParamA i ^ k.val
  | QuaternionGroup.xa k => order56_q8ParamX i j * order56_q8ParamA i ^ k.val

noncomputable def order56_q8ParamHom (i : Fin 6) (j : Fin 4) : order56_Q8 →* order56_Q8 where
  toFun := order56_q8ParamMap i j
  map_one' := by
    change order56_q8ParamA i ^ (0 : ZMod 4).val = 1
    simp
  map_mul' := by
    intro x y
    rcases x with k | k <;> rcases y with l | l <;>
      fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      decide +kernel

theorem order56_q8ParamHom_injective (i : Fin 6) (j : Fin 4) :
    Function.Injective (order56_q8ParamHom i j) := by
  intro x y h
  rcases x with k | k <;> rcases y with l | l <;>
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    first
    | rfl
    | exfalso
      revert h
      decide +kernel

noncomputable def order56_q8ParamAut (i : Fin 6) (j : Fin 4) : MulAut order56_Q8 :=
  MulEquiv.ofBijective (order56_q8ParamHom i j)
    (order56_q8ParamHom_injective i j).bijective_of_finite

theorem order56_q8ParamAut_injective :
    Function.Injective (fun p : Fin 6 × Fin 4 => order56_q8ParamAut p.1 p.2) := by
  intro p q h
  rcases p with ⟨i, j⟩
  rcases q with ⟨i', j'⟩
  have ha := congrArg (fun α : MulAut order56_Q8 => α order56_q8_a1) h
  have hx := congrArg (fun α : MulAut order56_Q8 => α order56_q8_x0) h
  fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
    first
    | rfl
    | exfalso
      revert ha
      decide +kernel
    | exfalso
      revert hx
      decide +kernel

theorem order56_card_aut_q8 : Nat.card (MulAut order56_Q8) = 24 := by
  rw [Nat.card_eq_fintype_card]
  apply le_antisymm
  · have h :=
      Fintype.card_le_of_injective order56_q8AutPair order56_q8AutPair_injective
    simpa [order56_q8Pair_card] using h
  · have h :=
      Fintype.card_le_of_injective
        (fun p : Fin 6 × Fin 4 => order56_q8ParamAut p.1 p.2)
        order56_q8ParamAut_injective
    simpa using h

theorem order56_c7_action_c8_trivial (φ : order56_C7 →* MulAut order56_C8) : φ = 1 :=
  order56_c7_action_trivial_of_not_dvd_card (by rw [order56_card_aut_c8]; norm_num) φ

theorem order56_c7_action_c4c2_trivial (φ : order56_C7 →* MulAut order56_C4C2) : φ = 1 :=
  order56_c7_action_trivial_of_not_dvd_card (by rw [order56_card_aut_c4c2]; norm_num) φ

theorem order56_c7_action_d8_trivial (φ : order56_C7 →* MulAut order56_D8) : φ = 1 :=
  order56_c7_action_trivial_of_not_dvd_card (by rw [order56_card_aut_d8]; norm_num) φ

theorem order56_c7_action_q8_trivial (φ : order56_C7 →* MulAut order56_Q8) : φ = 1 :=
  order56_c7_action_trivial_of_not_dvd_card (by rw [order56_card_aut_q8]; norm_num) φ

theorem order56_factorization_card_aut_c2c2c2_at_7 :
    Nat.factorization (Nat.card (MulAut order56_C2C2C2)) 7 = 1 := by
  rw [order56_card_aut_c2c2c2]
  decide +kernel

theorem order56_tau7_zpow_eq_pow_unit_of_ne_one {k : ℤ} (hk : order56_tau7 ^ k ≠ 1) :
    ∃ u : (ZMod 7)ˣ, order56_tau7 ^ k = order56_tau7 ^ (u : ZMod 7).val := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have htau_order : orderOf order56_tau7 = 7 :=
    orderOf_eq_prime order56_tau7_pow_seven order56_tau7_ne_one
  let r : ℕ := (k : ZMod 7).val
  have hrlt : r < 7 := by simpa [r] using ZMod.val_lt (k : ZMod 7)
  have hrne : r ≠ 0 := by
    intro hr0
    have hkz : (k : ZMod 7) = 0 := by
      rw [← ZMod.natCast_zmod_val (k : ZMod 7)]
      simp [r, hr0]
    have hmod0 : (0 : ℤ) ≡ k [ZMOD (7 : ℤ)] :=
      (ZMod.intCast_eq_intCast_iff 0 k 7).mp (by simp [hkz])
    have hpow : order56_tau7 ^ (0 : ℤ) = order56_tau7 ^ k := by
      rw [zpow_eq_zpow_iff_modEq, htau_order]
      exact hmod0
    exact hk (by simpa using hpow.symm)
  have hcop : Nat.Coprime r 7 := by
    exact ((show Nat.Prime 7 by norm_num).coprime_iff_not_dvd.mpr (by
      intro hd
      have hpos : 0 < r := Nat.pos_of_ne_zero hrne
      have hle : 7 ≤ r := Nat.le_of_dvd hpos hd
      omega)).symm
  refine ⟨ZMod.unitOfCoprime r hcop, ?_⟩
  have huval : ((ZMod.unitOfCoprime r hcop : (ZMod 7)ˣ) : ZMod 7).val = r := by
    have hcoe : ((ZMod.unitOfCoprime r hcop : (ZMod 7)ˣ) : ZMod 7) = (r : ZMod 7) :=
      ZMod.coe_unitOfCoprime r hcop
    rw [hcoe]
    exact ZMod.val_natCast_of_lt hrlt
  rw [huval]
  have hmod : (r : ℤ) ≡ k [ZMOD (7 : ℤ)] :=
    (ZMod.intCast_eq_intCast_iff (r : ℤ) k 7).mp (by
      simp [r])
  rw [← zpow_natCast]
  rw [zpow_eq_zpow_iff_modEq, htau_order]
  exact hmod.symm

/-- Every nontrivial order-`7` automorphism of `(C₂)^3` is conjugate to a unit power of `tau7`. -/
theorem order56_c2c2c2_aut_order7_conj_pow_unit
    (α : MulAut order56_C2C2C2) (hα7 : α ^ 7 = 1) (hα1 : α ≠ 1) :
    ∃ (θ : MulAut order56_C2C2C2) (u : (ZMod 7)ˣ),
      (MulAut.conj θ) α = order56_tau7 ^ (u : ZMod 7).val := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let A := MulAut order56_C2C2C2
  have hfact : Nat.factorization (Nat.card A) 7 = 1 :=
    order56_factorization_card_aut_c2c2c2_at_7
  have hαord : orderOf α = 7 := orderOf_eq_prime hα7 hα1
  have hτord : orderOf order56_tau7 = 7 :=
    orderOf_eq_prime order56_tau7_pow_seven order56_tau7_ne_one
  let Pα : Sylow 7 A := Sylow.ofCard (Subgroup.zpowers α) (by
    rw [Nat.card_zpowers, hαord, hfact]
    norm_num)
  let Pτ : Sylow 7 A := Sylow.ofCard (Subgroup.zpowers order56_tau7) (by
    rw [Nat.card_zpowers, hτord, hfact]
    norm_num)
  obtain ⟨θ, hθ⟩ := MulAction.exists_smul_eq A Pα Pτ
  have hPα : (↑Pα : Subgroup A) = Subgroup.zpowers α := Sylow.coe_ofCard _ _
  have hPτ : (↑Pτ : Subgroup A) = Subgroup.zpowers order56_tau7 := Sylow.coe_ofCard _ _
  have hsub : (MulAut.conj θ) • (Subgroup.zpowers α : Subgroup A) =
      Subgroup.zpowers order56_tau7 := by
    rw [← hPα, ← Sylow.coe_subgroup_smul, hθ, hPτ]
  have hmem : (MulAut.conj θ) α ∈ Subgroup.zpowers order56_tau7 := by
    rw [← hsub]
    rw [Subgroup.pointwise_smul_def]
    rw [Subgroup.mem_map]
    exact ⟨α, Subgroup.mem_zpowers α, rfl⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hkne : order56_tau7 ^ k ≠ 1 := by
    intro h1
    have hconj1 : (MulAut.conj θ) α = 1 := by rw [← hk, h1]
    have hα_eq : α = 1 := by
      apply (MulAut.conj θ).injective
      simpa using hconj1
    exact hα1 hα_eq
  obtain ⟨u, hu⟩ := order56_tau7_zpow_eq_pow_unit_of_ne_one hkne
  exact ⟨θ, u, by rw [← hk, hu]⟩

theorem order56_c7_hom_ext {M : Type} [Group M] {φ ψ : order56_C7 →* M}
    (hgen : φ (Multiplicative.ofAdd (1 : ZMod 7)) =
      ψ (Multiplicative.ofAdd (1 : ZMod 7))) :
    φ = ψ := by
  apply MonoidHom.ext
  intro x
  let n : ZMod 7 := Multiplicative.toAdd x
  have hx : x = (Multiplicative.ofAdd (1 : ZMod 7)) ^ n.val := by
    rw [show x = Multiplicative.ofAdd n from (ofAdd_toAdd _).symm]
    calc
      Multiplicative.ofAdd n = Multiplicative.ofAdd ((n.val : ZMod 7)) := by
        rw [ZMod.natCast_zmod_val]
      _ = Multiplicative.ofAdd (n.val • (1 : ZMod 7)) := by simp
      _ = (Multiplicative.ofAdd (1 : ZMod 7)) ^ n.val := by rw [ofAdd_nsmul]
  rw [hx, map_pow, map_pow, hgen]

theorem order56_c7_action_c2c2c2_nontrivial_equiv
    (φ : order56_C7 →* MulAut order56_C2C2C2) (hφ : φ ≠ 1) :
    Nonempty (SemidirectProduct order56_C2C2C2 order56_C7 φ ≃* order56_RM) := by
  let g : order56_C7 := Multiplicative.ofAdd (1 : ZMod 7)
  have hg7 : g ^ 7 = 1 := by decide
  have hα7 : φ g ^ 7 = 1 := by
    calc
      φ g ^ 7 = φ (g ^ 7) := by rw [map_pow]
      _ = 1 := by rw [hg7, map_one]
  have hα1 : φ g ≠ 1 := by
    intro hgen
    apply hφ
    apply order56_c7_hom_ext
    simpa using hgen
  obtain ⟨θ, u, hθu⟩ := order56_c2c2c2_aut_order7_conj_pow_unit (φ g) hα7 hα1
  have hgen_eq : (((MulAut.conj θ).toMonoidHom.comp φ)
        (Multiplicative.ofAdd (1 : ZMod 7))) =
      (order56_c7ActionC2C2C2.comp (unitAutHom u).toMonoidHom)
        (Multiplicative.ofAdd (1 : ZMod 7)) := by
    change (MulAut.conj θ) (φ g) = order56_tau7 ^
      (Multiplicative.toAdd ((unitAutHom u) g)).val
    rw [hθu]
    have htoadd : Multiplicative.toAdd ((unitAutHom u) g) = (u : ZMod 7) := by
      simp [g, unitAutHom_apply]
    rw [htoadd]
  have haction : ((MulAut.conj θ).toMonoidHom.comp φ) =
      order56_c7ActionC2C2C2.comp (unitAutHom u).toMonoidHom :=
    order56_c7_hom_ext hgen_eq
  exact ⟨(semidirectProductCongrConj θ).trans
    ((semidirectProductCongr_eq haction).trans (semidirectProductCongrAut (unitAutHom u)))⟩

/-! ### Normal Sylow-`7` branch exhaustiveness -/

/-- The thirteen displayed representatives, indexed for the counting framework. -/
noncomputable abbrev order56_reps : Fin 13 → Type
  | 0 => order56_RA
  | 1 => order56_RB
  | 2 => order56_RC
  | 3 => order56_RD
  | 4 => order56_RE
  | 5 => order56_RF
  | 6 => order56_RG
  | 7 => order56_RH
  | 8 => order56_RI
  | 9 => order56_RJ
  | 10 => order56_RK
  | 11 => order56_RL
  | 12 => order56_RM

noncomputable instance instGroupOrder56Reps : ∀ i, Group (order56_reps i)
  | 0 => inferInstanceAs (Group order56_RA)
  | 1 => inferInstanceAs (Group order56_RB)
  | 2 => inferInstanceAs (Group order56_RC)
  | 3 => inferInstanceAs (Group order56_RD)
  | 4 => inferInstanceAs (Group order56_RE)
  | 5 => inferInstanceAs (Group order56_RF)
  | 6 => inferInstanceAs (Group order56_RG)
  | 7 => inferInstanceAs (Group order56_RH)
  | 8 => inferInstanceAs (Group order56_RI)
  | 9 => inferInstanceAs (Group order56_RJ)
  | 10 => inferInstanceAs (Group order56_RK)
  | 11 => inferInstanceAs (Group order56_RL)
  | 12 => inferInstanceAs (Group order56_RM)

private theorem order56_classification_of_c7_action_on_c8 {G : Type*} [Group G]
    {φ : order56_C7 →* MulAut order56_C8}
    (e : G ≃* SemidirectProduct order56_C8 order56_C7 φ) :
    ∃ i, Nonempty (G ≃* order56_reps i) := by
  have hφ : φ = 1 := order56_c7_action_c8_trivial φ
  exact ⟨0, by
    simpa [order56_reps, order56_RA, order56_DP] using
      (⟨e.trans ((semidirectProductCongr_eq hφ).trans
        (SemidirectProduct.mulEquivProd.trans
          (MulEquiv.prodComm : order56_C8 × order56_C7 ≃* order56_C7 × order56_C8)))⟩ :
        Nonempty (G ≃* order56_RA))⟩

private theorem order56_classification_of_c7_action_on_c4c2 {G : Type*} [Group G]
    {φ : order56_C7 →* MulAut order56_C4C2}
    (e : G ≃* SemidirectProduct order56_C4C2 order56_C7 φ) :
    ∃ i, Nonempty (G ≃* order56_reps i) := by
  have hφ : φ = 1 := order56_c7_action_c4c2_trivial φ
  exact ⟨1, by
    simpa [order56_reps, order56_RB, order56_DP] using
      (⟨e.trans ((semidirectProductCongr_eq hφ).trans
        (SemidirectProduct.mulEquivProd.trans
          (MulEquiv.prodComm : order56_C4C2 × order56_C7 ≃* order56_C7 × order56_C4C2)))⟩ :
        Nonempty (G ≃* order56_RB))⟩

private theorem order56_classification_of_trivial_c7_action_on_c2c2c2 {G : Type*} [Group G]
    {φ : order56_C7 →* MulAut order56_C2C2C2} (hφ : φ = 1)
    (e : G ≃* SemidirectProduct order56_C2C2C2 order56_C7 φ) :
    ∃ i, Nonempty (G ≃* order56_reps i) := by
  exact ⟨2, by
    simpa [order56_reps, order56_RC, order56_DP] using
      (⟨e.trans ((semidirectProductCongr_eq hφ).trans
        (SemidirectProduct.mulEquivProd.trans
          (MulEquiv.prodComm :
            order56_C2C2C2 × order56_C7 ≃* order56_C7 × order56_C2C2C2)))⟩ :
        Nonempty (G ≃* order56_RC))⟩

private theorem order56_classification_of_c7_action_on_c2c2c2 {G : Type*} [Group G]
    {φ : order56_C7 →* MulAut order56_C2C2C2}
    (e : G ≃* SemidirectProduct order56_C2C2C2 order56_C7 φ) :
    ∃ i, Nonempty (G ≃* order56_reps i) := by
  by_cases hφ : φ = 1
  · exact order56_classification_of_trivial_c7_action_on_c2c2c2 hφ e
  · obtain ⟨eRM⟩ := order56_c7_action_c2c2c2_nontrivial_equiv φ hφ
    exact ⟨12, by simpa [order56_reps] using
      (⟨e.trans eRM⟩ : Nonempty (G ≃* order56_RM))⟩

private theorem order56_classification_of_c7_action_on_d8 {G : Type*} [Group G]
    {φ : order56_C7 →* MulAut order56_D8}
    (e : G ≃* SemidirectProduct order56_D8 order56_C7 φ) :
    ∃ i, Nonempty (G ≃* order56_reps i) := by
  have hφ : φ = 1 := order56_c7_action_d8_trivial φ
  exact ⟨3, by
    simpa [order56_reps, order56_RD, order56_DP] using
      (⟨e.trans ((semidirectProductCongr_eq hφ).trans
        (SemidirectProduct.mulEquivProd.trans
          (MulEquiv.prodComm : order56_D8 × order56_C7 ≃* order56_C7 × order56_D8)))⟩ :
        Nonempty (G ≃* order56_RD))⟩

private theorem order56_classification_of_c7_action_on_q8 {G : Type*} [Group G]
    {φ : order56_C7 →* MulAut order56_Q8}
    (e : G ≃* SemidirectProduct order56_Q8 order56_C7 φ) :
    ∃ i, Nonempty (G ≃* order56_reps i) := by
  have hφ : φ = 1 := order56_c7_action_q8_trivial φ
  exact ⟨4, by
    simpa [order56_reps, order56_RE, order56_DP] using
      (⟨e.trans ((semidirectProductCongr_eq hφ).trans
        (SemidirectProduct.mulEquivProd.trans
          (MulEquiv.prodComm : order56_Q8 × order56_C7 ≃* order56_C7 × order56_Q8)))⟩ :
        Nonempty (G ≃* order56_RE))⟩

private theorem order56_classification_of_c8_action {G : Type*} [Group G]
    {φ : order56_C8 →* MulAut order56_C7}
    (e : G ≃* SemidirectProduct order56_C7 order56_C8 φ) :
    ∃ i, Nonempty (G ≃* order56_reps i) := by
  rcases order56_c8_action_cases φ with hφ | hφ
  · exact ⟨0, by
      simpa [order56_reps] using
        (⟨e.trans ((semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd)⟩ :
          Nonempty (G ≃* order56_RA))⟩
  · exact ⟨5, by simpa [order56_reps] using
      (⟨e.trans (semidirectProductCongr_eq hφ)⟩ : Nonempty (G ≃* order56_RF))⟩

private theorem order56_classification_of_c4c2_action {G : Type*} [Group G]
    {φ : order56_C4C2 →* MulAut order56_C7}
    (e : G ≃* SemidirectProduct order56_C7 order56_C4C2 φ) :
    ∃ i, Nonempty (G ≃* order56_reps i) := by
  rcases order56_c4c2_action_cases φ with hφ | hφ | hφ | hφ
  · exact ⟨1, by
      simpa [order56_reps] using
        (⟨e.trans ((semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd)⟩ :
          Nonempty (G ≃* order56_RB))⟩
  · exact ⟨6, by simpa [order56_reps] using
      (⟨e.trans (semidirectProductCongr_eq hφ)⟩ : Nonempty (G ≃* order56_RG))⟩
  · exact ⟨7, by simpa [order56_reps] using
      (⟨e.trans (semidirectProductCongr_eq hφ)⟩ : Nonempty (G ≃* order56_RH))⟩
  · exact ⟨7, by simpa [order56_reps] using
      (⟨e.trans ((semidirectProductCongr_eq hφ).trans order56_c4c2_prod_equiv_snd)⟩ :
        Nonempty (G ≃* order56_RH))⟩

private theorem order56_classification_of_c2c2c2_action {G : Type*} [Group G]
    {φ : order56_C2C2C2 →* MulAut order56_C7}
    (e : G ≃* SemidirectProduct order56_C7 order56_C2C2C2 φ) :
    ∃ i, Nonempty (G ≃* order56_reps i) := by
  rcases order56_c2c2c2_action_cases φ with
    hφ | hφ | hφ | hφ | hφ | hφ | hφ | hφ
  · exact ⟨2, by
      simpa [order56_reps] using
        (⟨e.trans ((semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd)⟩ :
          Nonempty (G ≃* order56_RC))⟩
  · exact ⟨8, by simpa [order56_reps] using
      (⟨e.trans (semidirectProductCongr_eq hφ)⟩ : Nonempty (G ≃* order56_RI))⟩
  · exact ⟨8, by simpa [order56_reps] using
      (⟨e.trans ((semidirectProductCongr_eq hφ).trans order56_c2c2c2_snd_equiv)⟩ :
        Nonempty (G ≃* order56_RI))⟩
  · exact ⟨8, by simpa [order56_reps] using
      (⟨e.trans ((semidirectProductCongr_eq hφ).trans order56_c2c2c2_trd_equiv)⟩ :
        Nonempty (G ≃* order56_RI))⟩
  · exact ⟨8, by simpa [order56_reps] using
      (⟨e.trans ((semidirectProductCongr_eq hφ).trans order56_c2c2c2_fst_snd_equiv)⟩ :
        Nonempty (G ≃* order56_RI))⟩
  · exact ⟨8, by simpa [order56_reps] using
      (⟨e.trans ((semidirectProductCongr_eq hφ).trans order56_c2c2c2_fst_trd_equiv)⟩ :
        Nonempty (G ≃* order56_RI))⟩
  · exact ⟨8, by simpa [order56_reps] using
      (⟨e.trans ((semidirectProductCongr_eq hφ).trans order56_c2c2c2_snd_trd_equiv)⟩ :
        Nonempty (G ≃* order56_RI))⟩
  · exact ⟨8, by simpa [order56_reps] using
      (⟨e.trans ((semidirectProductCongr_eq hφ).trans order56_c2c2c2_fst_snd_trd_equiv)⟩ :
        Nonempty (G ≃* order56_RI))⟩

private theorem order56_classification_of_d8_action {G : Type*} [Group G]
    {φ : order56_D8 →* MulAut order56_C7}
    (e : G ≃* SemidirectProduct order56_C7 order56_D8 φ) :
    ∃ i, Nonempty (G ≃* order56_reps i) := by
  rcases order56_d8_action_cases φ with hφ | hφ | hφ | hφ
  · exact ⟨3, by
      simpa [order56_reps] using
        (⟨e.trans ((semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd)⟩ :
          Nonempty (G ≃* order56_RD))⟩
  · exact ⟨9, by simpa [order56_reps] using
      (⟨e.trans (semidirectProductCongr_eq hφ)⟩ : Nonempty (G ≃* order56_RJ))⟩
  · exact ⟨10, by simpa [order56_reps] using
      (⟨e.trans (semidirectProductCongr_eq hφ)⟩ : Nonempty (G ≃* order56_RK))⟩
  · exact ⟨9, by simpa [order56_reps] using
      (⟨e.trans ((semidirectProductCongr_eq hφ).trans order56_d8_prod_equiv_rot)⟩ :
        Nonempty (G ≃* order56_RJ))⟩

private theorem order56_classification_of_q8_action {G : Type*} [Group G]
    {φ : order56_Q8 →* MulAut order56_C7}
    (e : G ≃* SemidirectProduct order56_C7 order56_Q8 φ) :
    ∃ i, Nonempty (G ≃* order56_reps i) := by
  rcases order56_q8_action_cases φ with hφ | hφ | hφ | hφ
  · exact ⟨4, by
      simpa [order56_reps] using
        (⟨e.trans ((semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd)⟩ :
          Nonempty (G ≃* order56_RE))⟩
  · exact ⟨11, by simpa [order56_reps] using
      (⟨e.trans (semidirectProductCongr_eq hφ)⟩ : Nonempty (G ≃* order56_RL))⟩
  · exact ⟨11, by simpa [order56_reps] using
      (⟨e.trans ((semidirectProductCongr_eq hφ).trans order56_q8_xa_equiv_q8)⟩ :
        Nonempty (G ≃* order56_RL))⟩
  · exact ⟨11, by simpa [order56_reps] using
      (⟨e.trans ((semidirectProductCongr_eq hφ).trans order56_q8_prod_equiv_q8)⟩ :
        Nonempty (G ≃* order56_RL))⟩

/-- If the Sylow `7`-subgroup is normal, the group lies among the first twelve representatives. -/
theorem order56_classification_of_card_sylow_7_eq_one [Finite G] (hG : Nat.card G = 56)
    (hSyl : Nat.card (Sylow 7 G) = 1) :
    ∃ i, Nonempty (G ≃* order56_reps i) := by
  obtain ⟨N, H, φ, _, hcardN, hcardH, ⟨e⟩⟩ :=
    order56_semidirectProduct_of_card_sylow_7_eq_one hG hSyl
  obtain ⟨eN⟩ := prime_classification (by norm_num : Nat.Prime 7) hcardN
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Fintype H := Fintype.ofFinite H
  rcases P3Group.classification 2 H (hcardH.trans (by norm_num)) with
    hH | hH | hH | hH | hH | hH | hH
  · change Nonempty (H ≃* order56_C8) at hH
    obtain ⟨eH⟩ := hH
    exact order56_classification_of_c8_action (e.trans (SemidirectProduct.congr' eN eH))
  · change Nonempty (H ≃* order56_C4C2) at hH
    obtain ⟨eH⟩ := hH
    exact order56_classification_of_c4c2_action (e.trans (SemidirectProduct.congr' eN eH))
  · change Nonempty (H ≃* order56_C2C2C2) at hH
    obtain ⟨eH⟩ := hH
    exact order56_classification_of_c2c2c2_action (e.trans (SemidirectProduct.congr' eN eH))
  · exact (hH.1 rfl).elim
  · exact (hH.1 rfl).elim
  · obtain ⟨eH⟩ := hH.2
    exact order56_classification_of_d8_action (e.trans (SemidirectProduct.congr' eN eH))
  · obtain ⟨eH⟩ := hH.2
    exact order56_classification_of_q8_action (e.trans (SemidirectProduct.congr' eN eH))

/-- If the Sylow `7`-subgroups are not normal, the group is one of the first five direct
products or the extra nontrivial `(C₂)^3 ⋊ C₇` representative. -/
theorem order56_classification_of_card_sylow_7_eq_eight [Finite G] (hG : Nat.card G = 56)
    (hSyl : Nat.card (Sylow 7 G) = 8) :
    ∃ i, Nonempty (G ≃* order56_reps i) := by
  obtain ⟨N, H, φ, _, hcardN, hcardH, ⟨e⟩⟩ :=
    order56_semidirectProduct_of_card_sylow_7_eq_eight hG hSyl
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Fintype N := Fintype.ofFinite N
  obtain ⟨eH⟩ := prime_classification (by norm_num : Nat.Prime 7) hcardH
  rcases P3Group.classification 2 N (hcardN.trans (by norm_num)) with
    hN | hN | hN | hN | hN | hN | hN
  · change Nonempty (N ≃* order56_C8) at hN
    obtain ⟨eN⟩ := hN
    exact order56_classification_of_c7_action_on_c8 (e.trans (SemidirectProduct.congr' eN eH))
  · change Nonempty (N ≃* order56_C4C2) at hN
    obtain ⟨eN⟩ := hN
    exact order56_classification_of_c7_action_on_c4c2 (e.trans (SemidirectProduct.congr' eN eH))
  · change Nonempty (N ≃* order56_C2C2C2) at hN
    obtain ⟨eN⟩ := hN
    exact order56_classification_of_c7_action_on_c2c2c2 (e.trans (SemidirectProduct.congr' eN eH))
  · exact (hN.1 rfl).elim
  · exact (hN.1 rfl).elim
  · obtain ⟨eN⟩ := hN.2
    exact order56_classification_of_c7_action_on_d8 (e.trans (SemidirectProduct.congr' eN eH))
  · obtain ⟨eN⟩ := hN.2
    exact order56_classification_of_c7_action_on_q8 (e.trans (SemidirectProduct.congr' eN eH))

/-- Every group of order `56` is isomorphic to one of the thirteen displayed representatives. -/
theorem order56_classification [Finite G] (hG : Nat.card G = 56) :
    ∃ i, Nonempty (G ≃* order56_reps i) := by
  rcases card_sylow_7_eq_one_or_eight_of_card_56 hG with hSyl | hSyl
  · exact order56_classification_of_card_sylow_7_eq_one hG hSyl
  · exact order56_classification_of_card_sylow_7_eq_eight hG hSyl

/-! ### Cardinalities and distinctness of the representatives -/

private theorem nat_card_eq_of_fintype_card_eq {α : Type*} [Fintype α] {n : Nat}
    (h : Fintype.card α = n) : Nat.card α = n :=
  Nat.card_eq_of_equiv_fin (Fintype.equivFinOfCardEq h)

theorem card_order56_C7 : Nat.card order56_C7 = 7 := card_cyclicRep (by norm_num)

theorem card_order56_C8 : Nat.card order56_C8 = 8 := card_cyclicRep (by norm_num)

theorem card_order56_C4C2 : Nat.card order56_C4C2 = 8 := by
  rw [Nat.card_prod]
  norm_num [card_cyclicRep (by norm_num : 4 ≠ 0), card_cyclicRep (by norm_num : 2 ≠ 0)]

theorem card_order56_C2C2C2 : Nat.card order56_C2C2C2 = 8 := by
  rw [Nat.card_prod, Nat.card_prod]
  norm_num [card_cyclicRep (by norm_num : 2 ≠ 0)]

theorem card_order56_D8 : Nat.card order56_D8 = 8 := by
  rw [DihedralGroup.nat_card]

theorem card_order56_Q8 : Nat.card order56_Q8 = 8 := by
  simpa [order56_Q8] using P3Group.card_quaternion8

theorem card_order56_DP {H : Type} [Group H] (hH : Nat.card H = 8) :
    Nat.card (order56_DP H) = 56 := by
  rw [order56_DP, Nat.card_prod, card_order56_C7, hH]

theorem card_order56_SD {H : Type} [Group H] (χ : H →* Multiplicative (ZMod 2))
    (hH : Nat.card H = 8) : Nat.card (order56_SD H χ) = 56 := by
  rw [order56_SD, SemidirectProduct.card, card_order56_C7, hH]

theorem card_order56_RM : Nat.card order56_RM = 56 := by
  rw [order56_RM, SemidirectProduct.card, card_order56_C2C2C2, card_order56_C7]

theorem card_order56_RA : Nat.card order56_RA = 56 := card_order56_DP card_order56_C8
theorem card_order56_RB : Nat.card order56_RB = 56 := card_order56_DP card_order56_C4C2
theorem card_order56_RC : Nat.card order56_RC = 56 := card_order56_DP card_order56_C2C2C2
theorem card_order56_RD : Nat.card order56_RD = 56 := card_order56_DP card_order56_D8
theorem card_order56_RE : Nat.card order56_RE = 56 := card_order56_DP card_order56_Q8
theorem card_order56_RF : Nat.card order56_RF = 56 :=
  card_order56_SD order88_chiC8 card_order56_C8
theorem card_order56_RG : Nat.card order56_RG = 56 :=
  card_order56_SD order88_chiC4C2_fst card_order56_C4C2
theorem card_order56_RH : Nat.card order56_RH = 56 :=
  card_order56_SD order88_chiC4C2_snd card_order56_C4C2
theorem card_order56_RI : Nat.card order56_RI = 56 :=
  card_order56_SD order88_chiC2C2C2 card_order56_C2C2C2
theorem card_order56_RJ : Nat.card order56_RJ = 56 :=
  card_order56_SD order88_chiD8_rot card_order56_D8
theorem card_order56_RK : Nat.card order56_RK = 56 :=
  card_order56_SD order88_chiD8_ref card_order56_D8
theorem card_order56_RL : Nat.card order56_RL = 56 :=
  card_order56_SD order88_chiQ8 card_order56_Q8

theorem card_order56_reps (i : Fin 13) : Nat.card (order56_reps i) = 56 := by
  fin_cases i
  · exact card_order56_RA
  · exact card_order56_RB
  · exact card_order56_RC
  · exact card_order56_RD
  · exact card_order56_RE
  · exact card_order56_RF
  · exact card_order56_RG
  · exact card_order56_RH
  · exact card_order56_RI
  · exact card_order56_RJ
  · exact card_order56_RK
  · exact card_order56_RL
  · exact card_order56_RM

theorem card_center_order56_RA : Nat.card (Subgroup.center order56_RA) = 56 :=
  nat_card_eq_of_fintype_card_eq (by decide +kernel)

theorem card_center_order56_RB : Nat.card (Subgroup.center order56_RB) = 56 :=
  nat_card_eq_of_fintype_card_eq (by decide +kernel)

theorem card_center_order56_RC : Nat.card (Subgroup.center order56_RC) = 56 :=
  nat_card_eq_of_fintype_card_eq (by decide +kernel)

theorem card_center_order56_RD : Nat.card (Subgroup.center order56_RD) = 14 :=
  nat_card_eq_of_fintype_card_eq (by decide +kernel)

theorem card_center_order56_RE : Nat.card (Subgroup.center order56_RE) = 14 :=
  nat_card_eq_of_fintype_card_eq (by decide +kernel)

theorem card_center_order56_RF : Nat.card (Subgroup.center order56_RF) = 4 :=
  nat_card_eq_of_fintype_card_eq (by decide +kernel)

theorem card_center_order56_RG : Nat.card (Subgroup.center order56_RG) = 4 :=
  nat_card_eq_of_fintype_card_eq (by decide +kernel)

theorem card_center_order56_RH : Nat.card (Subgroup.center order56_RH) = 4 :=
  nat_card_eq_of_fintype_card_eq (by decide +kernel)

theorem card_center_order56_RI : Nat.card (Subgroup.center order56_RI) = 4 :=
  nat_card_eq_of_fintype_card_eq (by decide +kernel)

theorem card_center_order56_RJ : Nat.card (Subgroup.center order56_RJ) = 2 :=
  nat_card_eq_of_fintype_card_eq (by decide +kernel)

theorem card_center_order56_RK : Nat.card (Subgroup.center order56_RK) = 2 :=
  nat_card_eq_of_fintype_card_eq (by decide +kernel)

theorem card_center_order56_RL : Nat.card (Subgroup.center order56_RL) = 2 :=
  nat_card_eq_of_fintype_card_eq (by decide +kernel)

theorem card_center_order56_RM : Nat.card (Subgroup.center order56_RM) = 1 :=
  nat_card_eq_of_fintype_card_eq (by decide +kernel)

/-- Center cardinalities of the thirteen displayed representatives. -/
def order56_center_card : Fin 13 → Nat
  | 0 => 56
  | 1 => 56
  | 2 => 56
  | 3 => 14
  | 4 => 14
  | 5 => 4
  | 6 => 4
  | 7 => 4
  | 8 => 4
  | 9 => 2
  | 10 => 2
  | 11 => 2
  | 12 => 1

theorem card_center_order56_reps (i : Fin 13) :
    Nat.card (Subgroup.center (order56_reps i)) = order56_center_card i := by
  fin_cases i
  · exact card_center_order56_RA
  · exact card_center_order56_RB
  · exact card_center_order56_RC
  · exact card_center_order56_RD
  · exact card_center_order56_RE
  · exact card_center_order56_RF
  · exact card_center_order56_RG
  · exact card_center_order56_RH
  · exact card_center_order56_RI
  · exact card_center_order56_RJ
  · exact card_center_order56_RK
  · exact card_center_order56_RL
  · exact card_center_order56_RM

theorem card_pow_two_eq_one_order56_RA : pow_eq_one_card order56_RA 2 = 2 :=
  nat_card_eq_of_fintype_card_eq (by decide +kernel)

theorem card_pow_two_eq_one_order56_RB : pow_eq_one_card order56_RB 2 = 4 :=
  nat_card_eq_of_fintype_card_eq (by decide +kernel)

theorem card_pow_two_eq_one_order56_RC : pow_eq_one_card order56_RC 2 = 8 :=
  nat_card_eq_of_fintype_card_eq (by decide +kernel)

theorem card_pow_two_eq_one_order56_RD : pow_eq_one_card order56_RD 2 = 6 :=
  nat_card_eq_of_fintype_card_eq (by decide +kernel)

theorem card_pow_two_eq_one_order56_RE : pow_eq_one_card order56_RE 2 = 2 :=
  nat_card_eq_of_fintype_card_eq (by decide +kernel)

theorem card_pow_two_eq_one_order56_RF : pow_eq_one_card order56_RF 2 = 2 :=
  nat_card_eq_of_fintype_card_eq (by decide +kernel)

theorem card_pow_two_eq_one_order56_RG : pow_eq_one_card order56_RG 2 = 4 :=
  nat_card_eq_of_fintype_card_eq (by decide +kernel)

theorem card_pow_two_eq_one_order56_RH : pow_eq_one_card order56_RH 2 = 16 :=
  nat_card_eq_of_fintype_card_eq (by decide +kernel)

theorem card_pow_two_eq_one_order56_RI : pow_eq_one_card order56_RI 2 = 32 :=
  nat_card_eq_of_fintype_card_eq (by decide +kernel)

theorem card_pow_two_eq_one_order56_RJ : pow_eq_one_card order56_RJ 2 = 18 :=
  nat_card_eq_of_fintype_card_eq (by decide +kernel)

theorem card_pow_two_eq_one_order56_RK : pow_eq_one_card order56_RK 2 = 30 :=
  nat_card_eq_of_fintype_card_eq (by decide +kernel)

theorem card_pow_two_eq_one_order56_RL : pow_eq_one_card order56_RL 2 = 2 :=
  nat_card_eq_of_fintype_card_eq (by decide +kernel)

theorem card_pow_two_eq_one_order56_RM : pow_eq_one_card order56_RM 2 = 8 :=
  nat_card_eq_of_fintype_card_eq (by decide +kernel)

/-- Cardinalities of `{x | x ^ 2 = 1}` in the thirteen displayed representatives. -/
def order56_pow_two_eq_one_card : Fin 13 → Nat
  | 0 => 2
  | 1 => 4
  | 2 => 8
  | 3 => 6
  | 4 => 2
  | 5 => 2
  | 6 => 4
  | 7 => 16
  | 8 => 32
  | 9 => 18
  | 10 => 30
  | 11 => 2
  | 12 => 8

theorem card_pow_two_eq_one_order56_reps (i : Fin 13) :
    pow_eq_one_card (order56_reps i) 2 = order56_pow_two_eq_one_card i := by
  fin_cases i
  · exact card_pow_two_eq_one_order56_RA
  · exact card_pow_two_eq_one_order56_RB
  · exact card_pow_two_eq_one_order56_RC
  · exact card_pow_two_eq_one_order56_RD
  · exact card_pow_two_eq_one_order56_RE
  · exact card_pow_two_eq_one_order56_RF
  · exact card_pow_two_eq_one_order56_RG
  · exact card_pow_two_eq_one_order56_RH
  · exact card_pow_two_eq_one_order56_RI
  · exact card_pow_two_eq_one_order56_RJ
  · exact card_pow_two_eq_one_order56_RK
  · exact card_pow_two_eq_one_order56_RL
  · exact card_pow_two_eq_one_order56_RM

def order56_reps_invariant (i : Fin 13) : Nat × Nat :=
  (order56_center_card i, order56_pow_two_eq_one_card i)

theorem order56_reps_invariant_injective : Function.Injective order56_reps_invariant := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp [order56_reps_invariant, order56_center_card, order56_pow_two_eq_one_card] at h ⊢

theorem order56_reps_invariant_eq_of_mulEquiv {i j : Fin 13}
    (hiso : Nonempty (order56_reps i ≃* order56_reps j)) :
    order56_reps_invariant i = order56_reps_invariant j := by
  rcases hiso with ⟨e⟩
  apply Prod.ext
  · change order56_center_card i = order56_center_card j
    rw [← card_center_order56_reps i, ← card_center_order56_reps j]
    exact card_center_eq_of_mulEquiv e
  · change order56_pow_two_eq_one_card i = order56_pow_two_eq_one_card j
    rw [← card_pow_two_eq_one_order56_reps i, ← card_pow_two_eq_one_order56_reps j]
    exact pow_eq_one_card_eq_of_mulEquiv 2 e

theorem order56_reps_pairwise : PairwiseNonMulEquiv order56_reps := by
  intro i j hiso
  exact order56_reps_invariant_injective (order56_reps_invariant_eq_of_mulEquiv hiso)

/-- The displayed representatives exhaust the groups of order `56`, in `IsClassif` form. -/
theorem order56_complete (G : Type) [Group G] (hG : Nat.card G = 56) :
    ∃ i, Nonempty (G ≃* order56_reps i) := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  exact order56_classification (G := G) hG

/-- The displayed representatives form a complete classification of groups of order `56`. -/
theorem order56_isClassif : IsClassif 56 order56_reps where
  card := card_order56_reps
  complete := order56_complete
  distinct := order56_reps_pairwise

end Smallgroups.UsefulTheorems
