/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order4P
import Smallgroups.UsefulTheorems.Order2PSq
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic.NormNum.Prime

/-!
# Classification of groups of order `12` (`4 · 3`, the special case `p = 3`)

Every group of order `4p` with `p ≥ 5` has a unique Sylow-`p` subgroup (i.e. `n_p = 1`).
When `p = 3` this argument fails: the Sylow-3 count satisfies `n₃ ∣ 4` and `n₃ ≡ 1 [MOD 3]`,
giving `n₃ ∈ {1, 4}`.

* **`n₃ = 1`** (Sylow-3 normal): the same analysis as the `4p` case with `p ≡ 3 [MOD 4]`
  applies, yielding four types:
  - Type I:   `ℤ/12` (cyclic)
  - Type II:  `ℤ/2 × ℤ/6` (abelian, non-cyclic)
  - Type III: `ℤ/3 ⋊_{-1} ℤ/4` (a.k.a. `Dic₃`, the dicyclic group)
  - Type V:   `ℤ/2 × D₆` (equivalently `ℤ/2 × S₃`)

* **`n₃ = 4`** (Sylow-3 not normal): the conjugation action on the four Sylow-3 subgroups gives
  an injective homomorphism `G → S₄`, whose image is the unique index-2 subgroup `A₄`.

There are exactly **five** isomorphism classes of groups of order `12`.
-/

namespace Smallgroups.UsefulTheorems

open Sylow Equiv.Perm Subgroup

/-! ### The alternating group `A₄` as the fifth type -/

/-- The alternating group on 4 letters, the unique order-12 group with non-normal Sylow-3. -/
abbrev fourP_A4 : Type := alternatingGroup (Fin 4)

/-- `|A₄| = 12`. -/
theorem card_fourP_A4 : Nat.card fourP_A4 = 12 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

/-- `A₄` is not abelian. -/
theorem fourP_A4_not_comm : ¬ ∀ a b : fourP_A4, a * b = b * a := by
  intro h
  have : Nat.card (Fin 4) ≤ 3 :=
    alternatingGroup.isMulCommutative_iff_card_le_three.mp ⟨⟨h⟩⟩
  simp at this

/-- Every element of `A₄` satisfies `g² = 1` or `g³ = 1`
(the only element orders are `1, 2, 3`). -/
theorem fourP_A4_pow : ∀ g : fourP_A4, g ^ 2 = 1 ∨ g ^ 3 = 1 := by decide

/-- `A₄` has no element of order `4`. -/
theorem fourP_A4_no_order4 : ∀ g : fourP_A4, orderOf g ≠ 4 :=
  orderOf_ne_of_pow_or fourP_A4_pow (by decide) (by decide)

/-- `A₄` has no element of order `6`. -/
theorem fourP_A4_no_order6 : ∀ g : fourP_A4, orderOf g ≠ 6 :=
  orderOf_ne_of_pow_or fourP_A4_pow (by decide) (by decide)

/-! ### Element-order witnesses for Types III and V at `p = 3` -/

private instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- Type III (`ℤ/3 ⋊_{-1} ℤ/4`) has an element of order `4`. -/
theorem fourP_III_3_has_order4 : ∃ g : fourP_III 3, orderOf g = 4 := by
  use SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 4))
  rw [orderOf_injective (SemidirectProduct.inr : Multiplicative (ZMod 4) →* _)
    SemidirectProduct.inr_injective]
  rw [orderOf_ofAdd_eq_addOrderOf]
  exact ZMod.addOrderOf_one 4

/-- Type V (`ℤ/2 × D₆`) has an element of order `6`. -/
theorem fourP_V_3_has_order6 : ∃ g : fourP_V 3, orderOf g = 6 := by
  use (Multiplicative.ofAdd (1 : ZMod 2), DihedralGroup.r (1 : ZMod 3))
  rw [Prod.orderOf_mk, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one,
    DihedralGroup.orderOf_r_one]
  decide

/-! ### Distinctness -/

/-- Types I and A₄ are not isomorphic (abelian vs non-abelian). -/
theorem fourP_I_ne_A4 : ¬ Nonempty (fourP_I 3 ≃* fourP_A4) :=
  isEmpty_mulEquiv_of_comm_noncomm (fourP_I_comm 3) fourP_A4_not_comm

/-- Types II and A₄ are not isomorphic (abelian vs non-abelian). -/
theorem fourP_II_ne_A4 : ¬ Nonempty (fourP_II 3 ≃* fourP_A4) :=
  isEmpty_mulEquiv_of_comm_noncomm (fourP_II_comm 3) fourP_A4_not_comm

/-- Types III and A₄ are not isomorphic (III has order-4 elements, A₄ doesn't). -/
theorem fourP_III_ne_A4 : ¬ Nonempty (fourP_III 3 ≃* fourP_A4) :=
  not_mulEquiv_of_orderOf fourP_III_3_has_order4 fourP_A4_no_order4

/-- Types V and A₄ are not isomorphic (V has order-6 elements, A₄ doesn't). -/
theorem fourP_V_ne_A4 : ¬ Nonempty (fourP_V 3 ≃* fourP_A4) :=
  not_mulEquiv_of_orderOf fourP_V_3_has_order6 fourP_A4_no_order6

/-! ### Exhaustiveness -/

/-- **Exhaustiveness.** Every group of order `12` is isomorphic to one of the five types:
`ℤ/12`, `ℤ/2 × ℤ/6`, `ℤ/3 ⋊_{-1} ℤ/4`, `ℤ/2 × D₆`, or `A₄`. -/
theorem fourP_12_classification {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 12) :
    Nonempty (G ≃* fourP_I 3) ∨
    Nonempty (G ≃* fourP_II 3) ∨
    Nonempty (G ≃* fourP_III 3) ∨
    Nonempty (G ≃* fourP_V 3) ∨
    Nonempty (G ≃* fourP_A4) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hG' : Nat.card G = 4 * 3 := by omega
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 3 G))
  -- |P₀| = 3
  have hcardP : Nat.card (↑P0 : Subgroup G) = 3 := by
    rw [Sylow.card_eq_multiplicity, hG, show (12 : ℕ) = 4 * 3 from by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (3 : ℕ) ∣ 4),
      (by norm_num : Nat.Prime 3).factorization_self, zero_add, pow_one]
  -- [G : P₀] = 4
  have hidx : (↑P0 : Subgroup G).index = 4 := by
    have := (↑P0 : Subgroup G).card_mul_index
    rw [hcardP, hG] at this; omega
  -- n₃ divides 4 and n₃ ≡ 1 mod 3
  have hdvd4 : Nat.card (Sylow 3 G) ∣ 4 := hidx ▸ P0.card_dvd_index
  have hmod3 : Nat.card (Sylow 3 G) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 G
  have hpos : 0 < Nat.card (Sylow 3 G) := Nat.card_pos
  have hle4 : Nat.card (Sylow 3 G) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd4
  -- n₃ ∈ {1, 4}
  have hn3 : Nat.card (Sylow 3 G) = 1 ∨ Nat.card (Sylow 3 G) = 4 := by
    set n := Nat.card (Sylow 3 G) with hn
    interval_cases n
    · left; rfl
    · exfalso; unfold Nat.ModEq at hmod3; omega
    · exfalso; have : (3 : ℕ) ∣ 4 := hdvd4; omega
    · right; rfl
  rcases hn3 with hn1 | hn4
  · -- **Case n₃ = 1**: Sylow-3 is normal → semidirect product → Types I/II/III/V
    by_cases hcyc : IsCyclic G
    · -- Cyclic: Type I (ℤ/12)
      left; haveI := hcyc
      simpa [fourP_I, CyclicRep] using
        cyclicRep_classification (by norm_num : (12 : ℕ) ≠ 0) hG
    · -- Non-cyclic: Schur–Zassenhaus + fourP_classification_mod3_aux
      haveI : Subsingleton (Sylow 3 G) :=
        (Nat.card_eq_one_iff_unique.mp hn1).1
      haveI : (↑P0 : Subgroup G).Normal := normal_of_subsingleton P0
      haveI : (↑P0 : Subgroup G).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
      have hcop : Nat.Coprime (Nat.card (↑P0 : Subgroup G)) (↑P0 : Subgroup G).index := by
        rw [hcardP, hidx]; norm_num
      obtain ⟨H, φ, ⟨e⟩⟩ := schurZassenhaus_semidirectProduct (↑P0 : Subgroup G) hcop
      have hcardH : Nat.card H = 4 := by
        have h1 : Nat.card G = Nat.card (↑P0 : Subgroup G) * Nat.card H := by
          rw [Nat.card_congr e.toEquiv, Nat.card_congr SemidirectProduct.equivProd,
            Nat.card_prod]
        rw [hG, hcardP] at h1; omega
      have h4 := fourP_classification_mod3_aux (by norm_num : Nat.Prime 3)
        (by norm_num : (3 : ℕ) ≠ 2) (by norm_num : 3 % 4 = 3) hG' hcyc
        (↑P0) H φ hcardP hcardH e
      rcases h4 with h | h | h | h
      · left; exact h
      · right; left; exact h
      · right; right; left; exact h
      · right; right; right; left; exact h
  · -- **Case n₃ = 4**: G ≅ A₄ (via conjugation action on Sylow-3 subgroups)
    right; right; right; right
    haveI : Fintype (Sylow 3 G) := Fintype.ofFinite _
    have hfincard : Fintype.card (Sylow 3 G) = 4 := by
      rwa [← Nat.card_eq_fintype_card]
    -- Conjugation action homomorphism, transported to Perm (Fin 4)
    let ε : Sylow 3 G ≃ Fin 4 := by rw [← hfincard]; exact Fintype.equivFin _
    let φ := MulAction.toPermHom G (Sylow 3 G)
    let ψ : G →* Equiv.Perm (Fin 4) :=
      (Equiv.permCongrHom ε).toMonoidHom.comp φ
    -- Step 1: φ is injective (ker φ = ⊥)
    have hφ_inj : Function.Injective φ := by
      rw [← MonoidHom.ker_eq_bot_iff]
      -- normalizer(P₀) has index n₃ = 4, so |normalizer(P₀)| = 3
      have h_norm_idx : (normalizer (P0 : Set G)).index = 4 := by
        rwa [← Sylow.card_eq_index_normalizer P0]
      have h_norm_card : Nat.card (normalizer (P0 : Set G)) = 3 := by
        have := (normalizer (P0 : Set G)).card_mul_index
        rw [h_norm_idx, hG] at this; omega
      -- ↑P₀ = normalizer(P₀) (same cardinality, one ≤ the other)
      have hP_eq_norm : (↑P0 : Subgroup G) = normalizer (P0 : Set G) :=
        Subgroup.eq_of_le_of_card_ge Subgroup.le_normalizer (by rw [h_norm_card, hcardP])
      -- ker φ ≤ stabilizer G P₀ = normalizer(P₀) = ↑P₀
      have hker_le : φ.ker ≤ ↑P0 := by
        intro g hg
        rw [hP_eq_norm]
        have hg_ker := MonoidHom.mem_ker.mp hg
        rw [← Sylow.stabilizer_eq_normalizer]
        rw [MulAction.mem_stabilizer_iff]
        exact Equiv.Perm.ext_iff.mp hg_ker P0
      -- If ker ≠ ⊥, |ker| divides |↑P₀| = 3, so |ker| = 3, ker = ↑P₀
      by_contra hker
      have hker_card_dvd : Nat.card φ.ker ∣ Nat.card (↑P0 : Subgroup G) :=
        Subgroup.card_dvd_of_le hker_le
      rw [hcardP] at hker_card_dvd
      have hker_card_gt : 1 < Nat.card φ.ker :=
        (Subgroup.one_lt_card_iff_ne_bot _).mpr hker
      have hker_card : Nat.card φ.ker = 3 := by
        have hle := Nat.le_of_dvd (by omega) hker_card_dvd
        have : Nat.card φ.ker = 2 ∨ Nat.card φ.ker = 3 := by omega
        rcases this with h | h
        · exact absurd (h ▸ hker_card_dvd) (by norm_num)
        · exact h
      have hker_eq : φ.ker = ↑P0 :=
        Subgroup.eq_of_le_of_card_ge hker_le (by rw [hcardP, hker_card])
      -- ker is normal → ↑P₀ is normal → n₃ = 1, contradiction
      haveI : (↑P0 : Subgroup G).Normal := hker_eq ▸ MonoidHom.normal_ker φ
      haveI := Sylow.unique_of_normal P0 (by assumption)
      have : Nat.card (Sylow 3 G) = 1 := Nat.card_unique
      omega
    -- Step 2: ψ is injective (composition of injective and bijective)
    have hψ_inj : Function.Injective ψ :=
      (Equiv.permCongrHom ε).injective.comp hφ_inj
    -- Step 3: G ≃* ψ.range, and ψ.range has index 2 in Perm(Fin 4)
    have e_range : G ≃* ψ.range := MonoidHom.ofInjective hψ_inj
    have h_range_card : Nat.card ψ.range = 12 := by
      rw [← hG, Nat.card_congr e_range.toEquiv]
    have h_perm_card : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
      rw [Nat.card_perm, Nat.card_fin]; decide
    have h_idx : ψ.range.index = 2 := by
      have := ψ.range.card_mul_index
      rw [h_range_card, h_perm_card] at this; omega
    -- Step 4: ψ.range = alternatingGroup (Fin 4) by index-2 characterization
    have h_alt : ψ.range = alternatingGroup (Fin 4) :=
      Equiv.Perm.eq_alternatingGroup_of_index_eq_two h_idx
    exact ⟨e_range.trans (MulEquiv.subgroupCongr h_alt)⟩

/-! ### IsClassif -/

/-- **The five representatives form a complete classification of groups of order `12`.** -/
theorem fourP_12_isClassif :
    IsClassif 12 (rep5 (fourP_I 3) (fourP_II 3) (fourP_III 3) (fourP_V 3) fourP_A4) := by
  exact isClassif_five (fourP_I 3) (fourP_II 3) (fourP_III 3) (fourP_V 3) fourP_A4
    (card_fourP_I 3) (card_fourP_II 3) (card_fourP_III 3 (by norm_num)) (card_fourP_V 3)
    card_fourP_A4
    (fun G _ hG => by
      haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
      exact fourP_12_classification hG)
    (fourP_I_ne_II (p := 3) (by norm_num))
    (fourP_I_ne_III (p := 3) (by norm_num))
    (fourP_I_ne_V (p := 3) (by norm_num))
    fourP_I_ne_A4
    (fourP_II_ne_III (p := 3) (by norm_num))
    (fourP_II_ne_V (p := 3) (by norm_num))
    fourP_II_ne_A4
    (fourP_III_ne_V (p := 3) (by norm_num))
    fourP_III_ne_A4
    fourP_V_ne_A4

end Smallgroups.UsefulTheorems
