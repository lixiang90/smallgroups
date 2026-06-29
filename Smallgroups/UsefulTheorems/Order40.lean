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

/-- The quotient map `C₂ → (ZMod 5)ˣ` sending the generator to `order40_u4 ^ 2`. -/
noncomputable abbrev order40_c2UnitHom : Multiplicative (ZMod 2) →* (ZMod 5)ˣ :=
  powHom (p := 5) (q := 2) (order40_u4 ^ 2) (by decide)

/-- Turn a unit-valued character into the corresponding action on `C₅`. -/
noncomputable abbrev order40_action {H : Type} [Group H] (χ : H →* (ZMod 5)ˣ) :
    H →* MulAut order40_C5 :=
  unitAutHom.comp χ

noncomputable abbrev order40_chiC8_two : order40_C8 →* (ZMod 5)ˣ :=
  order40_c2UnitHom.comp order88_chiC8

noncomputable abbrev order40_chiC8_four : order40_C8 →* (ZMod 5)ˣ :=
  powHom (p := 5) (q := 8) order40_u4 (by decide)

noncomputable abbrev order40_chiC4C2_fst_two : order40_C4C2 →* (ZMod 5)ˣ :=
  order40_c2UnitHom.comp order88_chiC4C2_fst

noncomputable abbrev order40_chiC4C2_snd_two : order40_C4C2 →* (ZMod 5)ˣ :=
  order40_c2UnitHom.comp order88_chiC4C2_snd

noncomputable abbrev order40_chiC4C2_fst_four : order40_C4C2 →* (ZMod 5)ˣ :=
  (powHom (p := 5) (q := 4) order40_u4 (by decide)).comp
    (MonoidHom.fst (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2)))

noncomputable abbrev order40_chiC2C2C2 : order40_C2C2C2 →* (ZMod 5)ˣ :=
  order40_c2UnitHom.comp order88_chiC2C2C2

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
