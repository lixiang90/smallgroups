/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic.NormNum.Prime

/-!
# Groups of order 72: the first Sylow dichotomy

`72 = 2³ · 3²`.  By Sylow's theorem, the number `n₃` of Sylow `3`-subgroups divides
`8` and is `≡ 1 (mod 3)`, so `n₃ ∈ {1, 4}`; the number `n₂` of Sylow `2`-subgroups
divides `9` (automatically `≡ 1 (mod 2)`, since every divisor of `9` is odd), so
`n₂ ∈ {1, 3, 9}`.

Unlike order `80` (`2⁴ · 5`), there is **no** forcing counting argument here: the
group `S₃ × A₄` has order `72` with `n₃ = 4` (since `n₃(A₄) = 4` and `n₃(S₃) = 1`,
and Sylow subgroups of a direct product are products of Sylow subgroups) and
`n₂ = 3` (since `n₂(A₄) = 1` and `n₂(S₃) = 3`) *simultaneously* — a genuine example
where **neither** Sylow subgroup is normal. So the dichotomy proved here is really a
**trichotomy**: Sylow-`3` normal, or Sylow-`2` normal, or the residual case
`n₃ = 4 ∧ n₂ ≠ 1`, which needs a different (non-Sylow-counting) reduction later.

Main results:

* `card_sylow_three_of_card_72`: `n₃ = 1 ∨ n₃ = 4`;
* `card_sylow_two_of_card_72`: `n₂ = 1 ∨ n₂ = 3 ∨ n₂ = 9`;
* `order72_sylow_trichotomy`: the bundled trichotomy.
-/

namespace Smallgroups.UsefulTheorems

open Sylow

variable {G : Type*} [Group G]

/-! ### Step 1: the possible Sylow counts. -/

theorem card_sylow_three_of_card_72 [Finite G] (hG : Nat.card G = 72) :
    Nat.card (Sylow 3 G) = 1 ∨ Nat.card (Sylow 3 G) = 4 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 3 G))
  have hndvd_3 : ¬ 3 ∣ Nat.card (Sylow 3 G) := not_dvd_card_sylow 3 G
  have hdvd72 : Nat.card (Sylow 3 G) ∣ 72 := by
    rw [← hG]
    exact P0.card_dvd_index.trans (Subgroup.index_dvd_card _)
  have h72 : 72 = 8 * 9 := by norm_num
  have hdvd8_mul : Nat.card (Sylow 3 G) ∣ 8 * 9 := by simpa [h72] using hdvd72
  have hp3 : Nat.Prime 3 := by norm_num
  have hcop3 : Nat.Coprime (Nat.card (Sylow 3 G)) 3 :=
    (hp3.coprime_iff_not_dvd.mpr hndvd_3).symm
  have hcop : Nat.Coprime (Nat.card (Sylow 3 G)) 9 := by
    have h := hcop3.pow_right 2; norm_num at h; exact h
  have hdvd8 : Nat.card (Sylow 3 G) ∣ 8 := hcop.dvd_of_dvd_mul_right hdvd8_mul
  have hmod := card_sylow_modEq_one 3 G
  have hle : Nat.card (Sylow 3 G) ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd8
  have hpos : 0 < Nat.card (Sylow 3 G) := Nat.card_pos
  interval_cases h : Nat.card (Sylow 3 G) <;>
    first
      | exact Or.inl rfl
      | exact Or.inr rfl
      | (unfold Nat.ModEq at hmod; norm_num at hmod; done)
      | (norm_num at hdvd8)

theorem card_sylow_two_of_card_72 [Finite G] (hG : Nat.card G = 72) :
    Nat.card (Sylow 2 G) = 1 ∨ Nat.card (Sylow 2 G) = 3 ∨ Nat.card (Sylow 2 G) = 9 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 2 G))
  have hndvd_2 : ¬ 2 ∣ Nat.card (Sylow 2 G) := not_dvd_card_sylow 2 G
  have hdvd72 : Nat.card (Sylow 2 G) ∣ 72 := by
    rw [← hG]
    exact P0.card_dvd_index.trans (Subgroup.index_dvd_card _)
  have h72 : 72 = 9 * 8 := by norm_num
  have hdvd9_mul : Nat.card (Sylow 2 G) ∣ 9 * 8 := by simpa [h72] using hdvd72
  have hp2 : Nat.Prime 2 := by norm_num
  have hcop2 : Nat.Coprime (Nat.card (Sylow 2 G)) 2 :=
    (hp2.coprime_iff_not_dvd.mpr hndvd_2).symm
  have hcop : Nat.Coprime (Nat.card (Sylow 2 G)) 8 := by
    have h := hcop2.pow_right 3; norm_num at h; exact h
  have hdvd9 : Nat.card (Sylow 2 G) ∣ 9 := hcop.dvd_of_dvd_mul_right hdvd9_mul
  have hle : Nat.card (Sylow 2 G) ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd9
  have hpos : 0 < Nat.card (Sylow 2 G) := Nat.card_pos
  interval_cases h : Nat.card (Sylow 2 G) <;>
    first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr rfl)
      | (norm_num at hdvd9)

/-- A Sylow `3`-subgroup of a group of order `72` has order `9`. -/
theorem card_sylow_three_subgroup_of_card_72 [Finite G] (hG : Nat.card G = 72)
    (P : Sylow 3 G) : Nat.card (↑P : Subgroup G) = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hndvd : ¬ (3 : ℕ) ∣ 8 := by norm_num
  have hfact : (72 : ℕ).factorization 3 = 2 := by
    rw [show (72 : ℕ) = 8 * 3 ^ 2 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self (by norm_num : Nat.Prime 3),
      Nat.factorization_eq_zero_of_not_dvd hndvd]
  rw [Sylow.card_eq_multiplicity, hG, hfact]
  norm_num

/-- A Sylow `2`-subgroup of a group of order `72` has order `8`. -/
theorem card_sylow_two_subgroup_of_card_72 [Finite G] (hG : Nat.card G = 72)
    (P : Sylow 2 G) : Nat.card (↑P : Subgroup G) = 8 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hndvd : ¬ (2 : ℕ) ∣ 9 := by norm_num
  have hfact : (72 : ℕ).factorization 2 = 3 := by
    rw [show (72 : ℕ) = 2 ^ 3 * 9 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self (by norm_num : Nat.Prime 2),
      Nat.factorization_eq_zero_of_not_dvd hndvd]
  rw [Sylow.card_eq_multiplicity, hG, hfact]
  norm_num

/-! ### Step 2: uniqueness of the Sylow subgroup forces normality. -/

theorem sylow_three_normal_of_card_sylow_three_eq_one [Finite G]
    (hSyl : Nat.card (Sylow 3 G) = 1) (P : Sylow 3 G) : (↑P : Subgroup G).Normal := by
  haveI : Subsingleton (Sylow 3 G) := (Nat.card_eq_one_iff_unique.mp hSyl).1
  exact Sylow.normal_of_subsingleton P

theorem sylow_two_normal_of_card_sylow_two_eq_one [Finite G]
    (hSyl : Nat.card (Sylow 2 G) = 1) (P : Sylow 2 G) : (↑P : Subgroup G).Normal := by
  haveI : Subsingleton (Sylow 2 G) := (Nat.card_eq_one_iff_unique.mp hSyl).1
  exact Sylow.normal_of_subsingleton P

/-! ### The bundled trichotomy -/

/-- **The first Sylow trichotomy for groups of order `72`.**  Either the Sylow
`3`-subgroup is normal, or the Sylow `2`-subgroup is normal, or `n₃ = 4` and
`n₂ ≠ 1` — a residual case genuinely realized by `S₃ × A₄` (which has `n₃ = 4`,
`n₂ = 3`), so it cannot be eliminated by Sylow counting alone and needs a
different reduction. -/
theorem order72_sylow_trichotomy [Finite G] (hG : Nat.card G = 72) :
    (∀ P : Sylow 3 G, (↑P : Subgroup G).Normal) ∨
      (∀ P : Sylow 2 G, (↑P : Subgroup G).Normal) ∨
      (Nat.card (Sylow 3 G) = 4 ∧ Nat.card (Sylow 2 G) ≠ 1) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rcases card_sylow_three_of_card_72 hG with h1 | h4
  · exact Or.inl (fun P => sylow_three_normal_of_card_sylow_three_eq_one h1 P)
  · rcases card_sylow_two_of_card_72 hG with h1' | h3' | h9'
    · exact Or.inr (Or.inl (fun P => sylow_two_normal_of_card_sylow_two_eq_one h1' P))
    · exact Or.inr (Or.inr ⟨h4, by rw [h3']; norm_num⟩)
    · exact Or.inr (Or.inr ⟨h4, by rw [h9']; norm_num⟩)

end Smallgroups.UsefulTheorems
