/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.PGroup
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Tactic.NormNum.Prime
import Smallgroups.UsefulTheorems.Order80.Sylow

/-!
# Groups of order 48: the first Sylow trichotomy

`48 = 2⁴ · 3`.  This file proves the classical first step towards classifying
groups of order `48`, parallel to `Order80/Sylow.lean`.  By Sylow's theorem,
the number `n₃` of Sylow `3`-subgroups divides `16` and is `≡ 1 (mod 3)`, so
`n₃ ∈ {1, 4, 16}`.

* If `n₃ = 1`, the Sylow `3`-subgroup is normal (42 of the 52 classes).
* If `n₃ = 16`, a counting argument shows every Sylow `2`-subgroup is normal:
  the `16` Sylow `3`-subgroups pairwise intersect trivially (their order `3`
  is prime), contributing `16 * 2 = 32` distinct elements of order `3`.  This
  leaves exactly `48 - 32 = 16` elements whose order is not `3` -- precisely
  the size of a Sylow `2`-subgroup, none of whose elements can have order `3`
  (their order divides `16`).  Hence every Sylow `2`-subgroup coincides with
  this fixed set of `16` elements, so there is only one.
* If `n₃ = 4`, neither counting argument applies; this is the residual case
  (handled later via the conjugation action of `G` on its four Sylow
  `3`-subgroups, giving `G → S₄`).

Main results:

* `card_sylow_three_of_card_48`: `n₃ = 1 ∨ n₃ = 4 ∨ n₃ = 16`;
* `sylow_three_normal_of_card_sylow_three_eq_one`: if `n₃ = 1` the Sylow
  `3`-subgroup is normal;
* `card_sylow_two_eq_one_of_card_sylow_three_eq_sixteen`: if `n₃ = 16` then
  `n₂ = 1`;
* `order48_sylow_trichotomy`: the bundled trichotomy.
-/

namespace Smallgroups.UsefulTheorems

open Sylow

variable {G : Type*} [Group G]

/-! ### Step 1: the number of Sylow `3`-subgroups is `1`, `4` or `16`. -/

theorem card_sylow_three_of_card_48 [Finite G] (hG : Nat.card G = 48) :
    Nat.card (Sylow 3 G) = 1 ∨ Nat.card (Sylow 3 G) = 4 ∨ Nat.card (Sylow 3 G) = 16 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 3 G))
  have hndvd_3 : ¬ 3 ∣ Nat.card (Sylow 3 G) := not_dvd_card_sylow 3 G
  have hdvd48 : Nat.card (Sylow 3 G) ∣ 48 := by
    rw [← hG]
    exact P0.card_dvd_index.trans (Subgroup.index_dvd_card _)
  have h48 : 48 = 16 * 3 := by norm_num
  have hdvd16_mul : Nat.card (Sylow 3 G) ∣ 16 * 3 := by simpa [h48] using hdvd48
  have hp3 : Nat.Prime 3 := by norm_num
  have hcop : Nat.Coprime (Nat.card (Sylow 3 G)) 3 :=
    (hp3.coprime_iff_not_dvd.mpr hndvd_3).symm
  have hdvd16 : Nat.card (Sylow 3 G) ∣ 16 := hcop.dvd_of_dvd_mul_right hdvd16_mul
  have hmod := card_sylow_modEq_one 3 G
  have hle : Nat.card (Sylow 3 G) ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd16
  have hpos : 0 < Nat.card (Sylow 3 G) := Nat.card_pos
  interval_cases h : Nat.card (Sylow 3 G) <;>
    first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr rfl)
      | (unfold Nat.ModEq at hmod; norm_num at hmod; done)
      | (norm_num at hdvd16)

/-- A Sylow `3`-subgroup of a group of order `48` has order `3`. -/
theorem card_sylow_three_subgroup_of_card_48 [Finite G] (hG : Nat.card G = 48)
    (P : Sylow 3 G) : Nat.card (↑P : Subgroup G) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hndvd : ¬ (3 : ℕ) ∣ 16 := by norm_num
  have hfact : (48 : ℕ).factorization 3 = 1 := by
    rw [show (48 : ℕ) = 16 * 3 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hndvd,
      Nat.Prime.factorization_self (by norm_num : Nat.Prime 3), zero_add]
  rw [Sylow.card_eq_multiplicity, hG, hfact, pow_one]

/-- A Sylow `2`-subgroup of a group of order `48` has order `16`. -/
theorem card_sylow_two_subgroup_of_card_48 [Finite G] (hG : Nat.card G = 48)
    (P : Sylow 2 G) : Nat.card (↑P : Subgroup G) = 16 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hndvd : ¬ (2 : ℕ) ∣ 3 := by norm_num
  have hfact : (48 : ℕ).factorization 2 = 4 := by
    rw [show (48 : ℕ) = 2 ^ 4 * 3 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self (by norm_num : Nat.Prime 2),
      Nat.factorization_eq_zero_of_not_dvd hndvd]
  rw [Sylow.card_eq_multiplicity, hG, hfact]
  norm_num

/-! ### Step 2: if `n₃ = 1`, the Sylow `3`-subgroup is normal. -/

theorem sylow_three_normal_of_card_sylow_three_eq_one [Finite G]
    (hSyl : Nat.card (Sylow 3 G) = 1) (P : Sylow 3 G) : (↑P : Subgroup G).Normal := by
  haveI : Subsingleton (Sylow 3 G) := (Nat.card_eq_one_iff_unique.mp hSyl).1
  exact Sylow.normal_of_subsingleton P

/-! ### Step 3: if `n₃ = 16`, the Sylow `2`-subgroup is normal. -/

/-- Distinct Sylow `3`-subgroups of a group of order `48` intersect trivially:
their common order `3` is prime, so any nontrivial intersection would force
them to be equal. -/
theorem sylow_three_disjoint_of_ne [Finite G] (hG : Nat.card G = 48)
    {P Q : Sylow 3 G} (hne : P ≠ Q) : Disjoint (↑P : Subgroup G) (↑Q : Subgroup G) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hp3 : Nat.Prime 3 := by norm_num
  have hP3 := card_sylow_three_subgroup_of_card_48 hG P
  have hQ3 := card_sylow_three_subgroup_of_card_48 hG Q
  have hdvd : Nat.card (↥((↑P : Subgroup G) ⊓ ↑Q)) ∣ Nat.card (↥(↑P : Subgroup G)) :=
    Subgroup.card_dvd_of_le inf_le_left
  rw [hP3] at hdvd
  rcases (Nat.dvd_prime hp3).mp hdvd with h1 | h3
  · exact disjoint_iff.mpr (Subgroup.card_eq_one.mp h1)
  · exfalso
    apply hne
    apply Sylow.ext
    have heqP : (↑P : Subgroup G) ⊓ ↑Q = ↑P :=
      eq_of_le_of_card_eq inf_le_left (h3.trans hP3.symm)
    have hPQ : (↑P : Subgroup G) ≤ ↑Q := heqP ▸ inf_le_right
    exact eq_of_le_of_card_eq hPQ (hP3.trans hQ3.symm)

/-- The set of nonidentity elements of a Sylow `3`-subgroup. -/
private def sylowThreeNonId (P : Sylow 3 G) : Set G := (↑(↑P : Subgroup G) : Set G) \ {1}

private theorem sylowThreeNonId_pairwiseDisjoint [Finite G] (hG : Nat.card G = 48) :
    Pairwise (fun P Q : Sylow 3 G => Disjoint (sylowThreeNonId P) (sylowThreeNonId Q)) := by
  intro P Q hne
  have hbot : (↑P : Subgroup G) ⊓ ↑Q = ⊥ := disjoint_iff.mp (sylow_three_disjoint_of_ne hG hne)
  apply Set.disjoint_left.mpr
  intro x hxP hxQ
  have hxPQ : x ∈ (↑P : Subgroup G) ⊓ ↑Q := ⟨hxP.1, hxQ.1⟩
  rw [hbot] at hxPQ
  exact hxQ.2 (Subgroup.mem_bot.mp hxPQ)

private theorem sylowThreeNonId_ncard [Finite G] (hG : Nat.card G = 48) (P : Sylow 3 G) :
    (sylowThreeNonId P).ncard = 2 := by
  have hP3 := card_sylow_three_subgroup_of_card_48 hG P
  have hcard : (↑(↑P : Subgroup G) : Set G).ncard = 3 := by
    rw [← Nat.card_coe_set_eq]; exact hP3
  have hmem : (1 : G) ∈ (↑(↑P : Subgroup G) : Set G) := Subgroup.one_mem _
  rw [sylowThreeNonId, Set.ncard_sdiff_singleton_of_mem hmem, hcard]

/-- The set of order-`3` elements in a group of order `48` with `16` Sylow
`3`-subgroups is exactly the union of their nonidentity elements. -/
private theorem orderOf_eq_three_iff [Finite G] (hG : Nat.card G = 48) (g : G) :
    orderOf g = 3 ↔ ∃ P : Sylow 3 G, g ∈ sylowThreeNonId P := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  constructor
  · intro hg
    have hcard : Nat.card (Subgroup.zpowers g) = 3 := by rw [Nat.card_zpowers, hg]
    let P : Sylow 3 G := Sylow.ofCard (Subgroup.zpowers g) (by
      have hfact : (48 : ℕ).factorization 3 = 1 := by
        rw [show (48 : ℕ) = 16 * 3 by norm_num,
          Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
          Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (3 : ℕ) ∣ 16),
          Nat.Prime.factorization_self (by norm_num : Nat.Prime 3), zero_add]
      rw [hcard, hG, hfact, pow_one])
    refine ⟨P, ?_, ?_⟩
    · exact Subgroup.mem_zpowers g
    · intro hg1; rw [hg1, orderOf_one] at hg; norm_num at hg
  · rintro ⟨P, hgP, hg1⟩
    have hdvd : orderOf g ∣ Nat.card (↑P : Subgroup G) :=
      Subgroup.orderOf_dvd_natCard _ hgP
    rw [card_sylow_three_subgroup_of_card_48 hG P] at hdvd
    rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hg1
    · exact h3

private theorem card_orderOf_eq_three [Finite G] (hG : Nat.card G = 48)
    (hSyl : Nat.card (Sylow 3 G) = 16) :
    {g : G | orderOf g = 3}.ncard = 32 := by
  have hset : {g : G | orderOf g = 3} = ⋃ P : Sylow 3 G, sylowThreeNonId P := by
    ext g; simp [orderOf_eq_three_iff hG]
  have hFinIdx : Finite (Sylow 3 G) := Nat.finite_of_card_ne_zero (by rw [hSyl]; norm_num)
  haveI := Fintype.ofFinite (Sylow 3 G)
  rw [hset, Set.ncard_iUnion_of_finite (fun P => Set.toFinite _)
    (sylowThreeNonId_pairwiseDisjoint hG)]
  rw [finsum_eq_sum_of_fintype]
  rw [Finset.sum_congr rfl (fun P _ => sylowThreeNonId_ncard hG P)]
  rw [Finset.sum_const, Finset.card_univ]
  have : Fintype.card (Sylow 3 G) = 16 := by rw [← Nat.card_eq_fintype_card]; exact hSyl
  rw [this]
  rfl

/-- If a group of order `48` has `16` Sylow `3`-subgroups, then it has a unique
(hence normal) Sylow `2`-subgroup. -/
theorem card_sylow_two_eq_one_of_card_sylow_three_eq_sixteen [Finite G]
    (hG : Nat.card G = 48) (hSyl : Nat.card (Sylow 3 G) = 16) :
    Nat.card (Sylow 2 G) = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hCompl : {g : G | orderOf g ≠ 3}.ncard = 16 := by
    have hunion : {g : G | orderOf g = 3} ∪ {g : G | orderOf g ≠ 3} = Set.univ := by
      ext g; simp [em]
    have hdisj : Disjoint {g : G | orderOf g = 3} {g : G | orderOf g ≠ 3} :=
      Set.disjoint_left.mpr fun g hg hg' => hg' hg
    have hcard32 := card_orderOf_eq_three hG hSyl
    have htotal : Set.ncard (Set.univ : Set G) = 48 := by
      rw [Set.ncard_univ]; exact hG
    have := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
    rw [hunion] at this
    omega
  suffices h : ∀ P Q : Sylow 2 G, P = Q by
    exact Nat.card_eq_one_iff_unique.mpr ⟨⟨h⟩, (Sylow.nonempty : Nonempty (Sylow 2 G))⟩
  intro P Q
  apply Sylow.ext
  have hkey : ∀ R : Sylow 2 G, (↑(↑R : Subgroup G) : Set G) = {g : G | orderOf g ≠ 3} := by
    intro R
    have hR16 := card_sylow_two_subgroup_of_card_48 hG R
    have hsub : (↑(↑R : Subgroup G) : Set G) ⊆ {g : G | orderOf g ≠ 3} := by
      intro x hxR hx3
      have hdvd : orderOf x ∣ Nat.card (↑R : Subgroup G) := Subgroup.orderOf_dvd_natCard _ hxR
      rw [hR16, hx3] at hdvd
      norm_num at hdvd
    have hcardR : (↑(↑R : Subgroup G) : Set G).ncard = 16 := by
      rw [← Nat.card_coe_set_eq]; exact hR16
    exact Set.eq_of_subset_of_ncard_le hsub (by rw [hcardR, hCompl]) (Set.toFinite _)
  apply SetLike.coe_injective
  rw [hkey P, hkey Q]

/-! ### The bundled trichotomy -/

/-- **The first Sylow trichotomy for groups of order `48`.**  Either the Sylow
`3`-subgroup is normal (`n₃ = 1`), or `n₃ = 4` (the residual case), or there
are `16` Sylow `3`-subgroups and the Sylow `2`-subgroup is normal. -/
theorem order48_sylow_trichotomy [Finite G] (hG : Nat.card G = 48) :
    (∀ P : Sylow 3 G, (↑P : Subgroup G).Normal) ∨
      Nat.card (Sylow 3 G) = 4 ∨
      (Nat.card (Sylow 3 G) = 16 ∧ ∀ P : Sylow 2 G, (↑P : Subgroup G).Normal) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rcases card_sylow_three_of_card_48 hG with h1 | h4 | h16
  · exact Or.inl (fun P => sylow_three_normal_of_card_sylow_three_eq_one h1 P)
  · exact Or.inr (Or.inl h4)
  · refine Or.inr (Or.inr ⟨h16, fun P => ?_⟩)
    haveI : Subsingleton (Sylow 2 G) :=
      (Nat.card_eq_one_iff_unique.mp
        (card_sylow_two_eq_one_of_card_sylow_three_eq_sixteen hG h16)).1
    exact Sylow.normal_of_subsingleton P

end Smallgroups.UsefulTheorems
