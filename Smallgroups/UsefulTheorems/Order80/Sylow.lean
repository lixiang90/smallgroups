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

/-!
# Groups of order 80: the first Sylow dichotomy

`80 = 2⁴ · 5`.  This file proves the classical first step towards classifying
groups of order `80`.  By Sylow's theorem, the number `n₅` of Sylow
`5`-subgroups divides `16` and is `≡ 1 (mod 5)`, so `n₅ = 1` or `n₅ = 16`.

* If `n₅ = 1`, the Sylow `5`-subgroup is normal.
* If `n₅ = 16`, a counting argument shows every Sylow `2`-subgroup is normal:
  the `16` Sylow `5`-subgroups pairwise intersect trivially (their order `5`
  is prime), contributing `16 * 4 = 64` distinct elements of order `5`.  This
  leaves exactly `80 - 64 = 16` elements whose order is not `5` -- precisely
  the size of a Sylow `2`-subgroup, none of whose elements can have order `5`
  (their order divides `16`).  Hence every Sylow `2`-subgroup coincides with
  this fixed set of `16` elements, so there is only one.

Main results:

* `card_sylow_five_of_card_80`: `n₅ = 1 ∨ n₅ = 16`;
* `sylow_five_normal_of_card_sylow_five_eq_one`: if `n₅ = 1` the Sylow
  `5`-subgroup is normal;
* `card_sylow_two_eq_one_of_card_sylow_five_eq_sixteen`: if `n₅ = 16` then
  `n₂ = 1`;
* `order80_sylow_dichotomy`: the bundled dichotomy.
-/

namespace Smallgroups.UsefulTheorems

open Sylow

variable {G : Type*} [Group G]

/-! ### A general helper: a subgroup containment with equal (finite) cardinality is equality. -/

theorem eq_of_le_of_card_eq [Finite G] {H K : Subgroup G} (hle : H ≤ K)
    (hcard : Nat.card H = Nat.card K) : H = K := by
  apply SetLike.coe_injective
  have hH : Nat.card H = (↑H : Set G).ncard := Nat.card_coe_set_eq (↑H : Set G)
  have hK : Nat.card K = (↑K : Set G).ncard := Nat.card_coe_set_eq (↑K : Set G)
  exact Set.eq_of_subset_of_ncard_le (SetLike.coe_subset_coe.mpr hle) (by omega)

/-! ### Step 1: the number of Sylow `5`-subgroups is `1` or `16`. -/

theorem card_sylow_five_of_card_80 [Finite G] (hG : Nat.card G = 80) :
    Nat.card (Sylow 5 G) = 1 ∨ Nat.card (Sylow 5 G) = 16 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 5 G))
  have hndvd_5 : ¬ 5 ∣ Nat.card (Sylow 5 G) := not_dvd_card_sylow 5 G
  have hdvd80 : Nat.card (Sylow 5 G) ∣ 80 := by
    rw [← hG]
    exact P0.card_dvd_index.trans (Subgroup.index_dvd_card _)
  have h80 : 80 = 16 * 5 := by norm_num
  have hdvd16_mul : Nat.card (Sylow 5 G) ∣ 16 * 5 := by simpa [h80] using hdvd80
  have hp5 : Nat.Prime 5 := by norm_num
  have hcop : Nat.Coprime (Nat.card (Sylow 5 G)) 5 :=
    (hp5.coprime_iff_not_dvd.mpr hndvd_5).symm
  have hdvd16 : Nat.card (Sylow 5 G) ∣ 16 := hcop.dvd_of_dvd_mul_right hdvd16_mul
  have hmod := card_sylow_modEq_one 5 G
  have hle : Nat.card (Sylow 5 G) ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd16
  have hpos : 0 < Nat.card (Sylow 5 G) := Nat.card_pos
  interval_cases h : Nat.card (Sylow 5 G) <;>
    first
      | exact Or.inl rfl
      | exact Or.inr rfl
      | (unfold Nat.ModEq at hmod; norm_num at hmod; done)
      | (norm_num at hdvd16)

/-- A Sylow `5`-subgroup of a group of order `80` has order `5`. -/
theorem card_sylow_five_subgroup_of_card_80 [Finite G] (hG : Nat.card G = 80)
    (P : Sylow 5 G) : Nat.card (↑P : Subgroup G) = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hndvd : ¬ (5 : ℕ) ∣ 16 := by norm_num
  have hfact : (80 : ℕ).factorization 5 = 1 := by
    rw [show (80 : ℕ) = 16 * 5 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hndvd,
      Nat.Prime.factorization_self (by norm_num : Nat.Prime 5), zero_add]
  rw [Sylow.card_eq_multiplicity, hG, hfact, pow_one]

/-- A Sylow `2`-subgroup of a group of order `80` has order `16`. -/
theorem card_sylow_two_subgroup_of_card_80 [Finite G] (hG : Nat.card G = 80)
    (P : Sylow 2 G) : Nat.card (↑P : Subgroup G) = 16 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hndvd : ¬ (2 : ℕ) ∣ 5 := by norm_num
  have hfact : (80 : ℕ).factorization 2 = 4 := by
    rw [show (80 : ℕ) = 2 ^ 4 * 5 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self (by norm_num : Nat.Prime 2),
      Nat.factorization_eq_zero_of_not_dvd hndvd]
  rw [Sylow.card_eq_multiplicity, hG, hfact]
  norm_num

/-! ### Step 2: if `n₅ = 1`, the Sylow `5`-subgroup is normal. -/

theorem sylow_five_normal_of_card_sylow_five_eq_one [Finite G]
    (hSyl : Nat.card (Sylow 5 G) = 1) (P : Sylow 5 G) : (↑P : Subgroup G).Normal := by
  haveI : Subsingleton (Sylow 5 G) := (Nat.card_eq_one_iff_unique.mp hSyl).1
  exact Sylow.normal_of_subsingleton P

/-! ### Step 3: if `n₅ = 16`, the Sylow `2`-subgroup is normal. -/

/-- Distinct Sylow `5`-subgroups of a group of order `80` intersect trivially:
their common order `5` is prime, so any nontrivial intersection would force
them to be equal. -/
theorem sylow_five_disjoint_of_ne [Finite G] (hG : Nat.card G = 80)
    {P Q : Sylow 5 G} (hne : P ≠ Q) : Disjoint (↑P : Subgroup G) (↑Q : Subgroup G) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hp5 : Nat.Prime 5 := by norm_num
  have hP5 := card_sylow_five_subgroup_of_card_80 hG P
  have hQ5 := card_sylow_five_subgroup_of_card_80 hG Q
  have hdvd : Nat.card (↥((↑P : Subgroup G) ⊓ ↑Q)) ∣ Nat.card (↥(↑P : Subgroup G)) :=
    Subgroup.card_dvd_of_le inf_le_left
  rw [hP5] at hdvd
  rcases (Nat.dvd_prime hp5).mp hdvd with h1 | h5
  · exact disjoint_iff.mpr (Subgroup.card_eq_one.mp h1)
  · exfalso
    apply hne
    apply Sylow.ext
    have heqP : (↑P : Subgroup G) ⊓ ↑Q = ↑P :=
      eq_of_le_of_card_eq inf_le_left (h5.trans hP5.symm)
    have hPQ : (↑P : Subgroup G) ≤ ↑Q := heqP ▸ inf_le_right
    exact eq_of_le_of_card_eq hPQ (hP5.trans hQ5.symm)

/-- The set of nonidentity elements of a Sylow `5`-subgroup. -/
private def sylowFiveNonId (P : Sylow 5 G) : Set G := (↑(↑P : Subgroup G) : Set G) \ {1}

private theorem sylowFiveNonId_pairwiseDisjoint [Finite G] (hG : Nat.card G = 80) :
    Pairwise (fun P Q : Sylow 5 G => Disjoint (sylowFiveNonId P) (sylowFiveNonId Q)) := by
  intro P Q hne
  have hbot : (↑P : Subgroup G) ⊓ ↑Q = ⊥ := disjoint_iff.mp (sylow_five_disjoint_of_ne hG hne)
  apply Set.disjoint_left.mpr
  intro x hxP hxQ
  have hxPQ : x ∈ (↑P : Subgroup G) ⊓ ↑Q := ⟨hxP.1, hxQ.1⟩
  rw [hbot] at hxPQ
  exact hxQ.2 (Subgroup.mem_bot.mp hxPQ)

private theorem sylowFiveNonId_ncard [Finite G] (hG : Nat.card G = 80) (P : Sylow 5 G) :
    (sylowFiveNonId P).ncard = 4 := by
  have hP5 := card_sylow_five_subgroup_of_card_80 hG P
  have hcard : (↑(↑P : Subgroup G) : Set G).ncard = 5 := by
    rw [← Nat.card_coe_set_eq]; exact hP5
  have hmem : (1 : G) ∈ (↑(↑P : Subgroup G) : Set G) := Subgroup.one_mem _
  rw [sylowFiveNonId, Set.ncard_sdiff_singleton_of_mem hmem, hcard]

/-- The set of order-`5` elements in a group of order `80` with `16` Sylow
`5`-subgroups is exactly the union of their nonidentity elements. -/
private theorem orderOf_eq_five_iff [Finite G] (hG : Nat.card G = 80) (g : G) :
    orderOf g = 5 ↔ ∃ P : Sylow 5 G, g ∈ sylowFiveNonId P := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  constructor
  · intro hg
    have hcard : Nat.card (Subgroup.zpowers g) = 5 := by rw [Nat.card_zpowers, hg]
    let P : Sylow 5 G := Sylow.ofCard (Subgroup.zpowers g) (by
      have hfact : (80 : ℕ).factorization 5 = 1 := by
        rw [show (80 : ℕ) = 16 * 5 by norm_num,
          Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
          Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (5 : ℕ) ∣ 16),
          Nat.Prime.factorization_self (by norm_num : Nat.Prime 5), zero_add]
      rw [hcard, hG, hfact, pow_one])
    refine ⟨P, ?_, ?_⟩
    · exact Subgroup.mem_zpowers g
    · intro hg1; rw [hg1, orderOf_one] at hg; norm_num at hg
  · rintro ⟨P, hgP, hg1⟩
    have hdvd : orderOf g ∣ Nat.card (↑P : Subgroup G) :=
      Subgroup.orderOf_dvd_natCard _ hgP
    rw [card_sylow_five_subgroup_of_card_80 hG P] at hdvd
    rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h1 | h5
    · exact absurd (orderOf_eq_one_iff.mp h1) hg1
    · exact h5

private theorem card_orderOf_eq_five [Finite G] (hG : Nat.card G = 80)
    (hSyl : Nat.card (Sylow 5 G) = 16) :
    {g : G | orderOf g = 5}.ncard = 64 := by
  have hset : {g : G | orderOf g = 5} = ⋃ P : Sylow 5 G, sylowFiveNonId P := by
    ext g; simp [orderOf_eq_five_iff hG]
  have hFinIdx : Finite (Sylow 5 G) := Nat.finite_of_card_ne_zero (by rw [hSyl]; norm_num)
  haveI := Fintype.ofFinite (Sylow 5 G)
  rw [hset, Set.ncard_iUnion_of_finite (fun P => Set.toFinite _)
    (sylowFiveNonId_pairwiseDisjoint hG)]
  rw [finsum_eq_sum_of_fintype]
  rw [Finset.sum_congr rfl (fun P _ => sylowFiveNonId_ncard hG P)]
  rw [Finset.sum_const, Finset.card_univ]
  have : Fintype.card (Sylow 5 G) = 16 := by rw [← Nat.card_eq_fintype_card]; exact hSyl
  rw [this]
  rfl

/-- If a group of order `80` has `16` Sylow `5`-subgroups, then it has a unique
(hence normal) Sylow `2`-subgroup. -/
theorem card_sylow_two_eq_one_of_card_sylow_five_eq_sixteen [Finite G]
    (hG : Nat.card G = 80) (hSyl : Nat.card (Sylow 5 G) = 16) :
    Nat.card (Sylow 2 G) = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hCompl : {g : G | orderOf g ≠ 5}.ncard = 16 := by
    have hunion : {g : G | orderOf g = 5} ∪ {g : G | orderOf g ≠ 5} = Set.univ := by
      ext g; simp [em]
    have hdisj : Disjoint {g : G | orderOf g = 5} {g : G | orderOf g ≠ 5} :=
      Set.disjoint_left.mpr fun g hg hg' => hg' hg
    have hcard64 := card_orderOf_eq_five hG hSyl
    have htotal : Set.ncard (Set.univ : Set G) = 80 := by
      rw [Set.ncard_univ]; exact hG
    have := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
    rw [hunion] at this
    omega
  suffices h : ∀ P Q : Sylow 2 G, P = Q by
    exact Nat.card_eq_one_iff_unique.mpr ⟨⟨h⟩, (Sylow.nonempty : Nonempty (Sylow 2 G))⟩
  intro P Q
  apply Sylow.ext
  have hkey : ∀ R : Sylow 2 G, (↑(↑R : Subgroup G) : Set G) = {g : G | orderOf g ≠ 5} := by
    intro R
    have hR16 := card_sylow_two_subgroup_of_card_80 hG R
    have hsub : (↑(↑R : Subgroup G) : Set G) ⊆ {g : G | orderOf g ≠ 5} := by
      intro x hxR hx5
      have hdvd : orderOf x ∣ Nat.card (↑R : Subgroup G) := Subgroup.orderOf_dvd_natCard _ hxR
      rw [hR16, hx5] at hdvd
      norm_num at hdvd
    have hcardR : (↑(↑R : Subgroup G) : Set G).ncard = 16 := by
      rw [← Nat.card_coe_set_eq]; exact hR16
    exact Set.eq_of_subset_of_ncard_le hsub (by rw [hcardR, hCompl]) (Set.toFinite _)
  apply SetLike.coe_injective
  rw [hkey P, hkey Q]

/-! ### The bundled dichotomy -/

/-- **The first Sylow dichotomy for groups of order `80`.**  Either the Sylow
`5`-subgroup is normal, or there are `16` Sylow `5`-subgroups and the Sylow
`2`-subgroup is normal. -/
theorem order80_sylow_dichotomy [Finite G] (hG : Nat.card G = 80) :
    (∀ P : Sylow 5 G, (↑P : Subgroup G).Normal) ∨
      (Nat.card (Sylow 5 G) = 16 ∧ ∀ P : Sylow 2 G, (↑P : Subgroup G).Normal) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rcases card_sylow_five_of_card_80 hG with h1 | h16
  · exact Or.inl (fun P => sylow_five_normal_of_card_sylow_five_eq_one h1 P)
  · refine Or.inr ⟨h16, fun P => ?_⟩
    haveI : Subsingleton (Sylow 2 G) :=
      (Nat.card_eq_one_iff_unique.mp (card_sylow_two_eq_one_of_card_sylow_five_eq_sixteen hG h16)).1
    exact Sylow.normal_of_subsingleton P

end Smallgroups.UsefulTheorems
