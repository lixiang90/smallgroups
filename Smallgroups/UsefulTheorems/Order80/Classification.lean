/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order80.UniqueSylowFive_Summary
import Smallgroups.UsefulTheorems.Order80.SixteenSylowFive
import Smallgroups.UsefulTheorems.Counting

/-!
# The 52 groups of order 80

This file combines the two branches of `order80_sylow_dichotomy` into the full
classification of groups of order `80`:

* the Sylow-`5`-normal branch (`n₅ = 1`): `51` classes, from
  `Order80/UniqueSylowFive_Summary.lean`
  (`order80_normal_reps` indexed by `Σ k : Fin 14, Fin (order80_normal_counts k)`);
* the sixteen-Sylow-`5` branch (`n₅ = 16`): the single class
  `order80_nonnormal_rep = (C₂)⁴ ⋊[φ₀] C₅`, from `Order80/SixteenSylowFive.lean`.

The two branches are disjoint because the number of Sylow-`5` subgroups is an
isomorphism invariant (`card_sylow_of_mulEquiv`): every representative of the
first branch has `n₅ = 1` (`order80_normal_reps_sylow_five` — its `C₅` factor
is a normal Sylow-`5` subgroup), while `order80_nonnormal_rep` has `n₅ = 16`
(`order80_nonnormal_rep_sylow_five`).

Main results (the standard three-theorem package plus the bundling):

* `order80_classification` — **Exhaustiveness**: every group of order `80` is
  isomorphic to one of the `52` representatives `order80_reps i`;
* `order80_reps_pairwise` — **Distinctness**: the `52` representatives are
  pairwise non-isomorphic;
* `order80_classCount` — **Counting**: the index type has exactly `52`
  elements;
* `order80_isClassif : IsClassif 80 order80_reps` — the bundled statement:
  **there are exactly `52` isomorphism classes of groups of order `80`.**
-/

namespace Smallgroups.UsefulTheorems

open Sylow

/-! ### Every Sylow-5-normal representative has `n₅ = 1`

Each `order80_normal_reps k i = C₅ ⋊[χ] K` contains its `C₅` factor as a
normal subgroup of order `5`, which is therefore the unique Sylow-`5`
subgroup. -/

/-- A group of order `80` with a normal subgroup of order `5` has a unique
Sylow-`5` subgroup. -/
theorem card_sylow_five_eq_one_of_normal {H : Type*} [Group H] [Finite H]
    (hcard : Nat.card H = 80) (N : Subgroup H) (hnorm : N.Normal)
    (h5 : Nat.card N = 5) : Nat.card (Sylow 5 H) = 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rcases card_sylow_five_of_card_80 hcard with h1 | h16
  · exact h1
  · exfalso
    have hp : IsPGroup 5 N := IsPGroup.of_card (by rw [h5, pow_one])
    obtain ⟨Q, hle⟩ := hp.exists_le_sylow
    have hQ5 : Nat.card (↑Q : Subgroup H) = 5 := card_sylow_five_subgroup_of_card_80 hcard Q
    have heq : N = ↑Q := eq_of_le_of_card_eq hle (by rw [h5, hQ5])
    haveI : Finite (Sylow 5 H) := Nat.finite_of_card_ne_zero (by rw [h16]; norm_num)
    have hidx := Q.card_eq_index_normalizer
    rw [h16] at hidx
    haveI : (↑Q : Subgroup H).Normal := heq ▸ hnorm
    have htop : Subgroup.normalizer (Q : Set H) = ⊤ := by
      rw [← Sylow.coe_coe]
      exact Subgroup.normalizer_eq_top (H := (↑Q : Subgroup H))
    rw [htop, Subgroup.index_top] at hidx
    norm_num at hidx

/-- Each representative of the Sylow-`5`-normal branch has a unique Sylow-`5`
subgroup: the canonical copy of `C₅` is normal of order `5`. -/
theorem order80_normal_reps_sylow_five (k : Fin 14) (i : Fin (order80_normal_counts k)) :
    Nat.card (Sylow 5 (order80_normal_reps k i)) = 1 := by
  change Nat.card (Sylow 5 (SemidirectProduct (Multiplicative (ZMod 5)) (order80_normal_K k)
    (unitAutHom.comp (order80_normal_chi k i)))) = 1
  have hcard : Nat.card (SemidirectProduct (Multiplicative (ZMod 5)) (order80_normal_K k)
      (unitAutHom.comp (order80_normal_chi k i))) = 80 := order80_normal_reps_card k i
  haveI : Finite (SemidirectProduct (Multiplicative (ZMod 5)) (order80_normal_K k)
      (unitAutHom.comp (order80_normal_chi k i))) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  refine card_sylow_five_eq_one_of_normal hcard
    (SemidirectProduct.inl (φ := unitAutHom.comp (order80_normal_chi k i))).range ?_ ?_
  · rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    exact MonoidHom.normal_ker _
  · exact (Nat.card_congr
      (MonoidHom.ofInjective SemidirectProduct.inl_injective).toEquiv).symm.trans
      order80_normal_c5_card

/-- **The two branches are disjoint**: no Sylow-`5`-normal representative is
isomorphic to `order80_nonnormal_rep`, since `n₅` is `1` for the former and
`16` for the latter. -/
theorem order80_normal_nonnormal_disjoint (k : Fin 14) (i : Fin (order80_normal_counts k)) :
    ¬ Nonempty (order80_normal_reps k i ≃* order80_nonnormal_rep) := by
  rintro ⟨e⟩
  have h := card_sylow_of_mulEquiv 5 e
  rw [order80_normal_reps_sylow_five, order80_nonnormal_rep_sylow_five] at h
  norm_num at h

/-! ### The 52 representatives, indexed by `Fin 52`

`IsClassif` requires a `Fin`-indexed family, so we lay the `51` classes of the
normal branch out in lexicographic order and append the non-normal class as
index `51`.  `order80_reps` is *defined* through the explicit index map
`order80_index`, so the `Sum.elim` structure is definitionally available for
transporting distinctness and exhaustiveness. -/

/-- The index translation `Fin 52 → (Σ k, Fin (order80_normal_counts k)) ⊕ Fin 1`:
indices `0`–`50` enumerate the Sylow-`5`-normal classes in lexicographic order
`(k, i)`, and `51` is the non-normal class. -/
noncomputable abbrev order80_index :
    Fin 52 → (Σ k : Fin 14, Fin (order80_normal_counts k)) ⊕ Fin 1
  | 0 => Sum.inl ⟨0, ⟨0, by decide⟩⟩
  | 1 => Sum.inl ⟨0, ⟨1, by decide⟩⟩
  | 2 => Sum.inl ⟨1, ⟨0, by decide⟩⟩
  | 3 => Sum.inl ⟨1, ⟨1, by decide⟩⟩
  | 4 => Sum.inl ⟨1, ⟨2, by decide⟩⟩
  | 5 => Sum.inl ⟨1, ⟨3, by decide⟩⟩
  | 6 => Sum.inl ⟨1, ⟨4, by decide⟩⟩
  | 7 => Sum.inl ⟨2, ⟨0, by decide⟩⟩
  | 8 => Sum.inl ⟨2, ⟨1, by decide⟩⟩
  | 9 => Sum.inl ⟨2, ⟨2, by decide⟩⟩
  | 10 => Sum.inl ⟨2, ⟨3, by decide⟩⟩
  | 11 => Sum.inl ⟨3, ⟨0, by decide⟩⟩
  | 12 => Sum.inl ⟨3, ⟨1, by decide⟩⟩
  | 13 => Sum.inl ⟨3, ⟨2, by decide⟩⟩
  | 14 => Sum.inl ⟨3, ⟨3, by decide⟩⟩
  | 15 => Sum.inl ⟨3, ⟨4, by decide⟩⟩
  | 16 => Sum.inl ⟨4, ⟨0, by decide⟩⟩
  | 17 => Sum.inl ⟨4, ⟨1, by decide⟩⟩
  | 18 => Sum.inl ⟨4, ⟨2, by decide⟩⟩
  | 19 => Sum.inl ⟨5, ⟨0, by decide⟩⟩
  | 20 => Sum.inl ⟨5, ⟨1, by decide⟩⟩
  | 21 => Sum.inl ⟨5, ⟨2, by decide⟩⟩
  | 22 => Sum.inl ⟨6, ⟨0, by decide⟩⟩
  | 23 => Sum.inl ⟨6, ⟨1, by decide⟩⟩
  | 24 => Sum.inl ⟨6, ⟨2, by decide⟩⟩
  | 25 => Sum.inl ⟨7, ⟨0, by decide⟩⟩
  | 26 => Sum.inl ⟨7, ⟨1, by decide⟩⟩
  | 27 => Sum.inl ⟨7, ⟨2, by decide⟩⟩
  | 28 => Sum.inl ⟨7, ⟨3, by decide⟩⟩
  | 29 => Sum.inl ⟨8, ⟨0, by decide⟩⟩
  | 30 => Sum.inl ⟨8, ⟨1, by decide⟩⟩
  | 31 => Sum.inl ⟨8, ⟨2, by decide⟩⟩
  | 32 => Sum.inl ⟨8, ⟨3, by decide⟩⟩
  | 33 => Sum.inl ⟨9, ⟨0, by decide⟩⟩
  | 34 => Sum.inl ⟨9, ⟨1, by decide⟩⟩
  | 35 => Sum.inl ⟨9, ⟨2, by decide⟩⟩
  | 36 => Sum.inl ⟨9, ⟨3, by decide⟩⟩
  | 37 => Sum.inl ⟨10, ⟨0, by decide⟩⟩
  | 38 => Sum.inl ⟨10, ⟨1, by decide⟩⟩
  | 39 => Sum.inl ⟨10, ⟨2, by decide⟩⟩
  | 40 => Sum.inl ⟨10, ⟨3, by decide⟩⟩
  | 41 => Sum.inl ⟨11, ⟨0, by decide⟩⟩
  | 42 => Sum.inl ⟨11, ⟨1, by decide⟩⟩
  | 43 => Sum.inl ⟨11, ⟨2, by decide⟩⟩
  | 44 => Sum.inl ⟨12, ⟨0, by decide⟩⟩
  | 45 => Sum.inl ⟨12, ⟨1, by decide⟩⟩
  | 46 => Sum.inl ⟨12, ⟨2, by decide⟩⟩
  | 47 => Sum.inl ⟨12, ⟨3, by decide⟩⟩
  | 48 => Sum.inl ⟨13, ⟨0, by decide⟩⟩
  | 49 => Sum.inl ⟨13, ⟨1, by decide⟩⟩
  | 50 => Sum.inl ⟨13, ⟨2, by decide⟩⟩
  | _ => Sum.inr 0

/-- The inverse translation on the normal-branch indices. -/
noncomputable def order80_sigmaIndex :
    (Σ k : Fin 14, Fin (order80_normal_counts k)) → Fin 52
  | ⟨0, ⟨0, _⟩⟩ => 0
  | ⟨0, ⟨1, _⟩⟩ => 1
  | ⟨1, ⟨0, _⟩⟩ => 2
  | ⟨1, ⟨1, _⟩⟩ => 3
  | ⟨1, ⟨2, _⟩⟩ => 4
  | ⟨1, ⟨3, _⟩⟩ => 5
  | ⟨1, ⟨4, _⟩⟩ => 6
  | ⟨2, ⟨0, _⟩⟩ => 7
  | ⟨2, ⟨1, _⟩⟩ => 8
  | ⟨2, ⟨2, _⟩⟩ => 9
  | ⟨2, ⟨3, _⟩⟩ => 10
  | ⟨3, ⟨0, _⟩⟩ => 11
  | ⟨3, ⟨1, _⟩⟩ => 12
  | ⟨3, ⟨2, _⟩⟩ => 13
  | ⟨3, ⟨3, _⟩⟩ => 14
  | ⟨3, ⟨4, _⟩⟩ => 15
  | ⟨4, ⟨0, _⟩⟩ => 16
  | ⟨4, ⟨1, _⟩⟩ => 17
  | ⟨4, ⟨2, _⟩⟩ => 18
  | ⟨5, ⟨0, _⟩⟩ => 19
  | ⟨5, ⟨1, _⟩⟩ => 20
  | ⟨5, ⟨2, _⟩⟩ => 21
  | ⟨6, ⟨0, _⟩⟩ => 22
  | ⟨6, ⟨1, _⟩⟩ => 23
  | ⟨6, ⟨2, _⟩⟩ => 24
  | ⟨7, ⟨0, _⟩⟩ => 25
  | ⟨7, ⟨1, _⟩⟩ => 26
  | ⟨7, ⟨2, _⟩⟩ => 27
  | ⟨7, ⟨3, _⟩⟩ => 28
  | ⟨8, ⟨0, _⟩⟩ => 29
  | ⟨8, ⟨1, _⟩⟩ => 30
  | ⟨8, ⟨2, _⟩⟩ => 31
  | ⟨8, ⟨3, _⟩⟩ => 32
  | ⟨9, ⟨0, _⟩⟩ => 33
  | ⟨9, ⟨1, _⟩⟩ => 34
  | ⟨9, ⟨2, _⟩⟩ => 35
  | ⟨9, ⟨3, _⟩⟩ => 36
  | ⟨10, ⟨0, _⟩⟩ => 37
  | ⟨10, ⟨1, _⟩⟩ => 38
  | ⟨10, ⟨2, _⟩⟩ => 39
  | ⟨10, ⟨3, _⟩⟩ => 40
  | ⟨11, ⟨0, _⟩⟩ => 41
  | ⟨11, ⟨1, _⟩⟩ => 42
  | ⟨11, ⟨2, _⟩⟩ => 43
  | ⟨12, ⟨0, _⟩⟩ => 44
  | ⟨12, ⟨1, _⟩⟩ => 45
  | ⟨12, ⟨2, _⟩⟩ => 46
  | ⟨12, ⟨3, _⟩⟩ => 47
  | ⟨13, ⟨0, _⟩⟩ => 48
  | ⟨13, ⟨1, _⟩⟩ => 49
  | ⟨13, ⟨2, _⟩⟩ => 50

theorem order80_index_injective : Function.Injective order80_index := by decide

theorem order80_index_sigmaIndex (s : Σ k : Fin 14, Fin (order80_normal_counts k)) :
    order80_index (order80_sigmaIndex s) = Sum.inl s := by revert s; decide

/-- **The 52 isomorphism classes of groups of order 80.** Indices `0`–`50` are
the Sylow-`5`-normal classes `order80_normal_reps k i` (in lexicographic order
of `(k, i)`), and index `51` is `order80_nonnormal_rep = (C₂)⁴ ⋊[φ₀] C₅`. -/
noncomputable abbrev order80_reps (n : Fin 52) : Type :=
  Sum.elim
    (fun s : Σ k : Fin 14, Fin (order80_normal_counts k) => order80_normal_reps s.1 s.2)
    (fun _ : Fin 1 => order80_nonnormal_rep) (order80_index n)

noncomputable instance order80_reps_group (n : Fin 52) : Group (order80_reps n) :=
  inferInstanceAs (Group (Sum.elim _ _ (order80_index n)))

/-- Each of the 52 representatives has order `80`. -/
theorem order80_reps_card (n : Fin 52) : Nat.card (order80_reps n) = 80 := by
  change Nat.card (Sum.elim _ _ (order80_index n)) = 80
  cases order80_index n with
  | inl s => exact order80_normal_reps_card s.1 s.2
  | inr _ => exact order80_nonnormal_rep_card

/-- **Distinctness.** The 52 representatives are pairwise non-isomorphic. -/
theorem order80_reps_pairwise : PairwiseNonMulEquiv order80_reps := by
  have hsum : PairwiseNonMulEquiv (Sum.elim
      (fun s : Σ k : Fin 14, Fin (order80_normal_counts k) => order80_normal_reps s.1 s.2)
      (fun _ : Fin 1 => order80_nonnormal_rep)) :=
    PairwiseNonMulEquiv.sum order80_normal_reps_pairwise
      (fun i j _ => Subsingleton.elim i j)
      (fun s j => order80_normal_nonnormal_disjoint s.1 s.2)
  intro i j h
  exact order80_index_injective (hsum (order80_index i) (order80_index j) h)

set_option maxHeartbeats 1600000 in
-- the `51` `fin_cases` branches each check a definitional reduction of the `52`-arm index
-- match against the corresponding representative, which exceeds the default budget
/-- **Exhaustiveness.** Every group of order `80` is isomorphic to one of the
52 representatives. -/
theorem order80_classification (G : Type) [Group G] (hG : Nat.card G = 80) :
    ∃ n : Fin 52, Nonempty (G ≃* order80_reps n) := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  rcases card_sylow_five_of_card_80 hG with h1 | h16
  · obtain ⟨k, i, hiso⟩ := order80_normal_classification hG h1
    -- with concrete `(k, i)` the index match reduces definitionally, so each of the `51`
    -- branches is closed by `hiso` at the corresponding `Fin 52` literal
    fin_cases k <;> fin_cases i
    exacts [
      ⟨(0 : Fin 52), hiso⟩, ⟨(1 : Fin 52), hiso⟩, ⟨(2 : Fin 52), hiso⟩, ⟨(3 : Fin 52), hiso⟩,
      ⟨(4 : Fin 52), hiso⟩, ⟨(5 : Fin 52), hiso⟩, ⟨(6 : Fin 52), hiso⟩, ⟨(7 : Fin 52), hiso⟩,
      ⟨(8 : Fin 52), hiso⟩, ⟨(9 : Fin 52), hiso⟩, ⟨(10 : Fin 52), hiso⟩, ⟨(11 : Fin 52), hiso⟩,
      ⟨(12 : Fin 52), hiso⟩, ⟨(13 : Fin 52), hiso⟩, ⟨(14 : Fin 52), hiso⟩, ⟨(15 : Fin 52), hiso⟩,
      ⟨(16 : Fin 52), hiso⟩, ⟨(17 : Fin 52), hiso⟩, ⟨(18 : Fin 52), hiso⟩, ⟨(19 : Fin 52), hiso⟩,
      ⟨(20 : Fin 52), hiso⟩, ⟨(21 : Fin 52), hiso⟩, ⟨(22 : Fin 52), hiso⟩, ⟨(23 : Fin 52), hiso⟩,
      ⟨(24 : Fin 52), hiso⟩, ⟨(25 : Fin 52), hiso⟩, ⟨(26 : Fin 52), hiso⟩, ⟨(27 : Fin 52), hiso⟩,
      ⟨(28 : Fin 52), hiso⟩, ⟨(29 : Fin 52), hiso⟩, ⟨(30 : Fin 52), hiso⟩, ⟨(31 : Fin 52), hiso⟩,
      ⟨(32 : Fin 52), hiso⟩, ⟨(33 : Fin 52), hiso⟩, ⟨(34 : Fin 52), hiso⟩, ⟨(35 : Fin 52), hiso⟩,
      ⟨(36 : Fin 52), hiso⟩, ⟨(37 : Fin 52), hiso⟩, ⟨(38 : Fin 52), hiso⟩, ⟨(39 : Fin 52), hiso⟩,
      ⟨(40 : Fin 52), hiso⟩, ⟨(41 : Fin 52), hiso⟩, ⟨(42 : Fin 52), hiso⟩, ⟨(43 : Fin 52), hiso⟩,
      ⟨(44 : Fin 52), hiso⟩, ⟨(45 : Fin 52), hiso⟩, ⟨(46 : Fin 52), hiso⟩, ⟨(47 : Fin 52), hiso⟩,
      ⟨(48 : Fin 52), hiso⟩, ⟨(49 : Fin 52), hiso⟩, ⟨(50 : Fin 52), hiso⟩]
  · exact ⟨⟨51, by norm_num⟩, order80_sixteen_sylow_classification hG h16⟩

/-- **Counting.** The index family has exactly `52` elements. -/
theorem order80_classCount : Nat.card (Fin 52) = 52 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fin]

/-- **The classification of groups of order 80**: the 52 representatives are a
complete, non-redundant list — there are exactly `52` isomorphism classes of
groups of order `80` (`51` with a normal Sylow-`5` subgroup, plus
`(C₂)⁴ ⋊ C₅`). -/
theorem order80_isClassif : IsClassif 80 order80_reps where
  card := order80_reps_card
  complete := order80_classification
  distinct := order80_reps_pairwise

end Smallgroups.UsefulTheorems
