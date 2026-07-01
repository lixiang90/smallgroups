/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.AbelianPa
import Smallgroups.UsefulTheorems.AbelianPaUniqueness

/-!
# Abelian groups of order `p^4`

The structure theorem for finite abelian groups reduces the classification of abelian groups
of order `p^4` (for any prime `p`) to the **integer partitions of `4`**.  The five partitions

  `4`, `3+1`, `2+2`, `2+1+1`, `1+1+1+1`

correspond to the five abelian groups:

  `C_{p^4}`, `C_{p^3} × C_p`, `C_{p^2} × C_{p^2}`, `C_{p^2} × C_p × C_p`, `(C_p)^4`.

In particular, this file simultaneously handles the abelian part of order `16` (`p = 2`) and
order `81` (`p = 3`).

This file records the five representatives, proves they have order `p^4`, that every abelian
group of order `p^4` is isomorphic to one of them, and that they are pairwise non-isomorphic.
-/

namespace Smallgroups.UsefulTheorems

open scoped BigOperators

/-! ### The five partitions of `4` -/

/-- Partition `4` → `C_{p^4}`. -/
def part4 : Nat.Partition 4 :=
  ⟨{4}, by intro x hx; simp at hx; omega, by simp⟩

/-- Partition `3+1` → `C_{p^3} × C_p`. -/
def part31 : Nat.Partition 4 :=
  ⟨{3, 1}, by intro x hx; simp at hx; omega, by simp⟩

/-- Partition `2+2` → `C_{p^2} × C_{p^2}`. -/
def part22 : Nat.Partition 4 :=
  ⟨{2, 2}, by intro x hx; simp at hx; omega, by simp⟩

/-- Partition `2+1+1` → `C_{p^2} × C_p × C_p`. -/
def part211 : Nat.Partition 4 :=
  ⟨{2, 1, 1}, by intro x hx; simp at hx; omega, by simp⟩

/-- Partition `1+1+1+1` → `(C_p)^4`. -/
def part1111 : Nat.Partition 4 :=
  ⟨{1, 1, 1, 1}, by intro x hx; simp at hx; omega, by simp⟩

/-! ### Map from `Fin 5` to partitions -/

/-- Map a `Fin 5` index to the corresponding partition of `4`. -/
def idxToPartition : Fin 5 → Nat.Partition 4
  | 0 => part4
  | 1 => part31
  | 2 => part22
  | 3 => part211
  | 4 => part1111

lemma idxToPartition_injective : Function.Injective idxToPartition := by
  decide +kernel

/-! ### The five abelian representatives of order `p^4` -/

/-- The five-element representative family: `partitionGroup p` applied to each partition. -/
noncomputable abbrev orderP4Abel_reps (p : ℕ) (i : Fin 5) : Type :=
  partitionGroup p (idxToPartition i)

noncomputable instance instCommGroupOrderP4AbelRep (p : ℕ) (i : Fin 5) :
    CommGroup (orderP4Abel_reps p i) := inferInstance

/-! ### Named abbreviations for the five representatives (generic `p`) -/

/-- `C_{p^4}`. -/
noncomputable abbrev orderP4Abel_A1 (p : ℕ) : Type := orderP4Abel_reps p 0

/-- `C_{p^3} × C_p`. -/
noncomputable abbrev orderP4Abel_A2 (p : ℕ) : Type := orderP4Abel_reps p 1

/-- `C_{p^2} × C_{p^2}`. -/
noncomputable abbrev orderP4Abel_A3 (p : ℕ) : Type := orderP4Abel_reps p 2

/-- `C_{p^2} × C_p × C_p`. -/
noncomputable abbrev orderP4Abel_A4 (p : ℕ) : Type := orderP4Abel_reps p 3

/-- `(C_p)^4`. -/
noncomputable abbrev orderP4Abel_A5 (p : ℕ) : Type := orderP4Abel_reps p 4

/-! ### Named representatives for order `16` (p = 2) -/

noncomputable abbrev order16_A1 : Type := orderP4Abel_A1 2
noncomputable abbrev order16_A2 : Type := orderP4Abel_A2 2
noncomputable abbrev order16_A3 : Type := orderP4Abel_A3 2
noncomputable abbrev order16_A4 : Type := orderP4Abel_A4 2
noncomputable abbrev order16_A5 : Type := orderP4Abel_A5 2

/-! ### Named representatives for order `81` (p = 3) -/

noncomputable abbrev order81_A1 : Type := orderP4Abel_A1 3
noncomputable abbrev order81_A2 : Type := orderP4Abel_A2 3
noncomputable abbrev order81_A3 : Type := orderP4Abel_A3 3
noncomputable abbrev order81_A4 : Type := orderP4Abel_A4 3
noncomputable abbrev order81_A5 : Type := orderP4Abel_A5 3

/-! ### Cardinalities -/

/-- Each representative has cardinality `p^4`. -/
theorem card_orderP4Abel_reps (p : ℕ) [Fact p.Prime] (i : Fin 5) :
    Nat.card (orderP4Abel_reps p i) = p ^ 4 := by
  rw [orderP4Abel_reps, card_partitionGroup p (idxToPartition i)]

theorem card_orderP4Abel_A1 (p : ℕ) [Fact p.Prime] : Nat.card (orderP4Abel_A1 p) = p ^ 4 :=
  card_orderP4Abel_reps p 0

theorem card_orderP4Abel_A2 (p : ℕ) [Fact p.Prime] : Nat.card (orderP4Abel_A2 p) = p ^ 4 :=
  card_orderP4Abel_reps p 1

theorem card_orderP4Abel_A3 (p : ℕ) [Fact p.Prime] : Nat.card (orderP4Abel_A3 p) = p ^ 4 :=
  card_orderP4Abel_reps p 2

theorem card_orderP4Abel_A4 (p : ℕ) [Fact p.Prime] : Nat.card (orderP4Abel_A4 p) = p ^ 4 :=
  card_orderP4Abel_reps p 3

theorem card_orderP4Abel_A5 (p : ℕ) [Fact p.Prime] : Nat.card (orderP4Abel_A5 p) = p ^ 4 :=
  card_orderP4Abel_reps p 4

/-! ### Specialised cardinalities: order `16` -/

theorem card_order16_A1 : Nat.card order16_A1 = 16 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rw [order16_A1, card_orderP4Abel_A1 2]; norm_num

theorem card_order16_A2 : Nat.card order16_A2 = 16 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rw [order16_A2, card_orderP4Abel_A2 2]; norm_num

theorem card_order16_A3 : Nat.card order16_A3 = 16 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rw [order16_A3, card_orderP4Abel_A3 2]; norm_num

theorem card_order16_A4 : Nat.card order16_A4 = 16 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rw [order16_A4, card_orderP4Abel_A4 2]; norm_num

theorem card_order16_A5 : Nat.card order16_A5 = 16 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rw [order16_A5, card_orderP4Abel_A5 2]; norm_num

/-! ### Specialised cardinalities: order `81` -/

theorem card_order81_A1 : Nat.card order81_A1 = 81 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [order81_A1, card_orderP4Abel_A1 3]; norm_num

theorem card_order81_A2 : Nat.card order81_A2 = 81 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [order81_A2, card_orderP4Abel_A2 3]; norm_num

theorem card_order81_A3 : Nat.card order81_A3 = 81 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [order81_A3, card_orderP4Abel_A3 3]; norm_num

theorem card_order81_A4 : Nat.card order81_A4 = 81 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [order81_A4, card_orderP4Abel_A4 3]; norm_num

theorem card_order81_A5 : Nat.card order81_A5 = 81 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [order81_A5, card_orderP4Abel_A5 3]; norm_num

/-! ### Classification of partitions of `4` -/

set_option linter.style.nativeDecide false in
/-- Every integer partition of `4` is one of the five standard ones. -/
lemma partitions_of_four (lam : Nat.Partition 4) :
    lam = part4 ∨ lam = part31 ∨ lam = part22 ∨ lam = part211 ∨ lam = part1111 := by
  have h_all : (Finset.univ : Finset (Nat.Partition 4)) =
      {part4, part31, part22, part211, part1111} := by
    native_decide
  have h_mem : lam ∈ Finset.univ := Finset.mem_univ lam
  rw [h_all] at h_mem
  simp only [Finset.mem_insert, Finset.mem_singleton] at h_mem
  rcases h_mem with (rfl|rfl|rfl|rfl|rfl)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

/-! ### Completeness, distinctness, and the main classification -/

/-- Every abelian group of order `p^4` is isomorphic to one of the five standard representatives. -/
theorem orderP4Abel_complete (p : ℕ) [Fact p.Prime] (G : Type*) [CommGroup G]
    (hcard : Nat.card G = p ^ 4) : ∃ i, Nonempty (G ≃* orderP4Abel_reps p i) := by
  obtain ⟨lam, ⟨e⟩⟩ := abelian_pa_classification p 4 G hcard
  rcases partitions_of_four lam with rfl|rfl|rfl|rfl|rfl
  · exact ⟨0, ⟨e⟩⟩
  · exact ⟨1, ⟨e⟩⟩
  · exact ⟨2, ⟨e⟩⟩
  · exact ⟨3, ⟨e⟩⟩
  · exact ⟨4, ⟨e⟩⟩

/-- The five representatives are pairwise non-isomorphic. -/
theorem orderP4Abel_distinct (p : ℕ) [Fact p.Prime] (i j : Fin 5)
    (h : Nonempty (orderP4Abel_reps p i ≃* orderP4Abel_reps p j)) : i = j := by
  have hpart : idxToPartition i = idxToPartition j :=
    partitionGroup_distinct p h
  exact idxToPartition_injective hpart

/-- **Classification of abelian groups of order `p^4`.** There are exactly five isomorphism classes,
corresponding to the five partitions of `4`. -/
theorem orderP4Abel_classification (p : ℕ) [Fact p.Prime] :
    5 = Nat.card (Nat.Partition 4) := by
  have hcount := abelian_classCount p (orderP4Abel_reps p)
    (card_orderP4Abel_reps p) (orderP4Abel_complete p) (orderP4Abel_distinct p)
  simpa using hcount

end Smallgroups.UsefulTheorems
