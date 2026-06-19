/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases

/-!
# Counting isomorphism classes

This file provides the bookkeeping needed to turn an **exhaustiveness** theorem and a
**distinctness** theorem into a genuine statement about the *number* of isomorphism classes of
groups of a given order.

The number of classes of order `N` is packaged as a `Fin k`-indexed family `rep` of groups
together with the proof `IsClassif N rep` that the family is

* well-formed — each `rep i` has order `N`;
* **complete** (exhaustiveness) — every group of order `N` is isomorphic to some `rep i`;
* **non-redundant** (distinctness) — `rep i ≃* rep j` forces `i = j`.

The headline result is `IsClassif.card_unique`: **the number `k` is well defined**, i.e. any two
such lists for the same order have the same length.  Hence proving `IsClassif N rep` with
`rep : Fin k → Type` is exactly a proof that "there are exactly `k` isomorphism classes of groups
of order `N`", and it is built from the exhaustiveness and distinctness inputs.

`isClassif_one` and `isClassif_two` are the convenient constructors for the one- and two-class
cases used by the per-order files.
-/

namespace Smallgroups.UsefulTheorems

/-- `IsClassif N rep` states that the `Fin k`-indexed family of groups `rep` is a complete list of
pairwise non-isomorphic representatives of the isomorphism classes of groups of order `N`. -/
structure IsClassif (N : ℕ) {k : ℕ} (rep : Fin k → Type) [∀ i, Group (rep i)] : Prop where
  /-- Each representative is a group of order `N`. -/
  card : ∀ i, Nat.card (rep i) = N
  /-- **Exhaustiveness:** every group of order `N` is one of the representatives. -/
  complete : ∀ (G : Type) [Group G], Nat.card G = N → ∃ i, Nonempty (G ≃* rep i)
  /-- **Distinctness:** the representatives are pairwise non-isomorphic. -/
  distinct : ∀ i j, Nonempty (rep i ≃* rep j) → i = j

variable {N k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]

/-- Combining exhaustiveness and distinctness: every group of order `N` is isomorphic to a
**unique** representative. -/
theorem IsClassif.existsUnique (h : IsClassif N rep) (G : Type) [Group G] (hG : Nat.card G = N) :
    ∃! i, Nonempty (G ≃* rep i) := by
  obtain ⟨i, hi⟩ := h.complete G hG
  exact ⟨i, hi, fun j hj => h.distinct j i ⟨hj.some.symm.trans hi.some⟩⟩

/-- **The number of isomorphism classes is well defined.** Any two complete lists of pairwise
non-isomorphic representatives of the groups of order `N` have the same length. -/
theorem IsClassif.card_unique {k' : ℕ} {rep' : Fin k' → Type} [∀ i, Group (rep' i)]
    (h : IsClassif N rep) (h' : IsClassif N rep') : k = k' := by
  -- Map each representative of one list to the (unique) isomorphic representative of the other.
  let f : Fin k → Fin k' := fun i => (h'.complete (rep i) (h.card i)).choose
  let g : Fin k' → Fin k := fun j => (h.complete (rep' j) (h'.card j)).choose
  have hf : ∀ i, Nonempty (rep i ≃* rep' (f i)) := fun i => (h'.complete (rep i) (h.card i)).choose_spec
  have hg : ∀ j, Nonempty (rep' j ≃* rep (g j)) := fun j => (h.complete (rep' j) (h'.card j)).choose_spec
  have left : Function.LeftInverse g f := fun i =>
    (h.distinct i (g (f i)) ⟨(hf i).some.trans (hg (f i)).some⟩).symm
  have right : Function.RightInverse g f := fun j =>
    (h'.distinct j (f (g j)) ⟨(hg j).some.trans (hf (g j)).some⟩).symm
  have e : Fin k ≃ Fin k' := ⟨f, g, left, right⟩
  simpa using Fintype.card_congr e

/-! ### Constructors for the one- and two-class cases -/

/-- The one-element representative family. -/
def rep1 (A : Type) : Fin 1 → Type := fun _ => A

instance instGroupRep1 (A : Type) [Group A] : ∀ i, Group (rep1 A i) := fun _ => ‹Group A›

/-- A single representative `A` of order `N` that exhausts the groups of order `N` gives a
one-class classification. -/
theorem isClassif_one {N : ℕ} (A : Type) [Group A] (hA : Nat.card A = N)
    (hcomplete : ∀ (G : Type) [Group G], Nat.card G = N → Nonempty (G ≃* A)) :
    IsClassif N (rep1 A) where
  card _ := hA
  complete G _ hG := ⟨0, hcomplete G hG⟩
  distinct i j _ := Subsingleton.elim i j

/-- The two-element representative family. -/
def rep2 (A B : Type) : Fin 2 → Type
  | 0 => A
  | 1 => B

instance instGroupRep2 (A B : Type) [Group A] [Group B] : ∀ i, Group (rep2 A B i)
  | 0 => ‹Group A›
  | 1 => ‹Group B›

/-- Two representatives `A`, `B` of order `N` that together exhaust the groups of order `N` and are
not isomorphic give a two-class classification. -/
theorem isClassif_two {N : ℕ} (A B : Type) [Group A] [Group B]
    (hA : Nat.card A = N) (hB : Nat.card B = N)
    (hcomplete : ∀ (G : Type) [Group G], Nat.card G = N → Nonempty (G ≃* A) ∨ Nonempty (G ≃* B))
    (hdistinct : ¬ Nonempty (A ≃* B)) :
    IsClassif N (rep2 A B) where
  card i := by fin_cases i <;> assumption
  complete G _ hG := by
    rcases hcomplete G hG with hh | hh
    · exact ⟨0, hh⟩
    · exact ⟨1, hh⟩
  distinct i j hiso := by
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hiso hdistinct
    · exact absurd ⟨hiso.some.symm⟩ hdistinct
    · rfl

end Smallgroups.UsefulTheorems
