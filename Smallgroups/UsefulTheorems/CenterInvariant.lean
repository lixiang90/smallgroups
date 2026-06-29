/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Center cardinality as a group invariant

The cardinality of the center `Z(G)` is preserved by group isomorphisms. Groups with different
center cardinalities are non-isomorphic. This gives a simple and widely applicable distinctness
tool for classification.

## Main results

* `card_center_eq_of_mulEquiv` — center cardinality is an isomorphism invariant
* `not_nonempty_mulEquiv_of_card_center_ne` — different center sizes ⇒ non-isomorphic
* `card_center_eq_card_of_comm` — center of a commutative group equals the whole group
* `card_center_prod` — `|Z(G × H)| = |Z(G)| · |Z(H)|`
* `card_center_bot` — `|Z(G)| = 1` when the center is trivial
-/

namespace Smallgroups.UsefulTheorems

open Subgroup

/-- The center cardinality is preserved by group isomorphisms. -/
theorem card_center_eq_of_mulEquiv {H K : Type*} [Group H] [Group K] (e : H ≃* K) :
    Nat.card (center H) = Nat.card (center K) :=
  Nat.card_congr (centerCongr e).toEquiv

/-- Groups with different center cardinalities are non-isomorphic. -/
theorem not_nonempty_mulEquiv_of_card_center_ne {H K : Type*} [Group H] [Group K]
    (h : Nat.card (center H) ≠ Nat.card (center K)) :
    ¬ Nonempty (H ≃* K) := by
  rintro ⟨e⟩
  exact h (card_center_eq_of_mulEquiv e)

/-- The center of a commutative group is the whole group. -/
theorem card_center_eq_card_of_comm (H : Type*) [Group H] (hcomm : ∀ a b : H, a * b = b * a) :
    Nat.card (center H) = Nat.card H := by
  have : center H = ⊤ := by
    rw [eq_top_iff']; intro x; rw [mem_center_iff]; intro g; exact hcomm g x
  rw [this, Subgroup.card_top]

/-- The center of a product is the product of the centers. -/
theorem card_center_prod (H K : Type*) [Group H] [Group K] :
    Nat.card (center (H × K)) =
      Nat.card (center H) * Nat.card (center K) := by
  rw [Subgroup.center_prod,
    Nat.card_congr (Subgroup.prodEquiv (center H) (center K)).toEquiv,
    Nat.card_prod]

/-- When the center is trivial, its cardinality is `1`. -/
theorem card_center_of_eq_bot {G : Type*} [Group G] (h : center G = ⊥) :
    Nat.card (center G) = 1 := by
  rw [h, Subgroup.card_bot]

/-- Groups with different center cardinalities are in disjoint invariant classes.
    Supplies the `hdisj` hypothesis of `PairwiseNonMulEquiv.sigma` or
    the `hinv` hypothesis of `PairwiseNonMulEquiv.of_invariant`. -/
theorem pairwise_disjoint_of_card_center_ne {ι κ : Type*} {A : ι → Type}
    {B : κ → Type} [∀ i, Group (A i)] [∀ j, Group (B j)]
    (cA : ι → ℕ) (cB : κ → ℕ)
    (hA : ∀ i, Nat.card (Subgroup.center (A i)) = cA i)
    (hB : ∀ j, Nat.card (Subgroup.center (B j)) = cB j)
    (hne : ∀ i j, cA i ≠ cB j) :
    ∀ i j, ¬ Nonempty (A i ≃* B j) :=
  fun i j => not_nonempty_mulEquiv_of_card_center_ne (by rw [hA, hB]; exact hne i j)

end Smallgroups.UsefulTheorems
