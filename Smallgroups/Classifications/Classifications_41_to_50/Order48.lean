/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.Complete

/-!
# Classification of groups of order 48

`48 = 2⁴ · 3`. There are exactly **52** isomorphism classes, split by the
number of Sylow `3`-subgroups:

1. **`n₃ = 1` (42 classes).** These are the groups with a normal Sylow
   `3`-subgroup.
2. **`n₃ = 16` (2 classes).** These are the two faithful `C₃`-action
   representatives with normal subgroup `(C₂)⁴` or `C₄ × C₄`.
3. **`n₃ = 4` (8 classes).** These are the residual representatives obtained
   from central extensions of the three order-24 quotient types.

The representatives are indexed structurally; alignment with GAP small-group
numbers is intentionally deferred. This file re-exports the unconditional
classification proved in `Smallgroups.UsefulTheorems.Order48.Complete` through
the standard `Smallgroups.Classifications` interface.
-/

namespace Smallgroups.Classifications.Order48

open Smallgroups.UsefulTheorems

variable {G : Type} [Group G]

private theorem indexCard : Fintype.card order48_all_index = 52 := by
  rw [← Nat.card_eq_fintype_card]
  exact order48_all_classCount

/-- Reindex the structural representative family by the conventional
`Fin 52` index type. -/
noncomputable def indexEquiv :
    Fin 52 ≃ Fin (Fintype.card order48_all_index) :=
  Equiv.cast (congrArg Fin indexCard.symm)

/-- The 52 structural representatives for groups of order 48. -/
noncomputable abbrev Rep (i : Fin 52) : Type :=
  order48_all_reps_fin (indexEquiv i)

/-- **(1) Exhaustiveness.** Every group of order 48 is isomorphic to one of
the 52 representatives. -/
theorem classification (h : Nat.card G = 48) :
    ∃ i, Nonempty (G ≃* Rep i) := by
  obtain ⟨j, e⟩ := order48_isClassif.complete G h
  refine ⟨indexEquiv.symm j, ?_⟩
  change Nonempty (G ≃* order48_all_reps_fin
    (indexEquiv (indexEquiv.symm j)))
  rw [indexEquiv.apply_symm_apply]
  exact e

/-- **(2) Distinctness.** The 52 representatives are pairwise
non-isomorphic. -/
theorem distinct : PairwiseNonMulEquiv Rep := by
  intro i j e
  apply indexEquiv.injective
  exact order48_isClassif.distinct (indexEquiv i) (indexEquiv j) (by
    simpa [Rep] using e)

/-- **(3) Counting.** The 52 representatives form a complete,
non-redundant classification of groups of order 48. -/
theorem isClassif : IsClassif 48 Rep where
  card i := by
    simpa [Rep] using order48_isClassif.card (indexEquiv i)
  complete G _ hG := classification hG
  distinct := distinct

/-- **The number of isomorphism classes of groups of order 48 is exactly
`52`.** -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 48 rep) : k = 52 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order48
