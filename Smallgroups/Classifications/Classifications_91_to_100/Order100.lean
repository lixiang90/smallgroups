/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order100

/-!
# Classification of groups of order 100

There are exactly **sixteen** groups of order `100` up to isomorphism.  This is the concrete
`4 · 5²` classification from `Smallgroups.UsefulTheorems.Order100`.
-/

namespace Smallgroups.Classifications.Order100

open Smallgroups.UsefulTheorems

/-- The sixteen representatives of groups of order `100`. -/
noncomputable abbrev Rep : Fin 16 → Type := order100_reps

variable {G : Type} [Group G]

/-- **(1) Exhaustiveness.** Every group of order `100` is isomorphic to one of the sixteen
groups. -/
theorem classification (h : Nat.card G = 100) : ∃ i, Nonempty (G ≃* Rep i) := by
  simpa [Rep] using order100_complete G h

/-- **(2) Distinctness.** The sixteen representatives are pairwise non-isomorphic. -/
theorem distinct : ∀ i j, Nonempty (Rep i ≃* Rep j) → i = j := by
  intro i j h
  exact order100_reps_pairwise i j h

/-- **(3) Counting.** The sixteen groups are a complete, non-redundant list of
representatives of the groups of order `100`. -/
theorem isClassif : IsClassif 100 Rep := by
  simpa [Rep] using order100_isClassif

/-- **The number of isomorphism classes of groups of order `100` is exactly `16`.** -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 100 rep) : k = 16 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order100
