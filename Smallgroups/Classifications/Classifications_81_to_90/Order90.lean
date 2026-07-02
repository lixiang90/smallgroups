/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order90

/-!
# Classification of groups of order 90

The ten representatives in `Smallgroups.UsefulTheorems.order90_reps` give a complete,
non-redundant list of the groups of order `90`.

* `classification` — (1) exhaustiveness: every group of order `90` is one of the ten.
* `distinct` — (2) distinctness: the ten representatives are pairwise non-isomorphic.
* `isClassif` / `numIsoClasses_eq` — (3) counting: there are exactly ten isomorphism classes.
-/

namespace Smallgroups.Classifications.Order90

open Smallgroups.UsefulTheorems

variable {G : Type} [Group G]

/-- The ten displayed representatives for groups of order `90`. -/
noncomputable abbrev Rep : Fin 10 → Type :=
  order90_reps

/-- **(1) Exhaustiveness.** Every group of order `90` is isomorphic to one of the ten displayed
representatives. -/
theorem classification (h : Nat.card G = 90) :
    ∃ i, Nonempty (G ≃* Rep i) := by
  simpa [Rep] using order90_complete (G := G) h

/-- **(2) Distinctness.** The ten displayed representatives are pairwise non-isomorphic. -/
theorem distinct : PairwiseNonMulEquiv Rep := by
  simpa [Rep] using order90_reps_pairwise

/-- **(3) Counting.** The ten displayed representatives form a complete, non-redundant list of
the groups of order `90`. -/
theorem isClassif : IsClassif 90 Rep := by
  simpa [Rep] using order90_isClassif

/-- **The number of isomorphism classes of groups of order `90` is exactly `10`:** any complete
list of pairwise non-isomorphic representatives has length `10`. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 90 rep) : k = 10 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order90
