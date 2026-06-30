/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order56

/-!
# Classification of groups of order 56

`56 = 8 * 7`.  The Sylow `7`-subgroup may be normal or not.  The thirteen
representatives in `Smallgroups.UsefulTheorems.order56_reps` cover both cases:
the twelve semidirect products with a normal `C₇`-subgroup and the extra
nontrivial `(C₂)^3 ⋊ C₇` case when the normal subgroup has order `8`.

* `classification` — (1) exhaustiveness: every group of order `56` is one of the thirteen.
* `distinct` — (2) distinctness: the thirteen representatives are pairwise non-isomorphic.
* `isClassif` / `numIsoClasses_eq` — (3) counting: there are exactly thirteen isomorphism
  classes.
-/

namespace Smallgroups.Classifications.Order56

open Smallgroups.UsefulTheorems

variable {G : Type} [Group G]

/-- The thirteen displayed representatives for groups of order `56`. -/
noncomputable abbrev Rep : Fin 13 → Type :=
  order56_reps

/-- **(1) Exhaustiveness.** Every group of order `56` is isomorphic to one of the thirteen
displayed representatives. -/
theorem classification (h : Nat.card G = 56) :
    ∃ i, Nonempty (G ≃* Rep i) := by
  simpa [Rep] using order56_complete (G := G) h

/-- **(2) Distinctness.** The thirteen displayed representatives are pairwise non-isomorphic. -/
theorem distinct : PairwiseNonMulEquiv Rep := by
  simpa [Rep] using order56_reps_pairwise

/-- **(3) Counting.** The thirteen displayed representatives form a complete, non-redundant list
of the groups of order `56`. -/
theorem isClassif : IsClassif 56 Rep := by
  simpa [Rep] using order56_isClassif

/-- **The number of isomorphism classes of groups of order `56` is exactly `13`:** any complete
list of pairwise non-isomorphic representatives has length `13`. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 56 rep) : k = 13 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order56
