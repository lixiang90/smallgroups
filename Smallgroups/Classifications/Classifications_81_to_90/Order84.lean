/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order84

/-!
# Classification of groups of order 84

`84 = 12 * 7`. The Sylow `7`-subgroup is normal, so every group of order `84`
splits as a semidirect product `C₇ ⋊ H`, where `H` has order `12`.

The fifteen representatives in `Smallgroups.UsefulTheorems.order84_reps` give a
complete, non-redundant list of the groups of order `84`.

* `classification` — (1) exhaustiveness: every group of order `84` is one of the fifteen.
* `distinct` — (2) distinctness: the fifteen representatives are pairwise non-isomorphic.
* `isClassif` / `numIsoClasses_eq` — (3) counting: there are exactly fifteen isomorphism
  classes.
-/

namespace Smallgroups.Classifications.Order84

open Smallgroups.UsefulTheorems

variable {G : Type} [Group G]

/-- The fifteen displayed representatives for groups of order `84`. -/
noncomputable abbrev Rep : Fin 15 → Type :=
  order84_reps

/-- **(1) Exhaustiveness.** Every group of order `84` is isomorphic to one of the fifteen
displayed representatives. -/
theorem classification (h : Nat.card G = 84) :
    ∃ i, Nonempty (G ≃* Rep i) := by
  simpa [Rep] using order84_complete (G := G) h

/-- **(2) Distinctness.** The fifteen displayed representatives are pairwise non-isomorphic. -/
theorem distinct : PairwiseNonMulEquiv Rep := by
  simpa [Rep] using order84_reps_pairwise

/-- **(3) Counting.** The fifteen displayed representatives form a complete, non-redundant list
of the groups of order `84`. -/
theorem isClassif : IsClassif 84 Rep := by
  simpa [Rep] using order84_isClassif

/-- **The number of isomorphism classes of groups of order `84` is exactly `15`:** any complete
list of pairwise non-isomorphic representatives has length `15`. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 84 rep) : k = 15 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order84
