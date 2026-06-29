/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order88

/-!
# Classification of groups of order 88

`88 = 8 * 11`.  The Sylow `11`-subgroup is normal, so every group of order `88`
splits as a semidirect product `C₁₁ ⋊ H`, where `H` has order `8`.

The twelve representatives in `Smallgroups.UsefulTheorems.order88_reps` give a
complete, non-redundant list of the groups of order `88`.

* `classification` — (1) exhaustiveness: every group of order `88` is one of the twelve.
* `distinct` — (2) distinctness: the twelve representatives are pairwise non-isomorphic.
* `isClassif` / `numIsoClasses_eq` — (3) counting: there are exactly twelve isomorphism
  classes.
-/

namespace Smallgroups.Classifications.Order88

open Smallgroups.UsefulTheorems

variable {G : Type} [Group G]

/-- The twelve displayed representatives for groups of order `88`. -/
noncomputable abbrev Rep : Fin 12 → Type :=
  order88_reps

/-- **(1) Exhaustiveness.** Every group of order `88` is isomorphic to one of the twelve
displayed representatives. -/
theorem classification (h : Nat.card G = 88) :
    ∃ i, Nonempty (G ≃* Rep i) := by
  simpa [Rep] using order88_complete (G := G) h

/-- **(2) Distinctness.** The twelve displayed representatives are pairwise non-isomorphic. -/
theorem distinct : PairwiseNonMulEquiv Rep := by
  simpa [Rep] using order88_reps_pairwise

/-- **(3) Counting.** The twelve displayed representatives form a complete, non-redundant list
of the groups of order `88`. -/
theorem isClassif : IsClassif 88 Rep := by
  simpa [Rep] using order88_isClassif

/-- **The number of isomorphism classes of groups of order `88` is exactly `12`:** any complete
list of pairwise non-isomorphic representatives has length `12`. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 88 rep) : k = 12 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order88
