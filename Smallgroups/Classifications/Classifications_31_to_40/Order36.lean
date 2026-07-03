/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order36

/-!
# Classification of groups of order 36

`36 = 4 * 3^2`. Reindexing the normal and non-normal representatives from
`Smallgroups.UsefulTheorems.Order36` gives a complete, non-redundant list of the groups of
order `36`.

* `classification` — (1) exhaustiveness: every group of order `36` is one of the fourteen.
* `distinct` — (2) distinctness: the fourteen representatives are pairwise non-isomorphic.
* `isClassif` / `numIsoClasses_eq` — (3) counting: there are exactly fourteen isomorphism
  classes.
-/

namespace Smallgroups.Classifications.Order36

open Smallgroups.UsefulTheorems

variable {G : Type} [Group G]

/-- The fourteen displayed representatives for groups of order `36`. -/
noncomputable abbrev Rep : Fin 14 → Type :=
  fun i => Sum.elim order36_normal_reps order36_nonnormal_reps (finSumFinEquiv.symm i)

/-- **(1) Exhaustiveness.** Every group of order `36` is isomorphic to one of the fourteen
displayed representatives. -/
theorem classification (h : Nat.card G = 36) :
    ∃ i, Nonempty (G ≃* Rep i) := by
  obtain ⟨i, hi⟩ := order36_complete G h
  exact ⟨finSumFinEquiv i, by
    change Nonempty (G ≃*
      Sum.elim order36_normal_reps order36_nonnormal_reps
        (finSumFinEquiv.symm (finSumFinEquiv i)))
    rw [finSumFinEquiv.symm_apply_apply]
    exact hi⟩

/-- **(2) Distinctness.** The fourteen displayed representatives are pairwise non-isomorphic. -/
theorem distinct : PairwiseNonMulEquiv Rep := by
  simpa [Rep] using
    (PairwiseNonMulEquiv.reindex finSumFinEquiv.symm order36_sum_reps_pairwise)

/-- **(3) Counting.** The fourteen displayed representatives form a complete, non-redundant list
of the groups of order `36`. -/
theorem isClassif : IsClassif 36 Rep := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simpa [Rep] using card_order36_sum_reps (finSumFinEquiv.symm i)
  · intro G _ hG
    exact classification (G := G) hG
  · exact distinct

/-- **The number of isomorphism classes of groups of order `36` is exactly `14`:** any complete
list of pairwise non-isomorphic representatives has length `14`. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 36 rep) : k = 14 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order36
