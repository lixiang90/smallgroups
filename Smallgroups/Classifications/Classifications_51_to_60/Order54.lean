/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order54

/-!
# Classification of groups of order 54

`54 = 2 · 3³`.  The fifteen representatives in
`Smallgroups.UsefulTheorems.order54_reps` cover the abelian order-`27` kernels
and the two non-abelian order-`27` kernels in the Schur--Zassenhaus reduction.
-/

namespace Smallgroups.Classifications.Order54

open Smallgroups.UsefulTheorems

variable {G : Type} [Group G]

/-- The fifteen displayed representatives for groups of order `54`. -/
noncomputable abbrev Rep : Fin 15 → Type :=
  order54_reps

/-- **(1) Exhaustiveness.** Every group of order `54` is isomorphic to one of the fifteen
displayed representatives. -/
theorem classification (h : Nat.card G = 54) :
    ∃ i, Nonempty (G ≃* Rep i) := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  simpa [Rep] using order54_complete (G := G) h

/-- **(2) Distinctness.** The fifteen displayed representatives are pairwise non-isomorphic. -/
theorem distinct : PairwiseNonMulEquiv Rep := by
  simpa [Rep] using order54_reps_pairwise

/-- **(3) Counting.** The fifteen displayed representatives form a complete, non-redundant list
of the groups of order `54`. -/
theorem isClassif : IsClassif 54 Rep := by
  simpa [Rep] using order54_isClassif

/-- **The number of isomorphism classes of groups of order `54` is exactly `15`:** any complete
list of pairwise non-isomorphic representatives has length `15`. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 54 rep) : k = 15 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order54
