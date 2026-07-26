/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Prime

/-!
# GAP-numbered classification of groups of order 1

There is exactly one group of order `1` up to isomorphism: `SmallGroup(1, 1)`, the
trivial group `ℤ/1`.

* `classification` — (1) exhaustiveness: every group of order `1` is isomorphic to
  `SmallGroup(1, 1)`.
* `distinct` — (2) distinctness: vacuous, as there is a single class.
* `isClassif` / `numIsoClasses_eq` — (3) counting: there is exactly one isomorphism
  class, matching the GAP SmallGroups library count.
-/

namespace Smallgroups.GAP_Classifications.Order1

open Smallgroups.GAP Smallgroups.UsefulTheorems

variable {G : Type*} [Group G]

/-- The GAP-numbered representatives of order `1`: the single class `SmallGroup(1, 1)`. -/
abbrev gapRep : Fin 1 → Type := order1GapRep

/-- **(1) Exhaustiveness.** Every group of order `1` is isomorphic to
`SmallGroup(1, 1) = ℤ/1`. -/
theorem classification (h : Nat.card G = 1) : Nonempty (G ≃* gapRep 0) :=
  haveI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp h).1
  cyclicRep_classification one_ne_zero h

/-- **(2) Distinctness.** With a single class the distinctness statement holds
vacuously. -/
theorem distinct {i j : Fin 1} (hij : i ≠ j) :
    ¬ Nonempty (gapRep i ≃* gapRep j) :=
  singleReps_distinct _ hij

/-- **(3) Counting.** The GAP list `[SmallGroup(1, 1)]` is a complete, non-redundant
list of representatives of the groups of order `1`. -/
theorem isClassif : IsClassif 1 gapRep := order1_gap_isClassif

/-- **The number of isomorphism classes of groups of order `1` is exactly `1`,** the GAP
SmallGroups library count. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 1 rep) : k = 1 :=
  (isClassif.card_unique h).symm

end Smallgroups.GAP_Classifications.Order1
