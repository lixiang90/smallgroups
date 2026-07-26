/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Prime

/-!
# GAP-numbered classification of groups of order 31

`31` is prime, so there is a unique isomorphism class: `SmallGroup(31, 1) = ℤ/31`.

* `classification` — (1) exhaustiveness: every group of order `31` is isomorphic to
  `SmallGroup(31, 1)`.
* `distinct` — (2) distinctness: vacuous, as there is a single class.
* `isClassif` / `numIsoClasses_eq` — (3) counting: there is exactly one isomorphism
  class, matching the GAP SmallGroups library count.
-/

namespace Smallgroups.GAP_Classifications.Order31

open Smallgroups.GAP Smallgroups.UsefulTheorems

variable {G : Type*} [Group G]

/-- `31` is prime. -/
theorem prime_p : Nat.Prime 31 := by norm_num

/-- The GAP-numbered representatives of order `31`: the single class
`SmallGroup(31, 1)`. -/
abbrev gapRep : Fin 1 → Type := primeGapRep 31

/-- **(1) Exhaustiveness.** Every group of order `31` is isomorphic to
`SmallGroup(31, 1) = ℤ/31`. -/
theorem classification (h : Nat.card G = 31) : Nonempty (G ≃* gapRep 0) :=
  prime_classification prime_p h

/-- **(2) Distinctness.** With a single class the distinctness statement holds
vacuously. -/
theorem distinct {i j : Fin 1} (hij : i ≠ j) :
    ¬ Nonempty (gapRep i ≃* gapRep j) :=
  singleReps_distinct _ hij

/-- **(3) Counting.** The GAP list `[SmallGroup(31, 1)]` is a complete, non-redundant
list of representatives of the groups of order `31`. -/
theorem isClassif : IsClassif 31 gapRep := prime_gap_isClassif prime_p

/-- **The number of isomorphism classes of groups of order `31` is exactly `1`,** the
GAP SmallGroups library count. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 31 rep) : k = 1 :=
  (isClassif.card_unique h).symm

end Smallgroups.GAP_Classifications.Order31
