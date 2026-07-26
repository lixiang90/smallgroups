/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Prime

/-!
# GAP-numbered classification of groups of order 67

`67` is prime, so there is a unique isomorphism class: `SmallGroup(67, 1) = ℤ/67`.

* `classification` — (1) exhaustiveness: every group of order `67` is isomorphic to
  `SmallGroup(67, 1)`.
* `distinct` — (2) distinctness: vacuous, as there is a single class.
* `isClassif` / `numIsoClasses_eq` — (3) counting: there is exactly one isomorphism
  class, matching the GAP SmallGroups library count.
-/

namespace Smallgroups.GAP_Classifications.Order67

open Smallgroups.GAP Smallgroups.UsefulTheorems

variable {G : Type*} [Group G]

/-- `67` is prime. -/
theorem prime_p : Nat.Prime 67 := by norm_num

/-- The GAP-numbered representatives of order `67`: the single class
`SmallGroup(67, 1)`. -/
abbrev gapRep : Fin 1 → Type := primeGapRep 67

/-- **(1) Exhaustiveness.** Every group of order `67` is isomorphic to
`SmallGroup(67, 1) = ℤ/67`. -/
theorem classification (h : Nat.card G = 67) : Nonempty (G ≃* gapRep 0) :=
  prime_classification prime_p h

/-- **(2) Distinctness.** With a single class the distinctness statement holds
vacuously. -/
theorem distinct {i j : Fin 1} (hij : i ≠ j) :
    ¬ Nonempty (gapRep i ≃* gapRep j) :=
  singleReps_distinct _ hij

/-- **(3) Counting.** The GAP list `[SmallGroup(67, 1)]` is a complete, non-redundant
list of representatives of the groups of order `67`. -/
theorem isClassif : IsClassif 67 gapRep := prime_gap_isClassif prime_p

/-- **The number of isomorphism classes of groups of order `67` is exactly `1`,** the
GAP SmallGroups library count. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 67 rep) : k = 1 :=
  (isClassif.card_unique h).symm

end Smallgroups.GAP_Classifications.Order67
