/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PrimeSqPrimeNonabelian
import Mathlib.Tactic.NormNum.Prime

/-!
# Classification of groups of order 75

`75 = 5² · 3`. Since `3 ∤ 5 − 1` and `5 ∤ 2`, every group of order 75 is either:
1. the cyclic group `ℤ/75`,
2. the abelian but non-cyclic group `ℤ/5 × ℤ/15`, or
3. the unique nonabelian group `(ℤ/5)² ⋊ ℤ/3`.

This is the `p = 5, q = 3` instance of
`Smallgroups.UsefulTheorems.PrimeSqPrimeNonabelian`.
-/

namespace Smallgroups.Classifications.Order75

open Smallgroups.UsefulTheorems

/-- `ℤ/75` (cyclic). -/
abbrev RA : Type := psqPrimeRep1 5 3
/-- `ℤ/5 × ℤ/15`. -/
abbrev RB : Type := psqPrimeRep2 5 3
/-- `(ℤ/5)² ⋊ ℤ/3` (nonabelian). -/
abbrev RC : Type := psqPrimeNonabRep 5

variable {G : Type*} [Group G]

/-- **(1) Exhaustiveness.** Every group of order 75 is isomorphic to one of the three groups. -/
theorem classification (h : Nat.card G = 75) :
    Nonempty (G ≃* RA) ∨ Nonempty (G ≃* RB) ∨ Nonempty (G ≃* RC) := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  exact psq_prime_nonab_classification (p := 5) (by norm_num) (by decide) (by decide)
    (by norm_num) (hN := by norm_num) h

/-- **(2) Distinctness & (3) Counting.** The three groups are a complete, non-redundant list of
representatives of the groups of order 75. -/
theorem isClassif : IsClassif 75 (rep3 RA RB RC) :=
  psq_prime_nonab_isClassif (p := 5) (by norm_num) (by decide) (by decide)
    (by norm_num) (by norm_num)

/-- **The number of isomorphism classes of groups of order 75 is exactly `3`.** -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 75 rep) : k = 3 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order75
