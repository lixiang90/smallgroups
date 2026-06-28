/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PrimeSqPrimeAbelian
import Mathlib.Tactic.NormNum.Prime

/-!
# Classification of groups of order 45

`45 = 3² · 5`. Since `3 ∤ 5 − 1` and `5 ∤ 3² − 1`, both Sylow subgroups are normal, so every
group of order 45 is **abelian**, giving exactly **two** isomorphism classes: the cyclic group
`ℤ/45` (ℤ/45) and `ℤ/3 × ℤ/15`. This is the `p = 3, q = 5` instance of
`Smallgroups.UsefulTheorems.PrimeSqPrimeAbelian`.
-/

namespace Smallgroups.Classifications.Order45

open Smallgroups.UsefulTheorems

/-- `ℤ/45` (cyclic). -/
abbrev RA : Type := psqPrimeRep1 3 5
/-- `ℤ/3 × ℤ/15`. -/
abbrev RB : Type := psqPrimeRep2 3 5

variable {G : Type*} [Group G]

/-- **Every group of order 45 is abelian.** -/
theorem abelian (h : Nat.card G = 45) (a b : G) : a * b = b * a := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  exact psq_prime_abelian (p := 3) (q := 5) (by norm_num) (by norm_num) (by norm_num)
    (by decide) (by decide) (h.trans (by norm_num)) a b

/-- **(1) Exhaustiveness.** Every group of order 45 is isomorphic to one of the two groups. -/
theorem classification (h : Nat.card G = 45) : Nonempty (G ≃* RA) ∨ Nonempty (G ≃* RB) := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  exact psq_prime_abelian_classification (p := 3) (q := 5) (by norm_num) (by norm_num)
    (by norm_num) (by decide) (by decide) (h.trans (by norm_num))

/-- **(2) Distinctness.** `ℤ/45` and `ℤ/3 × ℤ/15` are not isomorphic. -/
theorem distinct : ¬ Nonempty (RA ≃* RB) :=
  psq_prime_distinct (by norm_num) (by norm_num)

/-- **(3) Counting.** The two groups are a complete, non-redundant list of
representatives of the groups of order 45. -/
theorem isClassif : IsClassif 45 (rep2 RA RB) :=
  psq_prime_isClassif (p := 3) (q := 5) (by norm_num) (by norm_num) (by norm_num)
    (by decide) (by decide) (by norm_num)

/-- **The number of isomorphism classes of groups of order 45 is exactly `2`.** -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 45 rep) : k = 2 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order45
