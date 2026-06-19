/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PrimeSqClassification
import Smallgroups.UsefulTheorems.Counting
import Mathlib.Tactic.NormNum.Prime

/-!
# Classification of groups of order 25

`25 = 5²`, so there are exactly **two** groups of order `25` up to isomorphism: the
cyclic group `ℤ/25` and the elementary abelian group `ℤ/5 × ℤ/5`. Both are abelian.

* `classification` — (1) exhaustiveness: every group of order `25` is `ℤ/25` or `ℤ/5 × ℤ/5`.
* `distinct` — (2) distinctness: the two are not isomorphic.
* `isClassif` / `numIsoClasses_eq` — (3) counting: there are exactly two isomorphism classes,
  proved from exhaustiveness and distinctness.
-/

namespace Smallgroups.Classifications.Order25

open Smallgroups.UsefulTheorems

variable {G : Type*} [Group G]

/-- `5` is prime. -/
theorem prime_p : Nat.Prime 5 := by norm_num

/-- A group of order `25` is abelian. -/
theorem mul_comm_of_card (h : Nat.card G = 25) (a b : G) : a * b = b * a := by
  haveI : Fact (Nat.Prime 5) := ⟨prime_p⟩
  exact prime_sq_mul_comm (p := 5) (by norm_num [h]) a b

/-- **(1) Exhaustiveness.** Every group of order `25` is isomorphic to the cyclic group
`ℤ/25` (`CyclicRep 25`) or to the elementary abelian group `ℤ/5 × ℤ/5` (`ElemAbelianRep 5`). -/
theorem classification (h : Nat.card G = 25) :
    Nonempty (G ≃* CyclicRep 25) ∨ Nonempty (G ≃* ElemAbelianRep 5) := by
  haveI : Fact (Nat.Prime 5) := ⟨prime_p⟩
  exact prime_sq_classification (p := 5) (by norm_num [h])

/-- **(2) Distinctness.** `ℤ/25` and `ℤ/5 × ℤ/5` are not isomorphic. -/
theorem distinct : ¬ Nonempty (CyclicRep 25 ≃* ElemAbelianRep 5) := by
  haveI : Fact (Nat.Prime 5) := ⟨prime_p⟩
  exact prime_sq_distinct (p := 5)

/-- **(3) Counting.** The list `[ℤ/25, ℤ/5 × ℤ/5]` is a complete, non-redundant list of
representatives of the groups of order `25` — assembled from exhaustiveness (`classification`)
and distinctness (`distinct`). -/
theorem isClassif : IsClassif 25 (rep2 (CyclicRep 25) (ElemAbelianRep 5)) :=
  isClassif_two _ _ (card_cyclicRep (by norm_num)) (card_elemAbelianRep (by norm_num))
    (fun _ _ hG => classification hG) distinct

/-- **The number of isomorphism classes of groups of order `25` is exactly `2`:** any complete
list of pairwise non-isomorphic representatives has length `2`. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 25 rep) : k = 2 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order25
