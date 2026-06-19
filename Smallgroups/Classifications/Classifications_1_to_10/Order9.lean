/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PrimeSqClassification
import Smallgroups.UsefulTheorems.Counting
import Mathlib.Tactic.NormNum.Prime

/-!
# Classification of groups of order 9

`9 = 3²`, so there are exactly **two** groups of order `9` up to isomorphism: the
cyclic group `ℤ/9` and the elementary abelian group `ℤ/3 × ℤ/3`. Both are abelian.

* `classification` — (1) exhaustiveness: every group of order `9` is `ℤ/9` or `ℤ/3 × ℤ/3`.
* `distinct` — (2) distinctness: the two are not isomorphic.
* `isClassif` / `numIsoClasses_eq` — (3) counting: there are exactly two isomorphism classes,
  proved from exhaustiveness and distinctness.
-/

namespace Smallgroups.Classifications.Order9

open Smallgroups.UsefulTheorems

variable {G : Type*} [Group G]

/-- `3` is prime. -/
theorem prime_p : Nat.Prime 3 := by norm_num

/-- A group of order `9` is abelian. -/
theorem mul_comm_of_card (h : Nat.card G = 9) (a b : G) : a * b = b * a := by
  haveI : Fact (Nat.Prime 3) := ⟨prime_p⟩
  exact prime_sq_mul_comm (p := 3) (by norm_num [h]) a b

/-- **(1) Exhaustiveness.** Every group of order `9` is isomorphic to the cyclic group
`ℤ/9` (`CyclicRep 9`) or to the elementary abelian group `ℤ/3 × ℤ/3` (`ElemAbelianRep 3`). -/
theorem classification (h : Nat.card G = 9) :
    Nonempty (G ≃* CyclicRep 9) ∨ Nonempty (G ≃* ElemAbelianRep 3) := by
  haveI : Fact (Nat.Prime 3) := ⟨prime_p⟩
  exact prime_sq_classification (p := 3) (by norm_num [h])

/-- **(2) Distinctness.** `ℤ/9` and `ℤ/3 × ℤ/3` are not isomorphic. -/
theorem distinct : ¬ Nonempty (CyclicRep 9 ≃* ElemAbelianRep 3) := by
  haveI : Fact (Nat.Prime 3) := ⟨prime_p⟩
  exact prime_sq_distinct (p := 3)

/-- **(3) Counting.** The list `[ℤ/9, ℤ/3 × ℤ/3]` is a complete, non-redundant list of
representatives of the groups of order `9` — assembled from exhaustiveness (`classification`)
and distinctness (`distinct`). -/
theorem isClassif : IsClassif 9 (rep2 (CyclicRep 9) (ElemAbelianRep 3)) :=
  isClassif_two _ _ (card_cyclicRep (by norm_num)) (card_elemAbelianRep (by norm_num))
    (fun _ _ hG => classification hG) distinct

/-- **The number of isomorphism classes of groups of order `9` is exactly `2`:** any complete
list of pairwise non-isomorphic representatives has length `2`. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 9 rep) : k = 2 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order9
