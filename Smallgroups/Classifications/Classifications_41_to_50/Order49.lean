/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PrimeSqClassification
import Smallgroups.UsefulTheorems.Counting
import Mathlib.Tactic.NormNum.Prime

/-!
# Classification of groups of order 49

`49 = 7²`, so there are exactly **two** groups of order `49` up to isomorphism: the
cyclic group `ℤ/49` and the elementary abelian group `ℤ/7 × ℤ/7`. Both are abelian.

* `classification` — (1) exhaustiveness: every group of order `49` is `ℤ/49` or `ℤ/7 × ℤ/7`.
* `distinct` — (2) distinctness: the two are not isomorphic.
* `isClassif` / `numIsoClasses_eq` — (3) counting: there are exactly two isomorphism classes,
  proved from exhaustiveness and distinctness.
-/

namespace Smallgroups.Classifications.Order49

open Smallgroups.UsefulTheorems

variable {G : Type*} [Group G]

/-- `7` is prime. -/
theorem prime_p : Nat.Prime 7 := by norm_num

/-- A group of order `49` is abelian. -/
theorem mul_comm_of_card (h : Nat.card G = 49) (a b : G) : a * b = b * a := by
  haveI : Fact (Nat.Prime 7) := ⟨prime_p⟩
  exact prime_sq_mul_comm (p := 7) (by norm_num [h]) a b

/-- **(1) Exhaustiveness.** Every group of order `49` is isomorphic to the cyclic group
`ℤ/49` (`CyclicRep 49`) or to the elementary abelian group `ℤ/7 × ℤ/7` (`ElemAbelianRep 7`). -/
theorem classification (h : Nat.card G = 49) :
    Nonempty (G ≃* CyclicRep 49) ∨ Nonempty (G ≃* ElemAbelianRep 7) := by
  haveI : Fact (Nat.Prime 7) := ⟨prime_p⟩
  exact prime_sq_classification (p := 7) (by norm_num [h])

/-- **(2) Distinctness.** `ℤ/49` and `ℤ/7 × ℤ/7` are not isomorphic. -/
theorem distinct : ¬ Nonempty (CyclicRep 49 ≃* ElemAbelianRep 7) := by
  haveI : Fact (Nat.Prime 7) := ⟨prime_p⟩
  exact prime_sq_distinct (p := 7)

/-- **(3) Counting.** The list `[ℤ/49, ℤ/7 × ℤ/7]` is a complete, non-redundant list of
representatives of the groups of order `49` — assembled from exhaustiveness (`classification`)
and distinctness (`distinct`). -/
theorem isClassif : IsClassif 49 (rep2 (CyclicRep 49) (ElemAbelianRep 7)) :=
  isClassif_two _ _ (card_cyclicRep (by norm_num)) (card_elemAbelianRep (by norm_num))
    (fun _ _ hG => classification hG) distinct

/-- **The number of isomorphism classes of groups of order `49` is exactly `2`:** any complete
list of pairwise non-isomorphic representatives has length `2`. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 49 rep) : k = 2 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order49
