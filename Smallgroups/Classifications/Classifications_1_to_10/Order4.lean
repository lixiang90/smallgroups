/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PrimeSqClassification
import Smallgroups.UsefulTheorems.Counting
import Mathlib.Tactic.NormNum.Prime

/-!
# Classification of groups of order 4

`4 = 2²`, so there are exactly **two** groups of order `4` up to isomorphism: the
cyclic group `ℤ/4` and the Klein four-group `ℤ/2 × ℤ/2`. Both are abelian.

* `classification` — (1) exhaustiveness: every group of order `4` is `ℤ/4` or `ℤ/2 × ℤ/2`.
* `distinct` — (2) distinctness: the two are not isomorphic.
* `isClassif` / `numIsoClasses_eq` — (3) counting: there are exactly two isomorphism classes,
  proved from exhaustiveness and distinctness.
-/

namespace Smallgroups.Classifications.Order4

open Smallgroups.UsefulTheorems

variable {G : Type*} [Group G]

/-- `2` is prime. -/
theorem prime_p : Nat.Prime 2 := by norm_num

/-- A group of order `4` is abelian. -/
theorem mul_comm_of_card (h : Nat.card G = 4) (a b : G) : a * b = b * a := by
  haveI : Fact (Nat.Prime 2) := ⟨prime_p⟩
  exact prime_sq_mul_comm (p := 2) (by norm_num [h]) a b

/-- **(1) Exhaustiveness.** Every group of order `4` is isomorphic to the cyclic group
`ℤ/4` (`CyclicRep 4`) or to the Klein four-group `ℤ/2 × ℤ/2` (`ElemAbelianRep 2`). -/
theorem classification (h : Nat.card G = 4) :
    Nonempty (G ≃* CyclicRep 4) ∨ Nonempty (G ≃* ElemAbelianRep 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨prime_p⟩
  exact prime_sq_classification (p := 2) (by norm_num [h])

/-- **(2) Distinctness.** `ℤ/4` and `ℤ/2 × ℤ/2` are not isomorphic. -/
theorem distinct : ¬ Nonempty (CyclicRep 4 ≃* ElemAbelianRep 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨prime_p⟩
  exact prime_sq_distinct (p := 2)

/-- **(3) Counting.** The list `[ℤ/4, ℤ/2 × ℤ/2]` is a complete, non-redundant list of
representatives of the groups of order `4` — assembled from exhaustiveness (`classification`)
and distinctness (`distinct`). -/
theorem isClassif : IsClassif 4 (rep2 (CyclicRep 4) (ElemAbelianRep 2)) :=
  isClassif_two _ _ (card_cyclicRep (by norm_num)) (card_elemAbelianRep (by norm_num))
    (fun _ _ hG => classification hG) distinct

/-- **The number of isomorphism classes of groups of order `4` is exactly `2`:** any complete
list of pairwise non-isomorphic representatives has length `2`. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 4 rep) : k = 2 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order4
