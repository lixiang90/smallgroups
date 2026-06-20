/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PrimePairDihedral
import Smallgroups.UsefulTheorems.Counting
import Mathlib.Tactic.NormNum.Prime

/-!
# Classification of groups of order 38

`38 = 2 * 19` with `19` an odd prime, so there are exactly **two** groups of order `38`
up to isomorphism: the cyclic group `ℤ/38` and the dihedral group `DihedralGroup 19`.

* `classification` — (1) exhaustiveness: every group of order `38` is cyclic or dihedral.
* `distinct` — (2) distinctness: the two are not isomorphic.
* `isClassif` / `numIsoClasses_eq` — (3) counting: there are exactly two isomorphism classes.
-/

namespace Smallgroups.Classifications.Order38

open Smallgroups.UsefulTheorems

variable {G : Type*} [Group G]

/-- `19` is prime. -/
theorem prime_p : Nat.Prime 19 := by norm_num

/-- `19` is odd. -/
theorem odd_p : Odd 19 := by decide

/-- **(1) Exhaustiveness.** Every group of order `38` is isomorphic to the cyclic group
`ℤ/38` (`CyclicRep 38`) or to the dihedral group `DihedralGroup 19`. -/
theorem classification (h : Nat.card G = 38) :
    Nonempty (G ≃* CyclicRep 38) ∨ Nonempty (G ≃* DihedralGroup 19) :=
  classification_card_two_mul_prime prime_p odd_p (h.trans (by norm_num))

/-- **(2) Distinctness.** `ℤ/38` and `DihedralGroup 19` are not isomorphic (the latter is not
cyclic). -/
theorem distinct : ¬ Nonempty (CyclicRep 38 ≃* DihedralGroup 19) :=
  cyclicRep_not_mulEquiv_dihedral (p := 19) (by norm_num)

/-- **(3) Counting.** The list `[ℤ/38, DihedralGroup 19]` is a complete, non-redundant list of
representatives of the groups of order `38` — assembled from exhaustiveness (`classification`)
and distinctness (`distinct`). -/
theorem isClassif : IsClassif 38 (rep2 (CyclicRep 38) (DihedralGroup 19)) :=
  isClassif_two _ _ (card_cyclicRep (by norm_num)) DihedralGroup.nat_card
    (fun _ _ hG => classification hG) distinct

/-- **The number of isomorphism classes of groups of order `38` is exactly `2`:** any complete
list of pairwise non-isomorphic representatives has length `2`. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 38 rep) : k = 2 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order38
