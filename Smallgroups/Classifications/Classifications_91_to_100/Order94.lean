/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PrimePairDihedral
import Smallgroups.UsefulTheorems.Counting
import Mathlib.Tactic.NormNum.Prime

/-!
# Classification of groups of order 94

`94 = 2 * 47` with `47` an odd prime, so there are exactly **two** groups of order `94`
up to isomorphism: the cyclic group `ℤ/94` and the dihedral group `DihedralGroup 47`.

* `classification` — (1) exhaustiveness: every group of order `94` is cyclic or dihedral.
* `distinct` — (2) distinctness: the two are not isomorphic.
* `isClassif` / `numIsoClasses_eq` — (3) counting: there are exactly two isomorphism classes.
-/

namespace Smallgroups.Classifications.Order94

open Smallgroups.UsefulTheorems

variable {G : Type*} [Group G]

/-- `47` is prime. -/
theorem prime_p : Nat.Prime 47 := by norm_num

/-- `47` is odd. -/
theorem odd_p : Odd 47 := by decide

/-- **(1) Exhaustiveness.** Every group of order `94` is isomorphic to the cyclic group
`ℤ/94` (`CyclicRep 94`) or to the dihedral group `DihedralGroup 47`. -/
theorem classification (h : Nat.card G = 94) :
    Nonempty (G ≃* CyclicRep 94) ∨ Nonempty (G ≃* DihedralGroup 47) :=
  classification_card_two_mul_prime prime_p odd_p (h.trans (by norm_num))

/-- **(2) Distinctness.** `ℤ/94` and `DihedralGroup 47` are not isomorphic (the latter is not
cyclic). -/
theorem distinct : ¬ Nonempty (CyclicRep 94 ≃* DihedralGroup 47) :=
  cyclicRep_not_mulEquiv_dihedral (p := 47) (by norm_num)

/-- **(3) Counting.** The list `[ℤ/94, DihedralGroup 47]` is a complete, non-redundant list of
representatives of the groups of order `94` — assembled from exhaustiveness (`classification`)
and distinctness (`distinct`). -/
theorem isClassif : IsClassif 94 (rep2 (CyclicRep 94) (DihedralGroup 47)) :=
  isClassif_two _ _ (card_cyclicRep (by norm_num)) DihedralGroup.nat_card
    (fun _ _ hG => classification hG) distinct

/-- **The number of isomorphism classes of groups of order `94` is exactly `2`:** any complete
list of pairwise non-isomorphic representatives has length `2`. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 94 rep) : k = 2 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order94
