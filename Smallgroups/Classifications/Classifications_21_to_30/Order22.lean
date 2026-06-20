/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PrimePairDihedral
import Smallgroups.UsefulTheorems.Counting
import Mathlib.Tactic.NormNum.Prime

/-!
# Classification of groups of order 22

`22 = 2 * 11` with `11` an odd prime, so there are exactly **two** groups of order `22`
up to isomorphism: the cyclic group `ℤ/22` and the dihedral group `DihedralGroup 11`.

* `classification` — (1) exhaustiveness: every group of order `22` is cyclic or dihedral.
* `distinct` — (2) distinctness: the two are not isomorphic.
* `isClassif` / `numIsoClasses_eq` — (3) counting: there are exactly two isomorphism classes.
-/

namespace Smallgroups.Classifications.Order22

open Smallgroups.UsefulTheorems

variable {G : Type*} [Group G]

/-- `11` is prime. -/
theorem prime_p : Nat.Prime 11 := by norm_num

/-- `11` is odd. -/
theorem odd_p : Odd 11 := by decide

/-- **(1) Exhaustiveness.** Every group of order `22` is isomorphic to the cyclic group
`ℤ/22` (`CyclicRep 22`) or to the dihedral group `DihedralGroup 11`. -/
theorem classification (h : Nat.card G = 22) :
    Nonempty (G ≃* CyclicRep 22) ∨ Nonempty (G ≃* DihedralGroup 11) :=
  classification_card_two_mul_prime prime_p odd_p (h.trans (by norm_num))

/-- **(2) Distinctness.** `ℤ/22` and `DihedralGroup 11` are not isomorphic (the latter is not
cyclic). -/
theorem distinct : ¬ Nonempty (CyclicRep 22 ≃* DihedralGroup 11) :=
  cyclicRep_not_mulEquiv_dihedral (p := 11) (by norm_num)

/-- **(3) Counting.** The list `[ℤ/22, DihedralGroup 11]` is a complete, non-redundant list of
representatives of the groups of order `22` — assembled from exhaustiveness (`classification`)
and distinctness (`distinct`). -/
theorem isClassif : IsClassif 22 (rep2 (CyclicRep 22) (DihedralGroup 11)) :=
  isClassif_two _ _ (card_cyclicRep (by norm_num)) DihedralGroup.nat_card
    (fun _ _ hG => classification hG) distinct

/-- **The number of isomorphism classes of groups of order `22` is exactly `2`:** any complete
list of pairwise non-isomorphic representatives has length `2`. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 22 rep) : k = 2 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order22
