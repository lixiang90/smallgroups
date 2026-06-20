/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PrimePairDihedral
import Smallgroups.UsefulTheorems.Counting
import Mathlib.Tactic.NormNum.Prime

/-!
# Classification of groups of order 82

`82 = 2 * 41` with `41` an odd prime, so there are exactly **two** groups of order `82`
up to isomorphism: the cyclic group `ℤ/82` and the dihedral group `DihedralGroup 41`.

* `classification` — (1) exhaustiveness: every group of order `82` is cyclic or dihedral.
* `distinct` — (2) distinctness: the two are not isomorphic.
* `isClassif` / `numIsoClasses_eq` — (3) counting: there are exactly two isomorphism classes.
-/

namespace Smallgroups.Classifications.Order82

open Smallgroups.UsefulTheorems

variable {G : Type*} [Group G]

/-- `41` is prime. -/
theorem prime_p : Nat.Prime 41 := by norm_num

/-- `41` is odd. -/
theorem odd_p : Odd 41 := by decide

/-- **(1) Exhaustiveness.** Every group of order `82` is isomorphic to the cyclic group
`ℤ/82` (`CyclicRep 82`) or to the dihedral group `DihedralGroup 41`. -/
theorem classification (h : Nat.card G = 82) :
    Nonempty (G ≃* CyclicRep 82) ∨ Nonempty (G ≃* DihedralGroup 41) :=
  classification_card_two_mul_prime prime_p odd_p (h.trans (by norm_num))

/-- **(2) Distinctness.** `ℤ/82` and `DihedralGroup 41` are not isomorphic (the latter is not
cyclic). -/
theorem distinct : ¬ Nonempty (CyclicRep 82 ≃* DihedralGroup 41) :=
  cyclicRep_not_mulEquiv_dihedral (p := 41) (by norm_num)

/-- **(3) Counting.** The list `[ℤ/82, DihedralGroup 41]` is a complete, non-redundant list of
representatives of the groups of order `82` — assembled from exhaustiveness (`classification`)
and distinctness (`distinct`). -/
theorem isClassif : IsClassif 82 (rep2 (CyclicRep 82) (DihedralGroup 41)) :=
  isClassif_two _ _ (card_cyclicRep (by norm_num)) DihedralGroup.nat_card
    (fun _ _ hG => classification hG) distinct

/-- **The number of isomorphism classes of groups of order `82` is exactly `2`:** any complete
list of pairwise non-isomorphic representatives has length `2`. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 82 rep) : k = 2 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order82
