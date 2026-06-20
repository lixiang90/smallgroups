/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PrimePairDihedral
import Smallgroups.UsefulTheorems.Counting
import Mathlib.Tactic.NormNum.Prime

/-!
# Classification of groups of order 58

`58 = 2 * 29` with `29` an odd prime, so there are exactly **two** groups of order `58`
up to isomorphism: the cyclic group `ℤ/58` and the dihedral group `DihedralGroup 29`.

* `classification` — (1) exhaustiveness: every group of order `58` is cyclic or dihedral.
* `distinct` — (2) distinctness: the two are not isomorphic.
* `isClassif` / `numIsoClasses_eq` — (3) counting: there are exactly two isomorphism classes.
-/

namespace Smallgroups.Classifications.Order58

open Smallgroups.UsefulTheorems

variable {G : Type*} [Group G]

/-- `29` is prime. -/
theorem prime_p : Nat.Prime 29 := by norm_num

/-- `29` is odd. -/
theorem odd_p : Odd 29 := by decide

/-- **(1) Exhaustiveness.** Every group of order `58` is isomorphic to the cyclic group
`ℤ/58` (`CyclicRep 58`) or to the dihedral group `DihedralGroup 29`. -/
theorem classification (h : Nat.card G = 58) :
    Nonempty (G ≃* CyclicRep 58) ∨ Nonempty (G ≃* DihedralGroup 29) :=
  classification_card_two_mul_prime prime_p odd_p (h.trans (by norm_num))

/-- **(2) Distinctness.** `ℤ/58` and `DihedralGroup 29` are not isomorphic (the latter is not
cyclic). -/
theorem distinct : ¬ Nonempty (CyclicRep 58 ≃* DihedralGroup 29) :=
  cyclicRep_not_mulEquiv_dihedral (p := 29) (by norm_num)

/-- **(3) Counting.** The list `[ℤ/58, DihedralGroup 29]` is a complete, non-redundant list of
representatives of the groups of order `58` — assembled from exhaustiveness (`classification`)
and distinctness (`distinct`). -/
theorem isClassif : IsClassif 58 (rep2 (CyclicRep 58) (DihedralGroup 29)) :=
  isClassif_two _ _ (card_cyclicRep (by norm_num)) DihedralGroup.nat_card
    (fun _ _ hG => classification hG) distinct

/-- **The number of isomorphism classes of groups of order `58` is exactly `2`:** any complete
list of pairwise non-isomorphic representatives has length `2`. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 58 rep) : k = 2 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order58
