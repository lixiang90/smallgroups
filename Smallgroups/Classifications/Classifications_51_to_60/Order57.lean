/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PrimePairNonabelian
import Smallgroups.UsefulTheorems.Counting
import Mathlib.Tactic.NormNum.Prime

/-!
# Classification of groups of order 57

`57 = 19 * 3` with `3 ∣ 19 - 1`, so there are exactly **two** groups of order `57`
up to isomorphism: the cyclic group `ℤ/57` and the non-abelian semidirect product
`ℤ/19 ⋊ ℤ/3` (`NonabRep c₀`, for an order-`3` unit `c₀` of `(ZMod 19)ˣ`).
-/

namespace Smallgroups.Classifications.Order57

open Smallgroups.UsefulTheorems

/-- `19` is prime. -/
theorem prime_p : Nat.Prime 19 := by norm_num

/-- `3` is prime. -/
theorem prime_q : Nat.Prime 3 := by norm_num

/-- A unit of order `3` in `(ZMod 19)ˣ`, which exists because `3 ∣ 19 - 1`. -/
noncomputable def c₀ : (ZMod 19)ˣ := (exists_unit_orderOf_eq prime_p (q := 3) (by norm_num)).choose

theorem hc₀order : orderOf c₀ = 3 :=
  (exists_unit_orderOf_eq prime_p (q := 3) (by norm_num)).choose_spec.1

theorem hc₀pow : c₀ ^ 3 = 1 :=
  (exists_unit_orderOf_eq prime_p (q := 3) (by norm_num)).choose_spec.2

theorem hc₀ne : c₀ ≠ 1 := by
  intro h; have ho := hc₀order; rw [h, orderOf_one] at ho; norm_num at ho

/-- The non-abelian representative `ℤ/19 ⋊ ℤ/3`. -/
abbrev NonabRep57 : Type := NonabRep c₀ hc₀pow

variable {G : Type*} [Group G]

/-- **(1) Exhaustiveness.** Every group of order `57` is isomorphic to the cyclic group
`ℤ/57` or to the non-abelian group `ℤ/19 ⋊ ℤ/3`. -/
theorem classification (h : Nat.card G = 57) :
    Nonempty (G ≃* CyclicRep 57) ∨ Nonempty (G ≃* NonabRep57) :=
  classification_card_eq_prime_mul' prime_p prime_q (by norm_num) (h.trans (by norm_num))
    c₀ hc₀pow hc₀ne

/-- **(2) Distinctness.** `ℤ/57` and `ℤ/19 ⋊ ℤ/3` are not isomorphic (the latter is not
cyclic). -/
theorem distinct : ¬ Nonempty (CyclicRep 57 ≃* NonabRep57) :=
  cyclicRep_not_mulEquiv_nonabRep (by norm_num) c₀ hc₀pow hc₀ne

/-- **(3) Counting.** The list `[ℤ/57, ℤ/19 ⋊ ℤ/3]` is a complete, non-redundant list of
representatives of the groups of order `57`. -/
theorem isClassif : IsClassif 57 (rep2 (CyclicRep 57) NonabRep57) :=
  isClassif_two _ _ (card_cyclicRep (by norm_num)) (card_nonabRep' c₀ hc₀pow)
    (fun _ _ hG => classification hG) distinct

/-- **The number of isomorphism classes of groups of order `57` is exactly `2`.** -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 57 rep) : k = 2 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order57
