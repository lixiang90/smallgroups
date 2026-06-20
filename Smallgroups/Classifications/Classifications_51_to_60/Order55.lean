/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PrimePairNonabelian
import Smallgroups.UsefulTheorems.Counting
import Mathlib.Tactic.NormNum.Prime

/-!
# Classification of groups of order 55

`55 = 11 * 5` with `5 ∣ 11 - 1`, so there are exactly **two** groups of order `55`
up to isomorphism: the cyclic group `ℤ/55` and the non-abelian semidirect product
`ℤ/11 ⋊ ℤ/5` (`NonabRep c₀`, for an order-`5` unit `c₀` of `(ZMod 11)ˣ`).
-/

namespace Smallgroups.Classifications.Order55

open Smallgroups.UsefulTheorems

/-- `11` is prime. -/
theorem prime_p : Nat.Prime 11 := by norm_num

/-- `5` is prime. -/
theorem prime_q : Nat.Prime 5 := by norm_num

/-- A unit of order `5` in `(ZMod 11)ˣ`, which exists because `5 ∣ 11 - 1`. -/
noncomputable def c₀ : (ZMod 11)ˣ := (exists_unit_orderOf_eq prime_p (q := 5) (by norm_num)).choose

theorem hc₀order : orderOf c₀ = 5 :=
  (exists_unit_orderOf_eq prime_p (q := 5) (by norm_num)).choose_spec.1

theorem hc₀pow : c₀ ^ 5 = 1 :=
  (exists_unit_orderOf_eq prime_p (q := 5) (by norm_num)).choose_spec.2

theorem hc₀ne : c₀ ≠ 1 := by
  intro h; have ho := hc₀order; rw [h, orderOf_one] at ho; norm_num at ho

/-- The non-abelian representative `ℤ/11 ⋊ ℤ/5`. -/
abbrev NonabRep55 : Type := NonabRep c₀ hc₀pow

variable {G : Type*} [Group G]

/-- **(1) Exhaustiveness.** Every group of order `55` is isomorphic to the cyclic group
`ℤ/55` or to the non-abelian group `ℤ/11 ⋊ ℤ/5`. -/
theorem classification (h : Nat.card G = 55) :
    Nonempty (G ≃* CyclicRep 55) ∨ Nonempty (G ≃* NonabRep55) :=
  classification_card_eq_prime_mul' prime_p prime_q (by norm_num) (h.trans (by norm_num))
    c₀ hc₀pow hc₀ne

/-- **(2) Distinctness.** `ℤ/55` and `ℤ/11 ⋊ ℤ/5` are not isomorphic (the latter is not
cyclic). -/
theorem distinct : ¬ Nonempty (CyclicRep 55 ≃* NonabRep55) :=
  cyclicRep_not_mulEquiv_nonabRep (by norm_num) c₀ hc₀pow hc₀ne

/-- **(3) Counting.** The list `[ℤ/55, ℤ/11 ⋊ ℤ/5]` is a complete, non-redundant list of
representatives of the groups of order `55`. -/
theorem isClassif : IsClassif 55 (rep2 (CyclicRep 55) NonabRep55) :=
  isClassif_two _ _ (card_cyclicRep (by norm_num)) (card_nonabRep' c₀ hc₀pow)
    (fun _ _ hG => classification hG) distinct

/-- **The number of isomorphism classes of groups of order `55` is exactly `2`.** -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 55 rep) : k = 2 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order55
