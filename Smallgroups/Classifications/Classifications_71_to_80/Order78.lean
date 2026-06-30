/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order2PQ
import Smallgroups.UsefulTheorems.Counting
import Mathlib.Tactic.NormNum.Prime

/-!
# Classification of groups of order 78

`78 = 2 * 3 * 13` with `2 < 3 < 13` and `3 ∣ 13 - 1`, so there are exactly **six** groups of order
`78` up to isomorphism (the `6`-class case of the order-`2pq` classification):

* Type I: `ℤ/78` (cyclic)
* Type II: `D₃₉` (dihedral of order `78`)
* Type III: `ℤ/13 × D₃`
* Type IV: `ℤ/3 × D₁₃`
* Type V: `(ℤ/13 ⋊ ℤ/3) × ℤ/2`
* Type VI: `ℤ/13 ⋊ ℤ/6`
-/

namespace Smallgroups.Classifications.Order78

open Smallgroups.UsefulTheorems

/-- `3` is prime. -/
theorem prime_p : Nat.Prime 3 := by norm_num

/-- `13` is prime. -/
theorem prime_q : Nat.Prime 13 := by norm_num

/-- `3 ∣ 13 - 1`, so the two extra (non-abelian-`N`) types appear. -/
theorem hmod : (3 : ℕ) ∣ 13 - 1 := by decide

/-- A unit of order `3` in `(ZMod 13)ˣ`, giving the action of type V. -/
noncomputable def c₀ : (ZMod 13)ˣ := (twoPQ_exists_unit_p 3 13 prime_p prime_q hmod).choose

theorem hc₀pow : c₀ ^ 3 = 1 :=
  (twoPQ_exists_unit_p 3 13 prime_p prime_q hmod).choose_spec.2.1

theorem hc₀ne : c₀ ≠ 1 :=
  (twoPQ_exists_unit_p 3 13 prime_p prime_q hmod).choose_spec.2.2

/-- A unit of order `2 * 3 = 6` in `(ZMod 13)ˣ`, giving the faithful action of type VI. -/
noncomputable def d₀ : (ZMod 13)ˣ :=
  (twoPQ_exists_unit_2p 3 13 prime_p prime_q (by norm_num) hmod).choose

theorem hd₀ord : orderOf d₀ = 2 * 3 :=
  (twoPQ_exists_unit_2p 3 13 prime_p prime_q (by norm_num) hmod).choose_spec.1

theorem hd₀pow : d₀ ^ (2 * 3) = 1 :=
  (twoPQ_exists_unit_2p 3 13 prime_p prime_q (by norm_num) hmod).choose_spec.2

theorem hd₀ne : d₀ ≠ 1 := by
  intro h; have ho := hd₀ord; rw [h, orderOf_one] at ho; norm_num at ho

/-- **(1) Exhaustiveness.** Every group of order `78` is isomorphic to one of the six types. -/
theorem classification {G : Type*} [Group G] (h : Nat.card G = 78) :
    Nonempty (G ≃* twoPQ_I 3 13) ∨ Nonempty (G ≃* twoPQ_II 3 13) ∨
    Nonempty (G ≃* twoPQ_III 3 13) ∨ Nonempty (G ≃* twoPQ_IV 3 13) ∨
    Nonempty (G ≃* twoPQ_V 3 13 c₀ hc₀pow) ∨ Nonempty (G ≃* twoPQ_VI 3 13 d₀ hd₀pow) := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  exact twoPQ_classification_6 3 13 prime_p prime_q (by norm_num) (by norm_num) hmod
    c₀ hc₀pow hc₀ne d₀ hd₀pow hd₀ord h

/-- **(2) Distinctness.** The six types are pairwise non-isomorphic. -/
theorem distinct :
    PairwiseNonMulEquiv
      (rep6 (twoPQ_I 3 13) (twoPQ_II 3 13) (twoPQ_III 3 13) (twoPQ_IV 3 13)
            (twoPQ_V 3 13 c₀ hc₀pow) (twoPQ_VI 3 13 d₀ hd₀pow)) :=
  twoPQ_pairwiseDistinct_6 3 13 prime_p prime_q (by norm_num) (by norm_num)
    c₀ hc₀pow hc₀ne d₀ hd₀pow hd₀ne hd₀ord

/-- **(3) Counting.** The six types form a complete, non-redundant list of representatives of the
groups of order `78`. -/
theorem isClassif :
    IsClassif 78
      (rep6 (twoPQ_I 3 13) (twoPQ_II 3 13) (twoPQ_III 3 13) (twoPQ_IV 3 13)
            (twoPQ_V 3 13 c₀ hc₀pow) (twoPQ_VI 3 13 d₀ hd₀pow)) :=
  twoPQ_isClassif_6 3 13 prime_p prime_q (by norm_num) (by norm_num) hmod
    c₀ hc₀pow hc₀ne d₀ hd₀pow hd₀ord hd₀ne

/-- **The number of isomorphism classes of groups of order `78` is exactly `6`.** -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 78 rep) : k = 6 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order78
