/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order4P
import Smallgroups.UsefulTheorems.Order2PSq
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic.NormNum.Prime

/-!
# Classification of groups of order `12` (`4 · 3`, the special case `p = 3`)

Every group of order `4p` with `p ≥ 5` has a unique Sylow-`p` subgroup (i.e. `n_p = 1`).
When `p = 3` this argument fails: the Sylow-3 count satisfies `n₃ ∣ 4` and `n₃ ≡ 1 [MOD 3]`,
giving `n₃ ∈ {1, 4}`.

* **`n₃ = 1`** (Sylow-3 normal): the same analysis as the `4p` case with `p ≡ 3 [MOD 4]`
  applies, yielding four types:
  - Type I:   `ℤ/12` (cyclic)
  - Type II:  `ℤ/2 × ℤ/6` (abelian, non-cyclic)
  - Type III: `ℤ/3 ⋊_{-1} ℤ/4` (a.k.a. `Dic₃`, the dicyclic group)
  - Type V:   `ℤ/2 × D₆` (equivalently `ℤ/2 × S₃`)

* **`n₃ = 4`** (Sylow-3 not normal): the conjugation action on the four Sylow-3 subgroups gives
  an injective homomorphism `G → S₄`, whose image is the unique index-2 subgroup `A₄`.

There are exactly **five** isomorphism classes of groups of order `12`.
-/

namespace Smallgroups.UsefulTheorems

open Sylow Equiv.Perm

/-! ### The alternating group `A₄` as the fifth type -/

/-- The alternating group on 4 letters, the unique order-12 group with non-normal Sylow-3. -/
abbrev fourP_A4 : Type := alternatingGroup (Fin 4)

/-- `|A₄| = 12`. -/
theorem card_fourP_A4 : Nat.card fourP_A4 = 12 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

/-- `A₄` is not abelian. -/
theorem fourP_A4_not_comm : ¬ ∀ a b : fourP_A4, a * b = b * a := by
  intro h
  have : Nat.card (Fin 4) ≤ 3 :=
    alternatingGroup.isMulCommutative_iff_card_le_three.mp ⟨⟨h⟩⟩
  simp at this

/-- Every element of `A₄` satisfies `g² = 1` or `g³ = 1`
(the only element orders are `1, 2, 3`). -/
theorem fourP_A4_pow : ∀ g : fourP_A4, g ^ 2 = 1 ∨ g ^ 3 = 1 := by decide

/-- `A₄` has no element of order `4`. -/
theorem fourP_A4_no_order4 : ∀ g : fourP_A4, orderOf g ≠ 4 :=
  orderOf_ne_of_pow_or fourP_A4_pow (by decide) (by decide)

/-- `A₄` has no element of order `6`. -/
theorem fourP_A4_no_order6 : ∀ g : fourP_A4, orderOf g ≠ 6 :=
  orderOf_ne_of_pow_or fourP_A4_pow (by decide) (by decide)

/-! ### Element-order witnesses for Types III and V at `p = 3` -/

private instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- Type III (`ℤ/3 ⋊_{-1} ℤ/4`) has an element of order `4`. -/
theorem fourP_III_3_has_order4 : ∃ g : fourP_III 3, orderOf g = 4 := by
  use SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 4))
  rw [orderOf_injective (SemidirectProduct.inr : Multiplicative (ZMod 4) →* _)
    SemidirectProduct.inr_injective]
  rw [orderOf_ofAdd_eq_addOrderOf]
  exact ZMod.addOrderOf_one 4

/-- Type V (`ℤ/2 × D₆`) has an element of order `6`. -/
theorem fourP_V_3_has_order6 : ∃ g : fourP_V 3, orderOf g = 6 := by
  use (Multiplicative.ofAdd (1 : ZMod 2), DihedralGroup.r (1 : ZMod 3))
  rw [Prod.orderOf_mk, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one,
    DihedralGroup.orderOf_r_one]
  decide

/-! ### Distinctness -/

/-- Types I and A₄ are not isomorphic (abelian vs non-abelian). -/
theorem fourP_I_ne_A4 : ¬ Nonempty (fourP_I 3 ≃* fourP_A4) :=
  isEmpty_mulEquiv_of_comm_noncomm (fourP_I_comm 3) fourP_A4_not_comm

/-- Types II and A₄ are not isomorphic (abelian vs non-abelian). -/
theorem fourP_II_ne_A4 : ¬ Nonempty (fourP_II 3 ≃* fourP_A4) :=
  isEmpty_mulEquiv_of_comm_noncomm (fourP_II_comm 3) fourP_A4_not_comm

/-- Types III and A₄ are not isomorphic (III has order-4 elements, A₄ doesn't). -/
theorem fourP_III_ne_A4 : ¬ Nonempty (fourP_III 3 ≃* fourP_A4) :=
  not_mulEquiv_of_orderOf fourP_III_3_has_order4 fourP_A4_no_order4

/-- Types V and A₄ are not isomorphic (V has order-6 elements, A₄ doesn't). -/
theorem fourP_V_ne_A4 : ¬ Nonempty (fourP_V 3 ≃* fourP_A4) :=
  not_mulEquiv_of_orderOf fourP_V_3_has_order6 fourP_A4_no_order6

/-! ### Exhaustiveness -/

/-- **Exhaustiveness.** Every group of order `12` is isomorphic to one of the five types:
`ℤ/12`, `ℤ/2 × ℤ/6`, `ℤ/3 ⋊_{-1} ℤ/4`, `ℤ/2 × D₆`, or `A₄`. -/
theorem fourP_12_classification {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 12) :
    Nonempty (G ≃* fourP_I 3) ∨
    Nonempty (G ≃* fourP_II 3) ∨
    Nonempty (G ≃* fourP_III 3) ∨
    Nonempty (G ≃* fourP_V 3) ∨
    Nonempty (G ≃* fourP_A4) := by
  sorry

/-! ### IsClassif -/

/-- **The five representatives form a complete classification of groups of order `12`.** -/
theorem fourP_12_isClassif :
    IsClassif 12 (rep5 (fourP_I 3) (fourP_II 3) (fourP_III 3) (fourP_V 3) fourP_A4) := by
  exact isClassif_five (fourP_I 3) (fourP_II 3) (fourP_III 3) (fourP_V 3) fourP_A4
    (card_fourP_I 3) (card_fourP_II 3) (card_fourP_III 3 (by norm_num)) (card_fourP_V 3)
    card_fourP_A4
    (fun G _ hG => by
      haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
      exact fourP_12_classification hG)
    (fourP_I_ne_II (p := 3) (by norm_num))
    (fourP_I_ne_III (p := 3) (by norm_num))
    (fourP_I_ne_V (p := 3) (by norm_num))
    fourP_I_ne_A4
    (fourP_II_ne_III (p := 3) (by norm_num))
    (fourP_II_ne_V (p := 3) (by norm_num))
    fourP_II_ne_A4
    (fourP_III_ne_V (p := 3) (by norm_num))
    fourP_III_ne_A4
    fourP_V_ne_A4

end Smallgroups.UsefulTheorems
