/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order72.H8xP9
import Smallgroups.UsefulTheorems.Counting
import Smallgroups.UsefulTheorems.CenterInvariant

namespace Smallgroups.UsefulTheorems

/-! # Direct-product branch distinctness for groups of order 72 -/

noncomputable def order72_direct_pow_eq_one_card (H : Type*) [Group H] (n : Nat) : Nat :=
  Nat.card {x : H // x ^ n = 1}

noncomputable def order72_direct_powEqOneEquivOfMulEquiv {H K : Type*} [Group H] [Group K]
    (n : Nat) (e : H ≃* K) :
    {x : H // x ^ n = 1} ≃ {y : K // y ^ n = 1} where
  toFun x := ⟨e x.1, by
    rw [← map_pow, x.2, map_one]⟩
  invFun y := ⟨e.symm y.1, by
    rw [← map_pow, y.2, map_one]⟩
  left_inv x := by
    ext
    simp
  right_inv x := by
    ext
    simp

theorem order72_direct_pow_eq_one_card_eq_of_mulEquiv {H K : Type*} [Group H] [Group K]
    (n : Nat) (e : H ≃* K) :
    order72_direct_pow_eq_one_card H n = order72_direct_pow_eq_one_card K n :=
  Nat.card_congr (order72_direct_powEqOneEquivOfMulEquiv n e)

/-- The ten direct products in the order-72 representative list. -/
noncomputable abbrev order72_direct_reps : Fin 10 → Type
  | 0 => CyclicRep 9 × Multiplicative (ZMod 8)
  | 1 => CyclicRep 9 × H2
  | 2 => CyclicRep 9 × E8
  | 3 => CyclicRep 9 × DihedralGroup 4
  | 4 => CyclicRep 9 × QuaternionGroup 2
  | 5 => ElemAbelianRep 3 × Multiplicative (ZMod 8)
  | 6 => ElemAbelianRep 3 × H2
  | 7 => ElemAbelianRep 3 × E8
  | 8 => ElemAbelianRep 3 × DihedralGroup 4
  | 9 => ElemAbelianRep 3 × QuaternionGroup 2

noncomputable instance order72_direct_reps_group :
    (i : Fin 10) → Group (order72_direct_reps i)
  | 0 => inferInstance
  | 1 => inferInstance
  | 2 => inferInstance
  | 3 => inferInstance
  | 4 => inferInstance
  | 5 => inferInstance
  | 6 => inferInstance
  | 7 => inferInstance
  | 8 => inferInstance
  | 9 => inferInstance
  | ⟨n + 10, h⟩ => by omega

noncomputable def order72_direct_invariant (i : Fin 10) : Nat × Nat × Nat × Nat :=
  (Nat.card (Subgroup.center (order72_direct_reps i)),
    order72_direct_pow_eq_one_card (order72_direct_reps i) 2,
    order72_direct_pow_eq_one_card (order72_direct_reps i) 3,
    order72_direct_pow_eq_one_card (order72_direct_reps i) 4)

theorem order72_direct_invariant_eq_of_mulEquiv {i j : Fin 10}
    (hiso : Nonempty (order72_direct_reps i ≃* order72_direct_reps j)) :
    order72_direct_invariant i = order72_direct_invariant j := by
  obtain ⟨e⟩ := hiso
  simp only [order72_direct_invariant]
  exact Prod.ext (card_center_eq_of_mulEquiv e)
    (Prod.ext (order72_direct_pow_eq_one_card_eq_of_mulEquiv 2 e)
      (Prod.ext (order72_direct_pow_eq_one_card_eq_of_mulEquiv 3 e)
        (order72_direct_pow_eq_one_card_eq_of_mulEquiv 4 e)))

def order72_direct_invariant_table : Fin 10 → Nat × Nat × Nat × Nat
  | 0 => (72, 2, 3, 4)
  | 1 => (72, 4, 3, 8)
  | 2 => (72, 8, 3, 8)
  | 3 => (18, 6, 3, 8)
  | 4 => (18, 2, 3, 8)
  | 5 => (72, 2, 9, 4)
  | 6 => (72, 4, 9, 8)
  | 7 => (72, 8, 9, 8)
  | 8 => (18, 6, 9, 8)
  | 9 => (18, 2, 9, 8)

set_option maxHeartbeats 1000000 in
-- Finite kernel computation over the ten concrete direct products.
theorem order72_direct_invariant_spec (i : Fin 10) :
    order72_direct_invariant i = order72_direct_invariant_table i := by
  classical
  fin_cases i <;>
    simp only [order72_direct_invariant, order72_direct_invariant_table,
      order72_direct_reps, order72_direct_pow_eq_one_card, Nat.card_eq_fintype_card]
  all_goals
    apply Prod.ext
    · norm_num
      decide +kernel
    · apply Prod.ext
      · norm_num
        decide +kernel
      · apply Prod.ext
        · norm_num
          decide +kernel
        · norm_num
          decide +kernel

theorem order72_direct_invariant_table_injective :
    Function.Injective order72_direct_invariant_table := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp [order72_direct_invariant_table] at h ⊢

theorem order72_direct_reps_pairwise :
    PairwiseNonMulEquiv order72_direct_reps := by
  exact PairwiseNonMulEquiv.of_invariant order72_direct_invariant
    (fun _ _ h => order72_direct_invariant_eq_of_mulEquiv h)
    (fun i j h _ =>
      order72_direct_invariant_table_injective (by
        rw [← order72_direct_invariant_spec i, ← order72_direct_invariant_spec j]
        exact h))

end Smallgroups.UsefulTheorems
