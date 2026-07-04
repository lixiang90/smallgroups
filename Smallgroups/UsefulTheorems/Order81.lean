/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Counting
import Smallgroups.UsefulTheorems.P3Group
import Smallgroups.UsefulTheorems.PrimePairNonabelian
import Smallgroups.UsefulTheorems.OrderP4_Abel
import Smallgroups.UsefulTheorems.OrderP4_NonAbel
import Mathlib.Tactic.NormNum.Prime

/-!
# First structural facts for groups of order `81`

`81 = 3^4`.  The abelian part is already covered by the general classification of abelian
groups of order `p^4`, giving the five groups corresponding to the partitions of `4`.

For the non-abelian part, this file records the first split supplied by the existing
`OrderP4_NonAbel` development: the center has order `3` or `9`, and hence is one of
`C_3`, `C_9`, or `C_3 × C_3`.

This is intentionally not yet a full classification of groups of order `81`: the ten
non-abelian representatives and their distinctness still need a separate development.
-/

namespace Smallgroups.UsefulTheorems

open Subgroup
open P3Group

/-! ## The five abelian representatives -/

/-- The five abelian representatives of order `81`. -/
noncomputable abbrev order81_abelian_reps : Fin 5 → Type :=
  orderP4Abel_reps 3

noncomputable instance instCommGroupOrder81AbelianReps (i : Fin 5) :
    CommGroup (order81_abelian_reps i) :=
  inferInstance

/-- Every abelian representative has order `81`. -/
theorem card_order81_abelian_reps (i : Fin 5) :
    Nat.card (order81_abelian_reps i) = 81 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  dsimp [order81_abelian_reps]
  rw [card_orderP4Abel_reps 3 i]
  norm_num

/-- Every abelian group of order `81` is isomorphic to one of the five abelian representatives. -/
theorem order81_abelian_complete (G : Type*) [CommGroup G] (hcard : Nat.card G = 81) :
    ∃ i, Nonempty (G ≃* order81_abelian_reps i) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  dsimp [order81_abelian_reps]
  exact orderP4Abel_complete 3 G (by rw [hcard]; norm_num)

/-- The five abelian representatives of order `81` are pairwise non-isomorphic. -/
theorem order81_abelian_distinct : PairwiseNonMulEquiv order81_abelian_reps := by
  intro i j h
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  dsimp [order81_abelian_reps] at h ⊢
  exact orderP4Abel_distinct 3 i j h

/-! ## The first non-abelian split -/

/-- In a non-abelian group of order `81`, the center has order `3` or `9`. -/
theorem order81_center_card_eq_three_or_nine {G : Type*} [Group G]
    (hcard : Nat.card G = 81) (hnonab : ¬ (∀ a b : G, a * b = b * a)) :
    Nat.card (center G) = 3 ∨ Nat.card (center G) = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hcard' : Nat.card G = 3 ^ 4 := by
    rw [hcard]
    norm_num
  rcases center_card_eq_p_or_p_sq_of_nonabelian_p4 (p := 3) hcard' hnonab with hcenter | hcenter
  · exact Or.inl hcenter
  · right
    rw [hcenter]
    norm_num

/-- In a non-abelian group of order `81`, the center is `C_3`, `C_9`, or `C_3 × C_3`. -/
theorem order81_center_classification_of_nonabelian {G : Type*} [Group G]
    (hcard : Nat.card G = 81) (hnonab : ¬ (∀ a b : G, a * b = b * a)) :
    Nonempty (center G ≃* CyclicRep 3) ∨
    Nonempty (center G ≃* CyclicRep 9) ∨
    Nonempty (center G ≃* ElemAbelianRep 3) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hcard' : Nat.card G = 3 ^ 4 := by
    rw [hcard]
    norm_num
  simpa using center_classification_of_nonabelian_p4 (p := 3) hcard' hnonab

/-! ## Two immediate non-abelian representatives -/

/-- `HeisenbergGroup 3 × C_3`, a non-abelian group of order `81`. -/
abbrev order81_heisenberg_prod_cyclic : Type :=
  HeisenbergGroup 3 × CyclicRep 3

/-- `SemidirectP2P 3 × C_3`, a non-abelian group of order `81`. -/
abbrev order81_semidirectP2P_prod_cyclic : Type :=
  SemidirectP2P 3 × CyclicRep 3

/-- `HeisenbergGroup 3 × C_3` has order `81`. -/
theorem card_order81_heisenberg_prod_cyclic :
    Nat.card order81_heisenberg_prod_cyclic = 81 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [order81_heisenberg_prod_cyclic, Nat.card_prod, HeisenbergGroup.card_heisenberg 3,
    card_cyclicRep (by norm_num : (3 : ℕ) ≠ 0)]
  norm_num

/-- `SemidirectP2P 3 × C_3` has order `81`. -/
theorem card_order81_semidirectP2P_prod_cyclic :
    Nat.card order81_semidirectP2P_prod_cyclic = 81 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [order81_semidirectP2P_prod_cyclic, Nat.card_prod,
    SemidirectP2P.card_semidirectP2P 3, card_cyclicRep (by norm_num : (3 : ℕ) ≠ 0)]
  norm_num

/-- `HeisenbergGroup 3 × C_3` is non-abelian. -/
theorem order81_heisenberg_prod_cyclic_nonabelian :
    ¬ ∀ x y : order81_heisenberg_prod_cyclic, x * y = y * x := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  intro hcomm
  exact HeisenbergGroup.heisenberg_nonabelian 3 (by
    intro x y
    have h := hcomm ((x, (1 : CyclicRep 3)) : order81_heisenberg_prod_cyclic)
      ((y, (1 : CyclicRep 3)) : order81_heisenberg_prod_cyclic)
    exact congrArg Prod.fst h)

/-- `SemidirectP2P 3 × C_3` is non-abelian. -/
theorem order81_semidirectP2P_prod_cyclic_nonabelian :
    ¬ ∀ x y : order81_semidirectP2P_prod_cyclic, x * y = y * x := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  intro hcomm
  exact SemidirectP2P.semidirectP2P_nonabelian 3 (by
    intro x y
    have h := hcomm ((x, (1 : CyclicRep 3)) : order81_semidirectP2P_prod_cyclic)
      ((y, (1 : CyclicRep 3)) : order81_semidirectP2P_prod_cyclic)
    exact congrArg Prod.fst h)

/-- `HeisenbergGroup 3 × C_3` has exponent `3`. -/
theorem exponent_order81_heisenberg_prod_cyclic :
    Monoid.exponent order81_heisenberg_prod_cyclic = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  change Monoid.exponent (HeisenbergGroup 3 × CyclicRep 3) = 3
  rw [Monoid.exponent_prod, HeisenbergGroup.heisenberg_exponent 3 (by norm_num)]
  simp only [Monoid.exponent_multiplicative, ZMod.exponent]
  norm_num [lcm_eq_nat_lcm]

/-- `SemidirectP2P 3 × C_3` has exponent `9`. -/
theorem exponent_order81_semidirectP2P_prod_cyclic :
    Monoid.exponent order81_semidirectP2P_prod_cyclic = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  change Monoid.exponent (SemidirectP2P 3 × CyclicRep 3) = 9
  rw [Monoid.exponent_prod, SemidirectP2P.semidirectP2P_exponent 3]
  simp only [Monoid.exponent_multiplicative, ZMod.exponent]
  norm_num [lcm_eq_nat_lcm]

/-- The two direct-product non-abelian representatives are not isomorphic. -/
theorem order81_heisenberg_prod_cyclic_not_equiv_semidirectP2P_prod_cyclic :
    ¬ Nonempty (order81_heisenberg_prod_cyclic ≃* order81_semidirectP2P_prod_cyclic) := by
  rintro ⟨e⟩
  have hExp : Monoid.exponent order81_heisenberg_prod_cyclic =
      Monoid.exponent order81_semidirectP2P_prod_cyclic :=
    Monoid.exponent_eq_of_mulEquiv e
  rw [exponent_order81_heisenberg_prod_cyclic, exponent_order81_semidirectP2P_prod_cyclic] at hExp
  norm_num at hExp

/-- The two direct-product non-abelian representatives of order `81`. -/
abbrev order81_direct_nonabelian_reps : Fin 2 → Type :=
  rep2 order81_heisenberg_prod_cyclic order81_semidirectP2P_prod_cyclic

/-- Each direct-product non-abelian representative has order `81`. -/
theorem card_order81_direct_nonabelian_reps (i : Fin 2) :
    Nat.card (order81_direct_nonabelian_reps i) = 81 := by
  fin_cases i
  · exact card_order81_heisenberg_prod_cyclic
  · exact card_order81_semidirectP2P_prod_cyclic

/-- Each direct-product non-abelian representative is non-abelian. -/
theorem order81_direct_nonabelian_reps_nonabelian (i : Fin 2) :
    ¬ ∀ x y : order81_direct_nonabelian_reps i, x * y = y * x := by
  fin_cases i
  · exact order81_heisenberg_prod_cyclic_nonabelian
  · exact order81_semidirectP2P_prod_cyclic_nonabelian

/-- The two direct-product non-abelian representatives are pairwise non-isomorphic. -/
theorem order81_direct_nonabelian_reps_pairwise :
    PairwiseNonMulEquiv order81_direct_nonabelian_reps := by
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd h order81_heisenberg_prod_cyclic_not_equiv_semidirectP2P_prod_cyclic
  · exact absurd ⟨h.some.symm⟩
      order81_heisenberg_prod_cyclic_not_equiv_semidirectP2P_prod_cyclic
  · rfl

/-! ## A split `C_9 × C_3` extension by `C_3` -/

/-- `C_9 × C_3`, written multiplicatively. -/
abbrev order81_C9C3 : Type :=
  Multiplicative (ZMod 9) × Multiplicative (ZMod 3)

/-- Reduction modulo `3`, as a ring hom `ZMod 9 →+* ZMod 3`. -/
noncomputable abbrev order81_zmod9To3 : ZMod 9 →+* ZMod 3 :=
  ZMod.castHom (by norm_num : 3 ∣ 9) (ZMod 3)

/-- The additive shear `(a, b) ↦ (a, b + a mod 3)` on `ZMod 9 × ZMod 3`. -/
noncomputable def order81_c9c3_shearAddEquiv : (ZMod 9 × ZMod 3) ≃+ (ZMod 9 × ZMod 3) where
  toFun x := (x.1, x.2 + order81_zmod9To3 x.1)
  invFun x := (x.1, x.2 - order81_zmod9To3 x.1)
  left_inv := by
    intro x
    ext <;> simp [order81_zmod9To3]
  right_inv := by
    intro x
    ext <;> simp [order81_zmod9To3]
  map_add' := by
    intro x y
    ext <;> simp [order81_zmod9To3, add_assoc, add_left_comm]

/-- The corresponding automorphism of `C_9 × C_3`. -/
noncomputable def order81_c9c3_shearAut : MulAut order81_C9C3 :=
  (MulEquiv.prodMultiplicative (ZMod 9) (ZMod 3)).symm.trans
    ((AddEquiv.toMultiplicative order81_c9c3_shearAddEquiv).trans
      (MulEquiv.prodMultiplicative (ZMod 9) (ZMod 3)))

@[simp] theorem order81_c9c3_shearAut_apply (a : ZMod 9) (b : ZMod 3) :
    order81_c9c3_shearAut
      ((Multiplicative.ofAdd a, Multiplicative.ofAdd b) : order81_C9C3) =
      (Multiplicative.ofAdd a, Multiplicative.ofAdd (b + order81_zmod9To3 a)) := by
  rfl

/-- The shear automorphism has order dividing `3`. -/
theorem order81_c9c3_shearAut_pow_three : order81_c9c3_shearAut ^ 3 = 1 := by
  ext x <;> fin_cases x <;> rfl

/-- The action of `C_3` generated by a chosen automorphism whose cube is the identity. -/
noncomputable def order81_actionOfOrderThree {N : Type*} [Group N]
    (α : MulAut N) (hα : α ^ 3 = 1) : CyclicRep 3 →* MulAut N :=
  MonoidHom.mk' (fun x => α ^ (Multiplicative.toAdd x).val)
    (fun x y => pow_val_add hα (Multiplicative.toAdd x) (Multiplicative.toAdd y))

theorem order81_actionOfOrderThree_ofAdd_one {N : Type*} [Group N]
    (α : MulAut N) (hα : α ^ 3 = 1) :
    order81_actionOfOrderThree α hα (Multiplicative.ofAdd (1 : ZMod 3)) = α := by
  change α ^ (1 : ZMod 3).val = α
  rw [show (1 : ZMod 3).val = 1 by decide, pow_one]

/-- The `C_3` action on `C_9 × C_3` generated by the shear automorphism. -/
noncomputable abbrev order81_c9c3_shearAction : CyclicRep 3 →* MulAut order81_C9C3 :=
  order81_actionOfOrderThree order81_c9c3_shearAut order81_c9c3_shearAut_pow_three

/-- The split semidirect product `(C_9 × C_3) ⋊ C_3` using the shear action. -/
abbrev order81_c9c3_shear_rep : Type :=
  SemidirectProduct order81_C9C3 (CyclicRep 3) order81_c9c3_shearAction

theorem card_order81_C9C3 : Nat.card order81_C9C3 = 27 := by
  rw [order81_C9C3, Nat.card_prod, card_cyclicRep (by norm_num : (9 : ℕ) ≠ 0),
    card_cyclicRep (by norm_num : (3 : ℕ) ≠ 0)]

/-- The shear semidirect product has order `81`. -/
theorem card_order81_c9c3_shear_rep : Nat.card order81_c9c3_shear_rep = 81 := by
  rw [order81_c9c3_shear_rep, SemidirectProduct.card, card_order81_C9C3,
    card_cyclicRep (by norm_num : (3 : ℕ) ≠ 0)]

/-- The shear semidirect product is non-abelian. -/
theorem order81_c9c3_shear_rep_nonabelian :
    ¬ ∀ x y : order81_c9c3_shear_rep, x * y = y * x := by
  intro hcomm
  let g : CyclicRep 3 := Multiplicative.ofAdd (1 : ZMod 3)
  let n : order81_C9C3 :=
    (Multiplicative.ofAdd (1 : ZMod 9), Multiplicative.ofAdd (0 : ZMod 3))
  have hfix : order81_c9c3_shearAut n = n := by
    have heq : (SemidirectProduct.inl (order81_c9c3_shearAction g n) :
        order81_c9c3_shear_rep) = SemidirectProduct.inl n := by
      have h := hcomm (SemidirectProduct.inr g : order81_c9c3_shear_rep)
        (SemidirectProduct.inl n : order81_c9c3_shear_rep)
      rw [SemidirectProduct.inl_aut (φ := order81_c9c3_shearAction) g n]
      rw [h, mul_assoc, ← map_mul, mul_inv_cancel, map_one]
      simp
    have hinj := SemidirectProduct.inl_injective heq
    simpa [order81_c9c3_shearAction, g, order81_actionOfOrderThree_ofAdd_one] using hinj
  have hnot : order81_c9c3_shearAut n ≠ n := by
    intro h
    have hsnd := congrArg (fun z : order81_C9C3 => Multiplicative.toAdd z.2) h
    norm_num [order81_c9c3_shearAut, order81_c9c3_shearAddEquiv, order81_zmod9To3, n] at hsnd
  exact hnot hfix

/-- A visible element of order `9` in the shear semidirect product. -/
noncomputable def order81_c9c3_shear_orderNineElem : order81_c9c3_shear_rep :=
  SemidirectProduct.inl
    ((Multiplicative.ofAdd (1 : ZMod 9), Multiplicative.ofAdd (0 : ZMod 3)) : order81_C9C3)

theorem orderOf_order81_c9c3_shear_orderNineElem :
    orderOf order81_c9c3_shear_orderNineElem = 9 := by
  unfold order81_c9c3_shear_orderNineElem
  rw [orderOf_injective SemidirectProduct.inl SemidirectProduct.inl_injective]
  rw [Prod.orderOf_mk]
  rw [orderOf_ofAdd_eq_addOrderOf, orderOf_ofAdd_eq_addOrderOf]
  rw [ZMod.addOrderOf_one]
  norm_num [lcm_eq_nat_lcm]

/-- The shear semidirect product is not the exponent-`3` direct-product representative. -/
theorem order81_c9c3_shear_rep_not_equiv_heisenberg_prod_cyclic :
    ¬ Nonempty (order81_c9c3_shear_rep ≃* order81_heisenberg_prod_cyclic) := by
  rintro ⟨e⟩
  have hord : orderOf (e order81_c9c3_shear_orderNineElem) = 9 := by
    rw [MulEquiv.orderOf_eq e, orderOf_order81_c9c3_shear_orderNineElem]
  have hdvd : orderOf (e order81_c9c3_shear_orderNineElem) ∣
      Monoid.exponent order81_heisenberg_prod_cyclic :=
    Monoid.order_dvd_exponent _
  rw [hord, exponent_order81_heisenberg_prod_cyclic] at hdvd
  norm_num at hdvd

/-! ## The currently formalized representatives -/

/-- The five abelian representatives together with the two direct-product non-abelian
representatives formalized above. -/
abbrev order81_known_reps : Fin 5 ⊕ Fin 2 → Type :=
  Sum.elim order81_abelian_reps order81_direct_nonabelian_reps

/-- Every currently formalized representative has order `81`. -/
theorem card_order81_known_reps (i : Fin 5 ⊕ Fin 2) :
    Nat.card (order81_known_reps i) = 81 := by
  rcases i with i | i
  · exact card_order81_abelian_reps i
  · exact card_order81_direct_nonabelian_reps i

/-- No abelian representative is isomorphic to one of the non-abelian direct-product
representatives. -/
theorem order81_abelian_direct_nonabelian_disjoint :
    ∀ i j, ¬ Nonempty (order81_abelian_reps i ≃* order81_direct_nonabelian_reps j) :=
  pairwise_disjoint_of_comm_noncomm
    (fun _ a b => mul_comm a b)
    order81_direct_nonabelian_reps_nonabelian

/-- The currently formalized seven representatives are pairwise non-isomorphic. -/
theorem order81_known_reps_pairwise : PairwiseNonMulEquiv order81_known_reps := by
  simpa [order81_known_reps] using
    PairwiseNonMulEquiv.sum order81_abelian_distinct order81_direct_nonabelian_reps_pairwise
      order81_abelian_direct_nonabelian_disjoint

end Smallgroups.UsefulTheorems
