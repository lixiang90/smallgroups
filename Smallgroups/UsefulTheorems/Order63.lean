/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order2PSq
import Smallgroups.UsefulTheorems.PrimePairNonabelian
import Smallgroups.UsefulTheorems.PrimeSqClassification
import Smallgroups.UsefulTheorems.SchurZassenhaus
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic.NormNum.Prime

/-!
# Useful theorems for groups of order 63

For `63 = 7 * 3^2`, Sylow counting makes the Sylow-`7` subgroup normal.  Hence every group of
order `63` splits, by Schur--Zassenhaus, as a semidirect product `C₇ ⋊ K` with `|K| = 9`.

This file sets up the four expected representatives and proves the bookkeeping facts that are
independent of the remaining action classification:

* all four representatives have order `63`;
* they are pairwise non-isomorphic;
* every group of order `63` has a normal subgroup of order `7` and a semidirect-product
  decomposition over a complement of order `9`;
* a small split lemma for semidirect products whose acting group is a direct product and whose
  action factors through the first component.
-/

namespace Smallgroups.UsefulTheorems

open Sylow

/-! ### Representatives -/

/-- `7` is prime. -/
theorem order63_prime7 : Nat.Prime 7 := by norm_num

/-- A unit of order `3` in `(ZMod 7)ˣ`, which exists because `3 ∣ 7 - 1`. -/
noncomputable def order63_c₀ : (ZMod 7)ˣ :=
  (exists_unit_orderOf_eq order63_prime7 (q := 3) (by norm_num)).choose

theorem order63_hc₀order : orderOf order63_c₀ = 3 :=
  (exists_unit_orderOf_eq order63_prime7 (q := 3) (by norm_num)).choose_spec.1

theorem order63_hc₀pow3 : order63_c₀ ^ 3 = 1 :=
  (exists_unit_orderOf_eq order63_prime7 (q := 3) (by norm_num)).choose_spec.2

theorem order63_hc₀pow9 : order63_c₀ ^ 9 = 1 := by
  rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul, order63_hc₀pow3, one_pow]

theorem order63_hc₀ne : order63_c₀ ≠ 1 := by
  intro h
  have ho := order63_hc₀order
  rw [h, orderOf_one] at ho
  norm_num at ho

/-- The cyclic group `C₆₃`. -/
abbrev order63_RA : Type := CyclicRep 63

/-- The abelian non-cyclic group `C₇ × C₃ × C₃`. -/
abbrev order63_RB : Type := CyclicRep 7 × ElemAbelianRep 3

/-- The non-abelian group `(C₇ ⋊ C₃) × C₃`. -/
abbrev order63_RC : Type := NonabRep order63_c₀ order63_hc₀pow3 × CyclicRep 3

/-- The non-abelian group `C₇ ⋊ C₉`, where the `C₉` action has image of order `3`. -/
abbrev order63_RD : Type := NonabRep order63_c₀ order63_hc₀pow9

/-! ### Cardinalities -/

theorem card_order63_RA : Nat.card order63_RA = 63 :=
  card_cyclicRep (by norm_num)

theorem card_order63_RB : Nat.card order63_RB = 63 := by
  rw [Nat.card_prod, card_cyclicRep (by norm_num : (7 : ℕ) ≠ 0),
    card_elemAbelianRep (by norm_num : (3 : ℕ) ≠ 0)]
  norm_num

theorem card_order63_RC : Nat.card order63_RC = 63 := by
  rw [Nat.card_prod, card_nonabRep' order63_c₀ order63_hc₀pow3,
    card_cyclicRep (by norm_num : (3 : ℕ) ≠ 0)]

theorem card_order63_RD : Nat.card order63_RD = 63 := by
  rw [card_nonabRep' order63_c₀ order63_hc₀pow9]

/-! ### Commutativity and distinctness -/

theorem order63_RA_comm : ∀ a b : order63_RA, a * b = b * a :=
  fun a b => mul_comm a b

theorem order63_RB_comm : ∀ a b : order63_RB, a * b = b * a :=
  fun a b => mul_comm a b

theorem elemAbelianRep3_not_isCyclic : ¬ IsCyclic (ElemAbelianRep 3) := by
  intro hcyc
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclic (ElemAbelianRep 3) := hcyc
  have hIso : Nonempty (ElemAbelianRep 3 ≃* CyclicRep (3 ^ 2)) :=
    cyclicRep_classification (by norm_num : 3 ^ 2 ≠ 0)
      (card_elemAbelianRep (by norm_num : (3 : ℕ) ≠ 0))
  exact prime_sq_distinct (p := 3) ⟨hIso.some.symm⟩

theorem order63_RB_not_isCyclic : ¬ IsCyclic order63_RB := by
  intro hcyc
  exact elemAbelianRep3_not_isCyclic
    (isCyclic_of_surjective (MonoidHom.snd (CyclicRep 7) (ElemAbelianRep 3))
      Prod.snd_surjective)

theorem order63_RA_not_mulEquiv_RB : ¬ Nonempty (order63_RA ≃* order63_RB) := by
  rintro ⟨e⟩
  exact order63_RB_not_isCyclic (isCyclic_of_surjective e e.surjective)

theorem order63_RC_not_comm : ¬ ∀ a b : order63_RC, a * b = b * a := by
  intro h
  have hfirst : ∀ a b : NonabRep order63_c₀ order63_hc₀pow3, a * b = b * a := by
    intro a b
    have hh := h (a, (1 : CyclicRep 3)) (b, (1 : CyclicRep 3))
    exact congrArg Prod.fst hh
  exact nonabRep_not_comm (by norm_num) order63_c₀ order63_hc₀pow3 order63_hc₀ne hfirst

theorem order63_RD_not_comm : ¬ ∀ a b : order63_RD, a * b = b * a :=
  nonabRep_not_comm (by norm_num) order63_c₀ order63_hc₀pow9 order63_hc₀ne

theorem order63_RD_has_order9 : ∃ g : order63_RD, orderOf g = 9 := by
  use SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 9))
  rw [orderOf_injective (SemidirectProduct.inr : Multiplicative (ZMod 9) →* order63_RD)
    SemidirectProduct.inr_injective]
  rw [orderOf_ofAdd_eq_addOrderOf]
  exact ZMod.addOrderOf_one 9

theorem order63_RC_pow21 (g : order63_RC) : g ^ 21 = 1 := by
  have h1dvd : orderOf g.1 ∣ 21 := by
    simpa [card_nonabRep' order63_c₀ order63_hc₀pow3] using
      (orderOf_dvd_natCard g.1)
  have h1 : g.1 ^ 21 = 1 := orderOf_dvd_iff_pow_eq_one.mp h1dvd
  have h2dvd : orderOf g.2 ∣ 3 := by
    simpa [card_cyclicRep (by norm_num : (3 : ℕ) ≠ 0)] using
      (orderOf_dvd_natCard g.2)
  have h2 : g.2 ^ 21 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (dvd_trans h2dvd (by norm_num))
  rw [Prod.pow_mk, h1, h2]
  simp

theorem order63_RC_no_order9 (g : order63_RC) : orderOf g ≠ 9 :=
  orderOf_ne_of_pow order63_RC_pow21 (by norm_num : ¬ 9 ∣ 21) g

theorem order63_RC_not_mulEquiv_RD : ¬ Nonempty (order63_RC ≃* order63_RD) := by
  intro h
  exact not_mulEquiv_of_orderOf order63_RD_has_order9 order63_RC_no_order9 ⟨h.some.symm⟩

theorem order63_RA_not_mulEquiv_RC : ¬ Nonempty (order63_RA ≃* order63_RC) :=
  isEmpty_mulEquiv_of_comm_noncomm order63_RA_comm order63_RC_not_comm

theorem order63_RA_not_mulEquiv_RD : ¬ Nonempty (order63_RA ≃* order63_RD) :=
  isEmpty_mulEquiv_of_comm_noncomm order63_RA_comm order63_RD_not_comm

theorem order63_RB_not_mulEquiv_RC : ¬ Nonempty (order63_RB ≃* order63_RC) :=
  isEmpty_mulEquiv_of_comm_noncomm order63_RB_comm order63_RC_not_comm

theorem order63_RB_not_mulEquiv_RD : ¬ Nonempty (order63_RB ≃* order63_RD) :=
  isEmpty_mulEquiv_of_comm_noncomm order63_RB_comm order63_RD_not_comm

/-- The four expected representatives of order `63` are pairwise non-isomorphic. -/
theorem order63_pairwise :
    PairwiseNonMulEquiv (rep4 order63_RA order63_RB order63_RC order63_RD) := by
  intro i j hiso
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd hiso order63_RA_not_mulEquiv_RB
  · exact absurd hiso order63_RA_not_mulEquiv_RC
  · exact absurd hiso order63_RA_not_mulEquiv_RD
  · exact absurd ⟨hiso.some.symm⟩ order63_RA_not_mulEquiv_RB
  · rfl
  · exact absurd hiso order63_RB_not_mulEquiv_RC
  · exact absurd hiso order63_RB_not_mulEquiv_RD
  · exact absurd ⟨hiso.some.symm⟩ order63_RA_not_mulEquiv_RC
  · exact absurd ⟨hiso.some.symm⟩ order63_RB_not_mulEquiv_RC
  · rfl
  · exact absurd hiso order63_RC_not_mulEquiv_RD
  · exact absurd ⟨hiso.some.symm⟩ order63_RA_not_mulEquiv_RD
  · exact absurd ⟨hiso.some.symm⟩ order63_RB_not_mulEquiv_RD
  · exact absurd ⟨hiso.some.symm⟩ order63_RC_not_mulEquiv_RD
  · rfl

/-! ### Sylow and Schur--Zassenhaus reduction -/

variable {G : Type*} [Group G]

theorem card_sylow7_eq_one_of_card63 [Finite G] (hG : Nat.card G = 63) :
    Nat.card (Sylow 7 G) = 1 := by
  haveI : Fact (Nat.Prime 7) := ⟨order63_prime7⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 7 G))
  have hdvd63 : Nat.card (Sylow 7 G) ∣ 63 := by
    rw [← hG]
    exact P0.card_dvd_index.trans (Subgroup.index_dvd_card _)
  have hndvd : ¬ 7 ∣ Nat.card (Sylow 7 G) := not_dvd_card_sylow 7 G
  have hcop : Nat.Coprime (Nat.card (Sylow 7 G)) 7 :=
    (Nat.prime_seven.coprime_iff_not_dvd.mpr hndvd).symm
  have hdvd9 : Nat.card (Sylow 7 G) ∣ 3 ^ 2 := by
    have hdvd : Nat.card (Sylow 7 G) ∣ 7 * 9 := by
      simpa using hdvd63
    have hdiv : Nat.card (Sylow 7 G) ∣ 9 := hcop.dvd_of_dvd_mul_left hdvd
    simpa using hdiv
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd9
  interval_cases k
  · rwa [pow_zero] at hk
  · exfalso
    have hmod := card_sylow_modEq_one 7 G
    rw [pow_one] at hk
    rw [hk] at hmod
    have hnot : ¬ 3 ≡ 1 [MOD 7] := by norm_num [Nat.ModEq]
    exact hnot hmod
  · exfalso
    have hmod := card_sylow_modEq_one 7 G
    rw [show 3 ^ 2 = 9 by norm_num] at hk
    rw [hk] at hmod
    have hnot : ¬ 9 ≡ 1 [MOD 7] := by norm_num [Nat.ModEq]
    exact hnot hmod

theorem sylow7_normal_of_card63 [Finite G] (hG : Nat.card G = 63) (P : Sylow 7 G) :
    (↑P : Subgroup G).Normal := by
  haveI : Fact (Nat.Prime 7) := ⟨order63_prime7⟩
  haveI : Subsingleton (Sylow 7 G) :=
    (Nat.card_eq_one_iff_unique.mp (card_sylow7_eq_one_of_card63 hG)).1
  exact normal_of_subsingleton P

theorem card_sylow7_subgroup_of_card63 [Finite G] (hG : Nat.card G = 63) (P : Sylow 7 G) :
    Nat.card (↑P : Subgroup G) = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨order63_prime7⟩
  rw [Sylow.card_eq_multiplicity, hG]
  have hfact : (63).factorization 7 = 1 := by
    rw [show 63 = 7 * 9 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_seven,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 7 ∣ 9), add_zero]
  rw [hfact]
  norm_num

theorem order63_semidirect [Finite G] (hG : Nat.card G = 63) :
    ∃ (N K : Subgroup G) (φ : K →* MulAut N),
      N.Normal ∧ Nat.card N = 7 ∧ Nat.card K = 9 ∧
        Nonempty (G ≃* SemidirectProduct N K φ) := by
  haveI : Fact (Nat.Prime 7) := ⟨order63_prime7⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 7 G))
  let N : Subgroup G := ↑P0
  haveI hNnorm : N.Normal := sylow7_normal_of_card63 hG P0
  have hNcard : Nat.card N = 7 := card_sylow7_subgroup_of_card63 hG P0
  obtain ⟨K, φ, hnonempty⟩ := schurZassenhaus_of_card (G := G) (m := 7) (n := 9)
    (by simpa using hG) (by norm_num : Nat.Coprime 7 9) N hNcard
  have hKcard : Nat.card K = 9 := by
    rcases hnonempty with ⟨e⟩
    have h1 : Nat.card G = Nat.card N * Nat.card K := by
      rw [Nat.card_congr e.toEquiv, Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
    rw [hG, hNcard] at h1
    exact (Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 7) h1).symm
  exact ⟨N, K, φ, hNnorm, hNcard, hKcard, hnonempty⟩

/-! ### Semidirect products with a product complement -/

variable {N B C : Type*} [Group N] [Group B] [Group C]

/-- If the action of `B × C` on `N` factors through `B`, then the semidirect product splits as
`(N ⋊ B) × C`. -/
def semidirectProductSplitComplement (ψ : B →* MulAut N) :
    SemidirectProduct N (B × C) (ψ.comp (MonoidHom.fst B C)) ≃*
      SemidirectProduct N B ψ × C where
  toFun x := (⟨x.left, x.right.1⟩, x.right.2)
  invFun y := ⟨y.1.left, (y.1.right, y.2)⟩
  left_inv x := by cases x; rfl
  right_inv y := by obtain ⟨x, c⟩ := y; cases x; rfl
  map_mul' x y := by
    refine Prod.ext (SemidirectProduct.ext ?_ ?_) ?_ <;> rfl

/-- The action of `C₃ × C₃` on `C₇` through the first factor, using `order63_c₀`. -/
noncomputable def order63_elemAction :
    ElemAbelianRep 3 →* MulAut (CyclicRep 7) :=
  (actionHom order63_c₀ order63_hc₀pow3).comp
    (MonoidHom.fst (CyclicRep 3) (CyclicRep 3))

/-- The semidirect product where only the first `C₃` factor acts is the representative `RC`. -/
noncomputable def order63_elemAction_mulEquiv_RC :
    SemidirectProduct (CyclicRep 7) (ElemAbelianRep 3) order63_elemAction ≃* order63_RC :=
  semidirectProductSplitComplement (N := CyclicRep 7) (B := CyclicRep 3) (C := CyclicRep 3)
    (actionHom order63_c₀ order63_hc₀pow3)

end Smallgroups.UsefulTheorems
