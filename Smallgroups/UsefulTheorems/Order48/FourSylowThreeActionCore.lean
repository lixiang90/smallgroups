/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.FourSylowThree

/-!
# Core filters for the order-48 `C₃` action tables

These lemmas are kept below the RM/RN files in the import graph.  They are
independent of the orbit tables and provide the uniform first filter: a
semidirect product with four Sylow `3`-subgroups cannot use the trivial action.
-/

namespace Smallgroups.UsefulTheorems

theorem order48_c3_action_generator_pow_three
    {K : Type} [Group K]
    (φ : Multiplicative (ZMod 3) →* MulAut K) :
    (φ (Multiplicative.ofAdd (1 : ZMod 3))) ^ 3 = 1 := by
  have hg : (Multiplicative.ofAdd (1 : ZMod 3)) ^ 3 = 1 := by
    decide
  rw [← map_pow, hg, map_one]

noncomputable def order48_sylowEquivOfMulEquiv
    {G H : Type*} [Group G] [Group H] {p : ℕ} (e : G ≃* H) :
    Sylow p G ≃ Sylow p H where
  toFun P := P.comapOfInjective e.symm.toMonoidHom e.symm.injective
    (by rw [MonoidHom.range_eq_top.mpr e.symm.surjective]; exact le_top)
  invFun Q := Q.comapOfInjective e.toMonoidHom e.injective
    (by rw [MonoidHom.range_eq_top.mpr e.surjective]; exact le_top)
  left_inv P := by
    apply Sylow.ext
    rw [Sylow.coe_comapOfInjective, Sylow.coe_comapOfInjective,
      Subgroup.comap_comap]
    have h : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    rw [h, Subgroup.comap_id]
  right_inv Q := by
    apply Sylow.ext
    rw [Sylow.coe_comapOfInjective, Sylow.coe_comapOfInjective,
      Subgroup.comap_comap]
    have h : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H := by
      ext x
      simp
    rw [h, Subgroup.comap_id]

theorem order48_card_sylow_of_mulEquiv
    {G H : Type*} [Group G] [Group H] (p : ℕ) (e : G ≃* H) :
    Nat.card (Sylow p G) = Nat.card (Sylow p H) :=
  Nat.card_congr (order48_sylowEquivOfMulEquiv e)

private theorem order48_card_sylow_three_eq_one_of_normal_card_three
    {H : Type*} [Group H] [Finite H] (hH : Nat.card H = 48)
    (N : Subgroup H) [N.Normal] (hN : Nat.card N = 3) :
    Nat.card (Sylow 3 H) = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hp : IsPGroup 3 N := IsPGroup.of_card (by rw [hN, pow_one])
  obtain ⟨P, hNP⟩ := hp.exists_le_sylow
  have hP : Nat.card (P : Subgroup H) = 3 := by
    rw [Sylow.card_eq_multiplicity, hH]
    decide +kernel
  have hNP' : N = (P : Subgroup H) :=
    Subgroup.eq_of_le_of_card_ge hNP (by rw [hN, hP])
  have hPnormal : (P : Subgroup H).Normal := by
    rw [← hNP']
    infer_instance
  letI : Unique (Sylow 3 H) := Sylow.unique_of_normal P hPnormal
  exact Nat.card_unique

private theorem order48_card_sylow_three_prod_of_card_sixteen
    {P : Type*} [Group P] [Finite P] (hP : Nat.card P = 16) :
    Nat.card (Sylow 3 (P × Multiplicative (ZMod 3))) = 1 := by
  let N : Subgroup (P × Multiplicative (ZMod 3)) :=
    (⊥ : Subgroup P).prod (⊤ : Subgroup (Multiplicative (ZMod 3)))
  haveI : N.Normal := by
    dsimp [N]
    infer_instance
  have hN : Nat.card N = 3 := by
    dsimp [N]
    rw [Nat.card_congr (Subgroup.prodEquiv (⊥ : Subgroup P)
      (⊤ : Subgroup (Multiplicative (ZMod 3)))).toEquiv,
      Nat.card_prod, Subgroup.card_bot, Subgroup.card_top,
      Nat.card_eq_fintype_card]
    decide
  apply order48_card_sylow_three_eq_one_of_normal_card_three
    (N := N)
  · rw [Nat.card_prod, hP, Nat.card_eq_fintype_card]
    decide
  · exact hN

private theorem order48_card_pow_three_eq_one_of_card_sylow_three_eq_one
    {H : Type*} [Group H] [Finite H] (hH : Nat.card H = 12)
    (hSyl : Nat.card (Sylow 3 H) = 1) :
    Nat.card {x : H // x ^ 3 = 1} = 3 := by
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow 3 H))
  letI : Subsingleton (Sylow 3 H) :=
    (Nat.card_eq_one_iff_unique.mp hSyl).1
  have hPnormal : (P : Subgroup H).Normal :=
    Sylow.normal_of_subsingleton P
  have hP : Nat.card (P : Subgroup H) = 3 := by
    rw [Sylow.card_eq_multiplicity, hH]
    have hfact : (12 : ℕ).factorization 3 = 1 := by
      rw [show (12 : ℕ) = 4 * 3 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (3 : ℕ) ∣ 4),
        (by norm_num : Nat.Prime 3).factorization_self, zero_add]
    rw [hfact, pow_one]
  let e : {x : H // x ^ 3 = 1} ≃ (P : Subgroup H) := {
    toFun := fun x => ⟨x.1, by
      have hdvd : orderOf x.1 ∣ 3 := orderOf_dvd_of_pow_eq_one x.2
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with hx1 | hx3
      · have hxone : x.1 = 1 := orderOf_eq_one_iff.mp hx1
        rw [hxone]
        exact Subgroup.one_mem _
      · let Q : Sylow 3 H := Sylow.ofCard (Subgroup.zpowers x.1) (by
          rw [Nat.card_zpowers, hx3]
          have hfact : (12 : ℕ).factorization 3 = 1 := by
            rw [show (12 : ℕ) = 4 * 3 by norm_num,
              Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
              Nat.factorization_eq_zero_of_not_dvd
                (by norm_num : ¬ (3 : ℕ) ∣ 4),
              (by norm_num : Nat.Prime 3).factorization_self, zero_add]
          rw [hH, hfact, pow_one])
        have hQP : Q = P := Subsingleton.elim _ _
        rw [← hQP]
        exact Subgroup.mem_zpowers x.1⟩
    invFun := fun x => ⟨x.1, by
      have hx := pow_card_eq_one' (x := x)
      rw [hP] at hx
      exact congrArg Subtype.val hx⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl }
  rw [Nat.card_congr e, hP]

theorem order48_card_sylow_three_eq_four_of_card_pow_three_eq_one
    {H : Type*} [Group H] [Finite H] (hH : Nat.card H = 12)
    (hRoots : Nat.card {x : H // x ^ 3 = 1} = 9) :
    Nat.card (Sylow 3 H) = 4 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 3 H))
  have hndvd : ¬ 3 ∣ Nat.card (Sylow 3 H) := not_dvd_card_sylow 3 H
  have hdvd12 : Nat.card (Sylow 3 H) ∣ 12 := by
    rw [← hH]
    exact P0.card_dvd_index.trans (Subgroup.index_dvd_card _)
  have hcop : Nat.Coprime (Nat.card (Sylow 3 H)) 3 :=
    ((show Nat.Prime 3 by norm_num).coprime_iff_not_dvd.mpr hndvd).symm
  have hdvd4 : Nat.card (Sylow 3 H) ∣ 4 := by
    apply hcop.dvd_of_dvd_mul_right
    simpa [show (12 : ℕ) = 4 * 3 by norm_num] using hdvd12
  have hmod := card_sylow_modEq_one 3 H
  have hle : Nat.card (Sylow 3 H) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd4
  have hpos : 0 < Nat.card (Sylow 3 H) := Nat.card_pos
  have hcases : Nat.card (Sylow 3 H) = 1 ∨ Nat.card (Sylow 3 H) = 4 := by
    interval_cases h : Nat.card (Sylow 3 H)
    all_goals simp_all [Nat.ModEq]
  rcases hcases with h1 | h4
  · have h3 := order48_card_pow_three_eq_one_of_card_sylow_three_eq_one hH h1
    omega
  · exact h4

/-- A four-Sylow-`3` semidirect product cannot come from the trivial action. -/
theorem order48_c3_action_generator_ne_one_of_card_sylow_four
    {P : Type} [Group P] [Finite P] (hP : Nat.card P = 16)
    (φ : Multiplicative (ZMod 3) →* MulAut P)
    (hSyl : Nat.card (Sylow 3
      (SemidirectProduct P (Multiplicative (ZMod 3)) φ)) = 4) :
    φ (Multiplicative.ofAdd (1 : ZMod 3)) ≠ 1 := by
  intro hgen
  have hφ : φ = 1 := by
    apply order24_c3_hom_ext (M := MulAut P)
    simpa using hgen
  have hprod := order48_card_sylow_three_prod_of_card_sixteen hP
  have htransport := order48_card_sylow_of_mulEquiv 3
    (SemidirectProduct.mulEquivProd :
      SemidirectProduct P (Multiplicative (ZMod 3)) 1 ≃*
        P × Multiplicative (ZMod 3))
  have hSyl' : Nat.card (Sylow 3
      (SemidirectProduct P (Multiplicative (ZMod 3)) 1)) = 4 := by
    rw [← hφ]
    exact hSyl
  have hbad : (4 : ℕ) = 1 := by
    calc
      4 = Nat.card (Sylow 3
          (SemidirectProduct P (Multiplicative (ZMod 3)) 1)) := hSyl'.symm
      _ = Nat.card (Sylow 3 (P × Multiplicative (ZMod 3))) := htransport
      _ = 1 := hprod
  omega

theorem order48_c3_action_generator_order_three_of_card_sylow_four
    {P : Type} [Group P] [Finite P] (hP : Nat.card P = 16)
    (φ : Multiplicative (ZMod 3) →* MulAut P)
    (hSyl : Nat.card (Sylow 3
      (SemidirectProduct P (Multiplicative (ZMod 3)) φ)) = 4) :
    orderOf (φ (Multiplicative.ofAdd (1 : ZMod 3))) = 3 := by
  apply orderOf_eq_prime
  · exact order48_c3_action_generator_pow_three φ
  · exact order48_c3_action_generator_ne_one_of_card_sylow_four hP φ hSyl

/-- The four-Sylow-`3` condition for an order-`16` semidirect product can be
read as the finite root count `9`.  This is the preferred invariant for the
remaining Wild action tables. -/
theorem order48_c3_action_card_sylow_three_eq_four_iff
    {P : Type} [Group P] [Finite P] (hP : Nat.card P = 16)
    (φ : Multiplicative (ZMod 3) →* MulAut P) :
    Nat.card (Sylow 3
      (SemidirectProduct P (Multiplicative (ZMod 3)) φ)) = 4 ↔
      Nat.card {x : SemidirectProduct P (Multiplicative (ZMod 3)) φ //
        x ^ 3 = 1} = 9 := by
  letI : Fintype P := Fintype.ofFinite P
  letI : Fintype (SemidirectProduct P (Multiplicative (ZMod 3)) φ) :=
    Fintype.ofEquiv (P × Multiplicative (ZMod 3))
      SemidirectProduct.equivProd.symm
  have hG : Nat.card (SemidirectProduct P
      (Multiplicative (ZMod 3)) φ) = 48 := by
    rw [SemidirectProduct.card, hP, Nat.card_eq_fintype_card]
    decide
  constructor
  · intro hSyl
    rw [order48_card_pow_three_eq_one hG, hSyl]
  · intro hroots
    rw [order48_card_pow_three_eq_one hG] at hroots
    omega

end Smallgroups.UsefulTheorems
