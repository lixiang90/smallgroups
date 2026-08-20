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

/-! ### Cube roots over a commutative kernel -/

noncomputable abbrev order48_c3Generator : Multiplicative (ZMod 3) :=
  Multiplicative.ofAdd (1 : ZMod 3)

/-- In the generator fibre of a semidirect product with commutative kernel,
the cube-root equation is exactly the order-three norm equation. -/
theorem order48_c3_action_cube_generator_iff_norm_one
    {K : Type} [CommGroup K]
    (φ : Multiplicative (ZMod 3) →* MulAut K) (x : K) :
    (⟨x, order48_c3Generator⟩ :
      SemidirectProduct K (Multiplicative (ZMod 3)) φ) ^ 3 = 1 ↔
      x * φ order48_c3Generator x *
        φ order48_c3Generator (φ order48_c3Generator x) = 1 := by
  rw [pow_three]
  constructor
  · intro h
    have hleft := congrArg SemidirectProduct.left h
    simp only [SemidirectProduct.mul_left, SemidirectProduct.one_left] at hleft
    rw [(φ order48_c3Generator).map_mul] at hleft
    simpa only [mul_assoc] using hleft
  · intro h
    apply SemidirectProduct.ext
    · simp only [SemidirectProduct.mul_left, SemidirectProduct.one_left]
      rw [(φ order48_c3Generator).map_mul]
      simpa only [mul_assoc] using h
    · change order48_c3Generator *
        (order48_c3Generator * order48_c3Generator) = 1
      decide

/-- The inverse-generator fibre has the same norm equation. -/
theorem order48_c3_action_cube_generator_sq_iff_norm_one
    {K : Type} [CommGroup K]
    (φ : Multiplicative (ZMod 3) →* MulAut K) (x : K) :
    (⟨x, order48_c3Generator ^ 2⟩ :
      SemidirectProduct K (Multiplicative (ZMod 3)) φ) ^ 3 = 1 ↔
      x * φ order48_c3Generator x *
        φ order48_c3Generator (φ order48_c3Generator x) = 1 := by
  have hthree : φ order48_c3Generator
      (φ order48_c3Generator (φ order48_c3Generator x)) = x := by
    have hp := congrArg (fun a : MulAut K => a x)
      (order48_c3_action_generator_pow_three φ)
    simpa only [pow_succ, pow_zero, mul_one, MulAut.mul_apply,
      MulAut.one_apply] using hp
  have hc2 : φ (order48_c3Generator ^ 2) x =
      φ order48_c3Generator (φ order48_c3Generator x) := by
    rw [map_pow, pow_two]
    rfl
  have hc22 : φ (order48_c3Generator ^ 2)
      (φ (order48_c3Generator ^ 2) x) = φ order48_c3Generator x := by
    rw [map_pow, pow_two, MulAut.mul_apply, MulAut.mul_apply]
    exact congrArg (φ order48_c3Generator) hthree
  rw [pow_three]
  constructor
  · intro hpair
    have h := congrArg SemidirectProduct.left hpair
    simp only [SemidirectProduct.mul_left, SemidirectProduct.one_left] at h
    rw [(φ (order48_c3Generator ^ 2)).map_mul] at h
    rw [hc22, hc2] at h
    convert h using 1
    all_goals ac_rfl
  · intro h
    apply SemidirectProduct.ext
    · simp only [SemidirectProduct.mul_left, SemidirectProduct.one_left]
      rw [(φ (order48_c3Generator ^ 2)).map_mul]
      rw [hc22, hc2]
      convert h using 1
      all_goals ac_rfl
    · change (order48_c3Generator ^ 2) *
        ((order48_c3Generator ^ 2) * (order48_c3Generator ^ 2)) = 1
      decide

private noncomputable def order48_c3ActionRootsSigmaEquiv
    {K : Type} [Group K]
    (φ : Multiplicative (ZMod 3) →* MulAut K) :
    {z : SemidirectProduct K (Multiplicative (ZMod 3)) φ // z ^ 3 = 1} ≃
      Σ g : Multiplicative (ZMod 3),
        {x : K // (⟨x, g⟩ : SemidirectProduct K _ φ) ^ 3 = 1} where
  toFun z := ⟨z.1.right, ⟨z.1.left, z.2⟩⟩
  invFun z := ⟨⟨z.2.1, z.1⟩, z.2.2⟩
  left_inv z := by cases z; rfl
  right_inv z := by cases z with | mk g z => cases z; rfl

private noncomputable def order48_subtypeIffEquiv
    {α : Type} {p q : α → Prop} (h : ∀ x, p x ↔ q x) :
    Subtype p ≃ Subtype q where
  toFun x := ⟨x, (h x).mp x.2⟩
  invFun x := ⟨x, (h x).mpr x.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

/-- For an elementary abelian `2`-kernel, the cube roots consist of the
identity plus two copies of the kernel of the order-three norm. -/
theorem order48_c3_action_card_cube_roots_eq_one_add_twice_norm
    {K : Type} [CommGroup K] [Finite K]
    (h2 : ∀ x : K, x ^ 2 = 1)
    (φ : Multiplicative (ZMod 3) →* MulAut K) :
    Nat.card {z : SemidirectProduct K (Multiplicative (ZMod 3)) φ //
        z ^ 3 = 1} =
      1 + 2 * Nat.card {x : K //
        x * φ order48_c3Generator x *
          φ order48_c3Generator (φ order48_c3Generator x) = 1} := by
  rw [Nat.card_congr (order48_c3ActionRootsSigmaEquiv φ), Nat.card_sigma]
  change (∑ g : Multiplicative (ZMod 3), Nat.card
    {x : K // (⟨x, g⟩ : SemidirectProduct K _ φ) ^ 3 = 1}) = _
  have hsum : (∑ g : Multiplicative (ZMod 3), Nat.card
      {x : K // (⟨x, g⟩ : SemidirectProduct K _ φ) ^ 3 = 1}) =
      Nat.card {x : K //
        (⟨x, 1⟩ : SemidirectProduct K _ φ) ^ 3 = 1} +
      Nat.card {x : K //
        (⟨x, order48_c3Generator⟩ : SemidirectProduct K _ φ) ^ 3 = 1} +
      Nat.card {x : K //
        (⟨x, order48_c3Generator ^ 2⟩ :
          SemidirectProduct K _ φ) ^ 3 = 1} := by
    classical
    exact Fin.sum_univ_three _
  rw [hsum]
  have hOne : Nat.card
      {x : K // (⟨x, 1⟩ : SemidirectProduct K _ φ) ^ 3 = 1} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    constructor
    · constructor
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      apply Subtype.ext
      have toOne : ∀ z : K,
          (⟨z, 1⟩ : SemidirectProduct K _ φ) ^ 3 = 1 → z = 1 := by
        intro z hz
        have hzleft := congrArg SemidirectProduct.left hz
        simp only [pow_three, SemidirectProduct.mul_left,
          SemidirectProduct.one_left, map_one, MulAut.one_apply] at hzleft
        have hz2 := h2 z
        rw [pow_two] at hz2
        simpa [hz2] using hzleft
      exact (toOne x hx).trans (toOne y hy).symm
    · exact ⟨1, by simp⟩
  rw [hOne]
  have hc : Nat.card {x : K //
      (⟨x, order48_c3Generator⟩ : SemidirectProduct K _ φ) ^ 3 = 1} =
      Nat.card {x : K // x * φ order48_c3Generator x *
        φ order48_c3Generator (φ order48_c3Generator x) = 1} := by
    apply Nat.card_congr
    exact order48_subtypeIffEquiv
      (order48_c3_action_cube_generator_iff_norm_one φ)
  have hc2 : Nat.card {x : K //
      (⟨x, order48_c3Generator ^ 2⟩ :
        SemidirectProduct K _ φ) ^ 3 = 1} =
      Nat.card {x : K // x * φ order48_c3Generator x *
        φ order48_c3Generator (φ order48_c3Generator x) = 1} := by
    apply Nat.card_congr
    exact order48_subtypeIffEquiv
      (order48_c3_action_cube_generator_sq_iff_norm_one φ)
  omega

/-- Thus the residual root count `9` is equivalent to a four-element norm
kernel for an elementary abelian order-`16` kernel. -/
theorem order48_c3_action_card_cube_roots_eq_nine_iff_norm_card_four
    {K : Type} [CommGroup K] [Finite K]
    (h2 : ∀ x : K, x ^ 2 = 1)
    (φ : Multiplicative (ZMod 3) →* MulAut K) :
    Nat.card {z : SemidirectProduct K (Multiplicative (ZMod 3)) φ //
        z ^ 3 = 1} = 9 ↔
      Nat.card {x : K // x * φ order48_c3Generator x *
        φ order48_c3Generator (φ order48_c3Generator x) = 1} = 4 := by
  rw [order48_c3_action_card_cube_roots_eq_one_add_twice_norm h2 φ]
  omega

/-- The order-three norm on a commutative kernel, regarded as a group
homomorphism. -/
noncomputable def order48_c3ActionNormHom
    {K : Type} [CommGroup K]
    (φ : Multiplicative (ZMod 3) →* MulAut K) : K →* K where
  toFun x := x * φ order48_c3Generator x *
    φ order48_c3Generator (φ order48_c3Generator x)
  map_one' := by
    rw [(φ order48_c3Generator).map_one]
    rw [(φ order48_c3Generator).map_one]
    group
  map_mul' x y := by
    rw [(φ order48_c3Generator).map_mul,
      (φ order48_c3Generator).map_mul]
    ac_rfl

/-- For an exponent-two commutative kernel, the norm image is precisely the
fixed subgroup of the action generator. -/
theorem order48_c3ActionNormHom_range_eq_fixed
    {K : Type} [CommGroup K]
    (h2 : ∀ x : K, x ^ 2 = 1)
    (φ : Multiplicative (ZMod 3) →* MulAut K) :
    (order48_c3ActionNormHom φ).range =
      {x : K | φ order48_c3Generator x = x} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    change φ order48_c3Generator
      (x * φ order48_c3Generator x *
        φ order48_c3Generator (φ order48_c3Generator x)) = _
    rw [(φ order48_c3Generator).map_mul,
      (φ order48_c3Generator).map_mul]
    have hp := congrArg (fun a : MulAut K => a x)
      (order48_c3_action_generator_pow_three φ)
    have h3 : φ order48_c3Generator
        (φ order48_c3Generator (φ order48_c3Generator x)) = x := by
      simpa [order48_c3Generator, pow_succ, MulAut.mul_apply] using hp
    rw [h3]
    change _ = x * φ order48_c3Generator x *
      φ order48_c3Generator (φ order48_c3Generator x)
    ac_rfl
  · intro hy
    refine ⟨y, ?_⟩
    change y * φ order48_c3Generator y *
      φ order48_c3Generator (φ order48_c3Generator y) = y
    rw [hy, hy]
    have hy2 := h2 y
    rw [pow_two] at hy2
    simp [hy2]

/-- On an elementary abelian kernel of order `16`, residual root count `9`
forces the generator-fixed subgroup to have order `4`. -/
theorem order48_c3_action_fixed_card_four_of_card_cube_roots_nine
    {K : Type} [CommGroup K] [Finite K]
    (hK : Nat.card K = 16) (h2 : ∀ x : K, x ^ 2 = 1)
    (φ : Multiplicative (ZMod 3) →* MulAut K)
    (hRoots : Nat.card {z : SemidirectProduct K (Multiplicative (ZMod 3)) φ //
      z ^ 3 = 1} = 9) :
    Nat.card {x : K // φ order48_c3Generator x = x} = 4 := by
  have hker : Nat.card (order48_c3ActionNormHom φ).ker = 4 := by
    have := (order48_c3_action_card_cube_roots_eq_nine_iff_norm_card_four
      h2 φ).mp hRoots
    simpa [order48_c3ActionNormHom, MonoidHom.mem_ker] using this
  have hrange : Nat.card (order48_c3ActionNormHom φ).range = 4 := by
    have hmul := (order48_c3ActionNormHom φ).ker.card_mul_index
    rw [Subgroup.index_ker, hker, hK] at hmul
    omega
  have heq := order48_c3ActionNormHom_range_eq_fixed h2 φ
  exact (Nat.card_congr (Equiv.setCongr heq)).symm.trans hrange

end Smallgroups.UsefulTheorems
