/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Mathlib.GroupTheory.NoncommCoprod
import Smallgroups.UsefulTheorems.Order81
import Smallgroups.UsefulTheorems.PGroupGeneration.Reconstruction

/-!
# Order 81, the final non-split case

This file works toward closing the last gap of the order-`81` exhaustiveness argument: a
non-abelian group of order `81` that is a non-split extension over a normal `C_9 × C_3`
kernel and has no element of order `27` is isomorphic to the non-split representative or
to `C_9 ⋊ C_9`.

The analysis is intrinsic (no cocycle enumeration): writing `D` for the "shift"
endomorphism `k ↦ (y k y⁻¹) k⁻¹` of the kernel induced by an outside element `y` of
order `9`, the center of `G` is `ker D`, and the two targets are separated by
`|ker D| = 9` (giving `C_9 ⋊ C_9` via an explicit two-generator presentation) versus
`|ker D| = 3` (giving the non-split representative).
-/

namespace Smallgroups.UsefulTheorems

open Subgroup

/-- Any outside element of a case-B group has order `9`. -/
theorem order81_caseB_orderOf_eq_nine
    {G : Type*} [Group G] {K : Subgroup G} [K.Normal]
    (hcard : Nat.card G = 81) (_hKcard : Nat.card K = 27)
    (hns : ∀ y : G, y ∉ K → y ^ 3 ≠ 1) (h27 : ∀ x : G, orderOf x ≠ 27)
    {y : G} (hyK : y ∉ K) :
    orderOf y = 9 := by
  have hy3ne : y ^ 3 ≠ 1 := hns y hyK
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hdvd : orderOf y ∣ 81 := by
    rw [← hcard]
    exact orderOf_dvd_natCard y
  have h81 : (81 : ℕ) = 3 ^ 4 := by norm_num
  rw [h81] at hdvd
  rcases (Nat.dvd_prime_pow Nat.prime_three).mp hdvd with ⟨k, hk4, hk⟩
  interval_cases k
  · exfalso
    apply hyK
    have h1 : y = 1 := orderOf_eq_one_iff.mp (by simpa using hk)
    simp [h1]
  · exfalso
    apply hy3ne
    have h3 : orderOf y = 3 := by simpa using hk
    exact orderOf_dvd_iff_pow_eq_one.mp (h3 ▸ dvd_refl _)
  · simpa using hk
  · exfalso
    exact h27 y (by simpa using hk)
  · exfalso
    have hord : orderOf y = 81 := by simpa using hk
    apply h27 (y ^ 3)
    rw [orderOf_pow, hord]
    norm_num

/-- The shift endomorphism `k ↦ (y k y⁻¹) · k⁻¹` of an abelian normal subgroup, as a
monoid homomorphism. -/
noncomputable def order81_caseB_shiftHom
    {G : Type*} [Group G] {K : Subgroup G} [K.Normal]
    (hKcomm : ∀ a b : K, a * b = b * a) (y : G) : K →* K :=
  MonoidHom.mk' (fun k => MulAut.conjNormal (H := K) y k * k⁻¹)
    (by
      letI : CommGroup K := { (inferInstance : Group K) with mul_comm := hKcomm }
      intro a b
      set ρ : MulAut K := MulAut.conjNormal (H := K) y
      rw [map_mul, mul_inv_rev, mul_comm b⁻¹ a⁻¹, mul_mul_mul_comm])

theorem order81_caseB_shiftHom_apply
    {G : Type*} [Group G] {K : Subgroup G} [K.Normal]
    (hKcomm : ∀ a b : K, a * b = b * a) (y : G) (k : K) :
    order81_caseB_shiftHom hKcomm y k = MulAut.conjNormal (H := K) y k * k⁻¹ := rfl

/-- An element of the kernel of the shift commutes with `y` in `G`. -/
theorem order81_caseB_commute_of_shift_eq_one
    {G : Type*} [Group G] {K : Subgroup G} [K.Normal]
    (hKcomm : ∀ a b : K, a * b = b * a) (y : G) {k : K}
    (hk : order81_caseB_shiftHom hKcomm y k = 1) :
    Commute y k.1 := by
  have h1 : MulAut.conjNormal (H := K) y k * k⁻¹ = 1 := hk
  have h2 : MulAut.conjNormal (H := K) y k = k := by
    have := mul_inv_eq_one.mp h1
    exact this
  have hval : y * k.1 * y⁻¹ = k.1 := congrArg Subtype.val h2
  exact mul_inv_eq_iff_eq_mul.mp hval

/-- Conversely, an element commuting with `y` is in the kernel of the shift. -/
theorem order81_caseB_shift_eq_one_of_commute
    {G : Type*} [Group G] {K : Subgroup G} [K.Normal]
    (hKcomm : ∀ a b : K, a * b = b * a) (y : G) {k : K}
    (hc : Commute y k.1) :
    order81_caseB_shiftHom hKcomm y k = 1 := by
  rw [order81_caseB_shiftHom_apply, mul_inv_eq_one]
  apply Subtype.ext
  change y * k.1 * y⁻¹ = k.1
  rw [hc.eq]
  group

/-- The cube of the outside element lies in the kernel of the shift. -/
theorem order81_caseB_cube_mem_shift_ker
    {G : Type*} [Group G] {K : Subgroup G} [K.Normal]
    (hcard : Nat.card G = 81) (hKcard : Nat.card K = 27)
    (hKcomm : ∀ a b : K, a * b = b * a) (y : G) :
    (⟨y ^ 3, order81_cube_mem_of_normal_subgroup_card_27 hcard hKcard y⟩ : K) ∈
      (order81_caseB_shiftHom hKcomm y).ker := by
  rw [MonoidHom.mem_ker]
  apply order81_caseB_shift_eq_one_of_commute
  exact (Commute.refl y).pow_right 3

/-- If the shift for some outside element is trivial, `G` is abelian. -/
theorem order81_caseB_comm_of_shift_trivial
    {G : Type*} [Group G] {K : Subgroup G} [K.Normal]
    (hcard : Nat.card G = 81) (hKcard : Nat.card K = 27)
    (hKcomm : ∀ a b : K, a * b = b * a) {y : G} (hyK : y ∉ K)
    (htriv : ∀ k : K, order81_caseB_shiftHom hKcomm y k = 1) :
    IsMulCommutative G := by
  have hgk : ∀ k : G, k ∈ K → y * k = k * y := fun k hk =>
    order81_caseB_commute_of_shift_eq_one hKcomm y (htriv ⟨k, hk⟩)
  refine IsMulCommutative.of_comm ?_
  intro a b
  obtain ⟨ka, hka, na, hxa⟩ :=
    order81_normal_layer_exists_mul_zpow_of_not_mem_card_27 hcard hKcard hyK (x := a)
  obtain ⟨kb, hkb, nb, hxb⟩ :=
    order81_normal_layer_exists_mul_zpow_of_not_mem_card_27 hcard hKcard hyK (x := b)
  have hc1 : Commute y kb := hgk kb hkb
  have hc2 : Commute y ka := hgk ka hka
  have hykb : Commute (y ^ na) kb := hc1.zpow_left na
  have hyka : Commute (y ^ nb) ka := hc2.zpow_left nb
  have hkakb : ka * kb = kb * ka := by
    have := hKcomm ⟨ka, hka⟩ ⟨kb, hkb⟩
    exact congrArg Subtype.val this
  have hyy : Commute (y ^ na) (y ^ nb) := (Commute.refl y).zpow_zpow na nb
  rw [hxa, hxb]
  calc ka * y ^ na * (kb * y ^ nb)
      = ka * (y ^ na * kb) * y ^ nb := by group
    _ = ka * (kb * y ^ na) * y ^ nb := by rw [hykb.eq]
    _ = (ka * kb) * (y ^ na * y ^ nb) := by group
    _ = (kb * ka) * (y ^ nb * y ^ na) := by rw [hkakb, hyy.eq]
    _ = kb * (ka * y ^ nb) * y ^ na := by group
    _ = kb * (y ^ nb * ka) * y ^ na := by rw [hyka.eq]
    _ = kb * y ^ nb * (ka * y ^ na) := by group

/-- The kernel of the shift has cardinality `3` or `9` (case-B setting: non-abelian, so
the shift is nontrivial; the cube of `y` provides an order-`3` kernel element). -/
theorem order81_caseB_shift_ker_card
    {G : Type*} [Group G] {K : Subgroup G} [K.Normal]
    (hcard : Nat.card G = 81) (hKcard : Nat.card K = 27)
    (hKcomm : ∀ a b : K, a * b = b * a)
    (hnoncomm : ¬ IsMulCommutative G)
    (hns : ∀ z : G, z ∉ K → z ^ 3 ≠ 1) (h27 : ∀ x : G, orderOf x ≠ 27)
    {y : G} (hyK : y ∉ K) :
    Nat.card (order81_caseB_shiftHom hKcomm y).ker = 3 ∨
      Nat.card (order81_caseB_shiftHom hKcomm y).ker = 9 := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hKcard]; norm_num)
  set D := order81_caseB_shiftHom hKcomm y with hDdef
  have hdvd : Nat.card D.ker ∣ 27 := by
    have h1 := Subgroup.card_subgroup_dvd_card D.ker
    rwa [hKcard] at h1
  have hne27 : Nat.card D.ker ≠ 27 := by
    intro hc27
    apply hnoncomm
    apply order81_caseB_comm_of_shift_trivial hcard hKcard hKcomm hyK
    intro k
    have hker_top : D.ker = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [hc27, hKcard]
    have : k ∈ D.ker := by rw [hker_top]; exact Subgroup.mem_top k
    rwa [MonoidHom.mem_ker] at this
  have hge3 : 3 ≤ Nat.card D.ker := by
    have hy9 : y ^ 9 = 1 := by
      have hord := order81_caseB_orderOf_eq_nine hcard hKcard hns h27 hyK
      exact orderOf_dvd_iff_pow_eq_one.mp (hord ▸ dvd_refl _)
    set k9 : K := ⟨y ^ 3, order81_cube_mem_of_normal_subgroup_card_27 hcard hKcard y⟩
      with hk9def
    have hk9mem : k9 ∈ D.ker :=
      order81_caseB_cube_mem_shift_ker hcard hKcard hKcomm y
    have hk9ne : k9 ≠ 1 := by
      intro h1
      exact hns y hyK (congrArg Subtype.val h1)
    have hk93 : k9 ^ 3 = 1 := by
      apply Subtype.ext
      change (y ^ 3) ^ 3 = 1
      rw [← pow_mul]
      exact hy9
    have hk9ord : orderOf k9 = 3 := orderOf_eq_prime hk93 hk9ne
    have hle : Subgroup.zpowers k9 ≤ D.ker := Subgroup.zpowers_le.mpr hk9mem
    calc (3 : ℕ) = Nat.card (Subgroup.zpowers k9) := by rw [Nat.card_zpowers, hk9ord]
      _ ≤ Nat.card D.ker := Subgroup.card_le_of_le hle
  have h27' : (27 : ℕ) = 3 ^ 3 := by norm_num
  rw [h27'] at hdvd
  rcases (Nat.dvd_prime_pow Nat.prime_three).mp hdvd with ⟨k, hk3, hk⟩
  interval_cases k
  · exfalso
    rw [hk] at hge3
    norm_num at hge3
  · left
    simpa using hk
  · right
    simpa using hk
  · exfalso
    apply hne27
    rw [hk]
    norm_num

/-- Every element of `C_9 × C_3` has ninth power `1`. -/
theorem order81_C9C3_pow_nine (x : order81_C9C3) : x ^ 9 = 1 := by
  fin_cases x <;> decide +kernel

/-- `C_9 × C_3` has exactly `8` nontrivial elements of order dividing `3`. -/
theorem order81_C9C3_torsion_ne_one_card :
    Nat.card {x : order81_C9C3 // x ^ 3 = 1 ∧ x ≠ 1} = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- Transport of the punctured `3`-torsion count to a kernel isomorphic to `C_9 × C_3`. -/
theorem order81_caseB_torsion_ne_one_card
    {K : Type*} [Group K] (e : K ≃* order81_C9C3) :
    Nat.card {k : K // k ^ 3 = 1 ∧ k ≠ 1} = 8 := by
  rw [← order81_C9C3_torsion_ne_one_card]
  apply Nat.card_congr
  exact
    { toFun := fun k => ⟨e k.1, by
        rw [← map_pow, k.2.1, map_one]
        exact ⟨rfl, fun h1 => k.2.2 (by
          have := congrArg e.symm h1
          simpa using this)⟩⟩
      invFun := fun x => ⟨e.symm x.1, by
        constructor
        · rw [← map_pow]
          have := congrArg e.symm x.2.1
          simpa using this
        · intro h1
          apply x.2.2
          have := congrArg e h1
          simpa using this⟩
      left_inv := fun k => by simp
      right_inv := fun x => by simp }

/-- Any element of a kernel isomorphic to `C_9 × C_3` has ninth power `1`. -/
theorem order81_caseB_pow_nine
    {K : Type*} [Group K] (e : K ≃* order81_C9C3) (k : K) : k ^ 9 = 1 := by
  apply e.injective
  rw [map_pow, order81_C9C3_pow_nine, map_one]

/-- In the case-B setting, when the inverse cube of `y` lies in the range of the shift,
some preimage `B` has order `9` in `K` and conjugates `y` to `y ^ 4`. -/
theorem order81_caseB_exists_conjugator
    {G : Type*} [Group G] {K : Subgroup G} [K.Normal]
    (hcard : Nat.card G = 81) (hKcard : Nat.card K = 27)
    (e : K ≃* order81_C9C3)
    (hKcomm : ∀ a b : K, a * b = b * a)
    (hns : ∀ z : G, z ∉ K → z ^ 3 ≠ 1)
    {y : G} (hyK : y ∉ K)
    (hker9 : Nat.card (order81_caseB_shiftHom hKcomm y).ker = 9)
    (hmem : (⟨y ^ 3, order81_cube_mem_of_normal_subgroup_card_27 hcard hKcard y⟩ : K)⁻¹ ∈
      (order81_caseB_shiftHom hKcomm y).range) :
    ∃ B : K, orderOf B = 9 ∧
      order81_caseB_shiftHom hKcomm y B =
        (⟨y ^ 3, order81_cube_mem_of_normal_subgroup_card_27 hcard hKcard y⟩ : K)⁻¹ ∧
      B.1 * y * B.1⁻¹ = y ^ 4 := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  set D := order81_caseB_shiftHom hKcomm y with hDdef
  set k9 : K := ⟨y ^ 3, order81_cube_mem_of_normal_subgroup_card_27 hcard hKcard y⟩
    with hk9def
  obtain ⟨m₀, hm₀⟩ := hmem
  -- find an order-9 element in the preimage coset `m₀ * ker D`
  have hexists : ∃ z ∈ D.ker, (m₀ * z) ^ 3 ≠ 1 := by
    by_contra hnone
    push Not at hnone
    -- then `z ↦ m₀ * z` injects `ker D` into the 8-element punctured torsion
    have hinj : Function.Injective (fun z : D.ker =>
        (⟨m₀ * z.1, hnone z.1 z.2, by
          intro h1
          have hz : (z : K) = m₀⁻¹ := by
            have := congrArg (fun w => m₀⁻¹ * w) h1
            simpa [mul_assoc] using this
          have hzker := z.2
          rw [hz] at hzker
          have hDm₀inv : D m₀⁻¹ = k9 := by
            rw [map_inv, hm₀]
            simp
          rw [MonoidHom.mem_ker, hDm₀inv] at hzker
          apply hns y hyK
          have := congrArg Subtype.val hzker
          simpa [hk9def] using this⟩ :
          {k : K // k ^ 3 = 1 ∧ k ≠ 1})) := by
      intro z w hzw
      have := congrArg Subtype.val hzw
      simp only at this
      exact Subtype.ext (mul_left_cancel this)
    have hcard_le := Nat.card_le_card_of_injective _ hinj
    rw [hker9, order81_caseB_torsion_ne_one_card e] at hcard_le
    omega
  obtain ⟨z, hzker, hz3⟩ := hexists
  set B : K := m₀ * z with hBdef
  have hDB : D B = k9⁻¹ := by
    rw [hBdef, map_mul, hm₀, MonoidHom.mem_ker.mp hzker, mul_one]
  have hBord : orderOf B = 9 := by
    have hB9 : B ^ 9 = 1 := order81_caseB_pow_nine e B
    have hdvd : orderOf B ∣ 9 := orderOf_dvd_iff_pow_eq_one.mpr hB9
    have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
    rw [h9] at hdvd
    rcases (Nat.dvd_prime_pow Nat.prime_three).mp hdvd with ⟨j, hj2, hj⟩
    interval_cases j
    · exfalso
      apply hz3
      have hB1 : B = 1 := orderOf_eq_one_iff.mp (by simpa using hj)
      rw [hB1]
      simp
    · exfalso
      apply hz3
      have hB3 : orderOf B = 3 := by simpa using hj
      have hpow := pow_orderOf_eq_one B
      rwa [hB3] at hpow
    · simpa using hj
  refine ⟨B, hBord, hDB, ?_⟩
  -- from `D B = k9⁻¹`: `y B y⁻¹ = y⁻³ B` in `G`, hence `B y B⁻¹ = y⁴`
  have hσB : MulAut.conjNormal (H := K) y B = k9⁻¹ * B := by
    have h1 : MulAut.conjNormal (H := K) y B * B⁻¹ = k9⁻¹ := hDB
    have := congrArg (· * B) h1
    simpa [mul_assoc] using this
  have hval : y * B.1 * y⁻¹ = (y ^ 3)⁻¹ * B.1 := by
    have := congrArg Subtype.val hσB
    simpa [hk9def] using this
  -- rearrange in `G`
  have hyB : y * B.1 = (y ^ 3)⁻¹ * B.1 * y := by
    have := congrArg (· * y) hval
    simpa [mul_assoc] using this
  have hinv : y * B.1⁻¹ * y⁻¹ = B.1⁻¹ * y ^ 3 := by
    have h2 := congrArg (·⁻¹) hval
    simp only [mul_inv_rev, inv_inv] at h2
    calc y * B.1⁻¹ * y⁻¹ = y * (B.1⁻¹ * y⁻¹) := by group
      _ = B.1⁻¹ * y ^ 3 := by
          rw [← mul_assoc] at h2 ⊢
          exact h2
  calc B.1 * y * B.1⁻¹
      = B.1 * (y * B.1⁻¹ * y⁻¹) * y := by group
    _ = B.1 * (B.1⁻¹ * y ^ 3) * y := by rw [hinv]
    _ = y ^ 4 := by group

/-- The cube of `y` is not a power of the conjugator `B` (else adjusting `y` by a power
of `B` would produce an outside element of order `3`, contradicting non-splitness). -/
theorem order81_caseB_cube_not_mem_zpowers_conjugator
    {G : Type*} [Group G] {K : Subgroup G} [K.Normal]
    (hcard : Nat.card G = 81) (hKcard : Nat.card K = 27)
    (hKcomm : ∀ a b : K, a * b = b * a)
    (hns : ∀ z : G, z ∉ K → z ^ 3 ≠ 1)
    {y : G} (hyK : y ∉ K) (hy9 : y ^ 9 = 1) {B : K} (hBord : orderOf B = 9)
    (hDB : order81_caseB_shiftHom hKcomm y B =
      (⟨y ^ 3, order81_cube_mem_of_normal_subgroup_card_27 hcard hKcard y⟩ : K)⁻¹) :
    (⟨y ^ 3, order81_cube_mem_of_normal_subgroup_card_27 hcard hKcard y⟩ : K) ∉
      Subgroup.zpowers B := by
  set k9 : K := ⟨y ^ 3, order81_cube_mem_of_normal_subgroup_card_27 hcard hKcard y⟩
    with hk9def
  intro hmem
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
  -- `3 ∣ m` since `k9` has order dividing 3 and `B` has order 9
  have hk93 : k9 ^ 3 = 1 := by
    apply Subtype.ext
    change (y ^ 3) ^ 3 = 1
    rw [← pow_mul]
    exact hy9
  obtain ⟨j, hj⟩ : ∃ j : ℤ, m = 3 * j := by
    have h3m : B ^ (m * 3) = 1 := by
      rw [zpow_mul]
      have h1 : (B ^ m) ^ (3 : ℤ) = k9 ^ (3 : ℤ) := by rw [hm]
      rw [h1]
      have h2 : k9 ^ (3 : ℤ) = k9 ^ (3 : ℕ) := by norm_cast
      rw [h2, hk93]
    have hdvd9 : ((9 : ℕ) : ℤ) ∣ m * 3 := by
      have := orderOf_dvd_iff_zpow_eq_one.mpr h3m
      rwa [hBord] at this
    obtain ⟨t, ht⟩ := hdvd9
    refine ⟨t, ?_⟩
    have : m * 3 = 9 * t := by exact_mod_cast ht
    linarith
  -- commutation of `y ^ 3` with `B` inside the abelian kernel
  have hy3B : Commute (y ^ 3) B.1 := by
    have := hKcomm k9 B
    have hval := congrArg Subtype.val this
    exact hval
  -- conjugation formulas
  have hσB : y * B.1 * y⁻¹ = (y ^ 3)⁻¹ * B.1 := by
    have h1 : MulAut.conjNormal (H := K) y B * B⁻¹ = k9⁻¹ := hDB
    have h2 : MulAut.conjNormal (H := K) y B = k9⁻¹ * B := by
      have := congrArg (· * B) h1
      simpa [mul_assoc] using this
    have := congrArg Subtype.val h2
    simpa [hk9def] using this
  have hinvB : y⁻¹ * B.1 * y = y ^ 3 * B.1 := by
    have h7 : B.1 = (y ^ 3)⁻¹ * (y⁻¹ * B.1 * y) := by
      calc B.1 = y⁻¹ * (y * B.1 * y⁻¹) * y := by group
        _ = y⁻¹ * ((y ^ 3)⁻¹ * B.1) * y := by rw [hσB]
        _ = (y ^ 3)⁻¹ * (y⁻¹ * B.1 * y) := by group
    calc y⁻¹ * B.1 * y = y ^ 3 * ((y ^ 3)⁻¹ * (y⁻¹ * B.1 * y)) := by group
      _ = y ^ 3 * B.1 := by rw [← h7]
  -- the adjusted element and its cube
  set c : G := B.1 ^ (-j) with hcdef
  have hcK : c ∈ K := by
    rw [hcdef]
    exact K.zpow_mem B.2 (-j)
  have hyc_out : y * c ∉ K := by
    intro hmem2
    apply hyK
    have hy_eq : y = (y * c) * c⁻¹ := by group
    rw [hy_eq]
    exact K.mul_mem hmem2 (K.inv_mem hcK)
  apply hns (y * c) hyc_out
  have h1conj : y⁻¹ * c * y = (y ^ 3) ^ (-j) * c := by
    rw [hcdef]
    calc y⁻¹ * B.1 ^ (-j) * y = y⁻¹ * B.1 ^ (-j) * y⁻¹⁻¹ := by rw [inv_inv]
      _ = (y⁻¹ * B.1 * y⁻¹⁻¹) ^ (-j) := conj_zpow.symm
      _ = (y ^ 3 * B.1) ^ (-j) := by rw [inv_inv, hinvB]
      _ = (y ^ 3) ^ (-j) * B.1 ^ (-j) := hy3B.mul_zpow (-j)
  have hcy3 : ∀ n : ℤ, Commute ((y ^ 3) ^ n) c := by
    intro n
    rw [hcdef]
    exact (hy3B.zpow_zpow n (-j))
  have h2conj : y⁻¹ * (y⁻¹ * c * y) * y = (y ^ 3) ^ (-2 * j) * c := by
    rw [h1conj]
    have hyp : Commute y⁻¹ ((y ^ 3) ^ (-j)) := by
      have : Commute y (y ^ 3) := (Commute.refl y).pow_right 3
      exact (this.zpow_right (-j)).inv_left
    calc y⁻¹ * ((y ^ 3) ^ (-j) * c) * y
        = (y ^ 3) ^ (-j) * (y⁻¹ * c * y) := by
          rw [← mul_assoc, hyp.eq]
          group
      _ = (y ^ 3) ^ (-j) * ((y ^ 3) ^ (-j) * c) := by rw [h1conj]
      _ = (y ^ 3) ^ (-2 * j) * c := by
          rw [← mul_assoc, ← zpow_add]
          congr 2
          ring
  have hcube : (y * c) ^ 3 = 1 := by
    have hexpand : (y * c) ^ 3 = y ^ 3 * (y⁻¹ * (y⁻¹ * c * y) * y) * (y⁻¹ * c * y) * c := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, sq]
      group
    rw [hexpand, h2conj, h1conj]
    -- y³ * ((y³)^(-2j) c) * ((y³)^(-j) c) * c = y³ * (y³)^(-3j) * c³ = y³ * (y³)⁻¹-story
    have hc3 : c * c * c = (y ^ 3)⁻¹ := by
      rw [hcdef, ← zpow_add, ← zpow_add]
      have hsum : -j + -j + -j = -m := by rw [hj]; ring
      rw [hsum]
      have : B.1 ^ (-m) = (B ^ (-m) : K).1 := by
        simp [SubgroupClass.coe_zpow]
      rw [this]
      have hBm : (B ^ (-m) : K) = k9⁻¹ := by
        rw [zpow_neg, hm]
      rw [hBm]
      simp [hk9def]
    calc y ^ 3 * ((y ^ 3) ^ (-2 * j) * c) * ((y ^ 3) ^ (-j) * c) * c
        = y ^ 3 * (y ^ 3) ^ (-2 * j) * (c * ((y ^ 3) ^ (-j))) * (c * c) := by group
      _ = y ^ 3 * (y ^ 3) ^ (-2 * j) * ((y ^ 3) ^ (-j) * c) * (c * c) := by
          rw [(hcy3 (-j)).symm.eq]
      _ = y ^ 3 * ((y ^ 3) ^ (-2 * j) * (y ^ 3) ^ (-j)) * (c * c * c) := by group
      _ = y ^ 3 * (y ^ 3) ^ (-3 * j) * (y ^ 3)⁻¹ := by
          rw [hc3, ← zpow_add]
          congr 3
          ring
      _ = 1 := by
          have h93 : ((y : G) ^ 3) ^ (-3 * j) = (y ^ 9) ^ (-j) := by
            rw [show (-3 : ℤ) * j = (3 : ℤ) * (-j) by ring, zpow_mul]
            congr 1
            rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, ← pow_mul]
          rw [h93, hy9, one_zpow, mul_one, mul_inv_cancel]
  exact hcube

/-! ### The `B1a` lift: from a conjugator to `C_9 ⋊ C_9` -/

/-- Every element of `C_9` is a power of the standard generator. -/
theorem order81_caseB_cyclicRep9_ofAdd_eq_gen_pow (n : ZMod 9) :
    Multiplicative.ofAdd n = (Multiplicative.ofAdd (1 : ZMod 9)) ^ n.val := by
  calc
    Multiplicative.ofAdd n = Multiplicative.ofAdd ((n.val : ZMod 9)) := by
      rw [ZMod.natCast_zmod_val]
    _ = Multiplicative.ofAdd (n.val • (1 : ZMod 9)) := by simp
    _ = (Multiplicative.ofAdd (1 : ZMod 9)) ^ n.val := by rw [ofAdd_nsmul]

/-- A homomorphism from `C_9` is determined by the image of the standard generator. -/
theorem order81_caseB_cyclicRep9_hom_ext {M : Type*} [Monoid M]
    {φ ψ : CyclicRep 9 →* M}
    (hgen : φ (Multiplicative.ofAdd (1 : ZMod 9)) =
      ψ (Multiplicative.ofAdd (1 : ZMod 9))) :
    φ = ψ := by
  apply MonoidHom.ext
  intro x
  have hx : x = (Multiplicative.ofAdd (1 : ZMod 9)) ^ (Multiplicative.toAdd x).val := by
    conv_lhs => rw [← ofAdd_toAdd x]
    exact order81_caseB_cyclicRep9_ofAdd_eq_gen_pow _
  rw [hx, map_pow, map_pow, hgen]

/-- If the kernel contains an order-`9` element `x` with `y³ ∉ ⟨x⟩`, then any subgroup
containing `x` and the outside element `y` is all of `G`: the pair `(x, y³)` generates
the kernel (their spans intersect trivially, so counting gives all `27` elements), and
`y` supplies the missing index-`3` layer. -/
theorem order81_caseB_eq_top_of_kernel_gen
    {G : Type*} [Group G] {K : Subgroup G} [K.Normal]
    (hcard : Nat.card G = 81) (hKcard : Nat.card K = 27)
    (hKcomm : ∀ a b : K, a * b = b * a)
    (hns : ∀ z : G, z ∉ K → z ^ 3 ≠ 1)
    {y : G} (hyK : y ∉ K) (hy9 : y ^ 9 = 1)
    {x : K} (hxord : orderOf x = 9)
    (hnotmem : (⟨y ^ 3, order81_cube_mem_of_normal_subgroup_card_27 hcard hKcard y⟩ : K) ∉
      Subgroup.zpowers x)
    {R : Subgroup G} (hxR : (x : G) ∈ R) (hyR : y ∈ R) :
    R = ⊤ := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set k9 : K := ⟨y ^ 3, order81_cube_mem_of_normal_subgroup_card_27 hcard hKcard y⟩
    with hk9def
  have hx9K : x ^ 9 = 1 := by
    rw [← hxord]
    exact pow_orderOf_eq_one x
  have hk93 : k9 ^ 3 = 1 := by
    apply Subtype.ext
    change (y ^ 3) ^ 3 = 1
    rw [← pow_mul]
    exact hy9
  have hk9ne : k9 ≠ 1 := by
    intro h
    apply hns y hyK
    have := congrArg Subtype.val h
    simpa [hk9def] using this
  have hk9ord : orderOf k9 = 3 := orderOf_eq_prime hk93 hk9ne
  have hk9R : (k9 : G) ∈ R := by
    have hk9y : (k9 : G) = y ^ 3 := rfl
    rw [hk9y]
    exact R.pow_mem hyR 3
  -- `⟨x⟩` and `⟨k9⟩` intersect trivially inside the kernel
  have hinter : ∀ z : K, z ∈ Subgroup.zpowers x → z ∈ Subgroup.zpowers k9 → z = 1 := by
    intro z hzx hzk9
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hzk9
    have hk93z : k9 ^ (3 : ℤ) = 1 := by exact_mod_cast hk93
    have hxr : k9 ^ (j % 3) = z := by
      have hsplit : j = 3 * (j / 3) + j % 3 := by omega
      calc k9 ^ (j % 3) = (k9 ^ (3 : ℤ)) ^ (j / 3) * k9 ^ (j % 3) := by
            rw [hk93z, one_zpow, one_mul]
        _ = k9 ^ (3 * (j / 3) + j % 3) := by rw [← zpow_mul, ← zpow_add]
        _ = k9 ^ j := by rw [← hsplit]
        _ = z := hj
    have hcases : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases hcases with h | h | h <;> rw [h] at hxr
    · rw [← hxr, zpow_zero]
    · exfalso
      apply hnotmem
      rw [zpow_one] at hxr
      rw [hxr]
      exact hzx
    · exfalso
      apply hnotmem
      have h4 : z * z = k9 := by
        rw [← hxr]
        calc k9 ^ (2 : ℤ) * k9 ^ (2 : ℤ) = k9 ^ ((2 : ℤ) + 2) := (zpow_add _ _ _).symm
          _ = k9 ^ ((3 : ℤ) + 1) := by norm_num
          _ = k9 ^ (3 : ℤ) * k9 ^ (1 : ℤ) := zpow_add _ _ _
          _ = k9 := by rw [hk93z, one_mul, zpow_one]
      rw [← h4]
      exact mul_mem hzx hzx
  -- `x` and `k9` generate the kernel: the multiplication map from `C_9 × C_3` is bijective
  have hcommxk : ∀ (m : Multiplicative (ZMod 9)) (n : Multiplicative (ZMod 3)),
      Commute (zmodZPowHom 9 x hx9K m) (zmodZPowHom 3 k9 hk93 n) := fun m n => hKcomm _ _
  set ψ : Multiplicative (ZMod 9) × Multiplicative (ZMod 3) →* K :=
    (zmodZPowHom 9 x hx9K).noncommCoprod (zmodZPowHom 3 k9 hk93) hcommxk with hψdef
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨m, n⟩ hmn
    rw [hψdef, MonoidHom.noncommCoprod_apply] at hmn
    have hfmx : zmodZPowHom 9 x hx9K m ∈ Subgroup.zpowers x :=
      zmodZPowHom_mem_zpowers 9 x hx9K m
    have hgnk : zmodZPowHom 3 k9 hk93 n ∈ Subgroup.zpowers k9 :=
      zmodZPowHom_mem_zpowers 3 k9 hk93 n
    have hfmk : zmodZPowHom 9 x hx9K m ∈ Subgroup.zpowers k9 := by
      have heq : zmodZPowHom 9 x hx9K m = (zmodZPowHom 3 k9 hk93 n)⁻¹ :=
        eq_inv_of_mul_eq_one_left hmn
      rw [heq]
      exact inv_mem hgnk
    have hfm1 : zmodZPowHom 9 x hx9K m = 1 := hinter _ hfmx hfmk
    have hgn1 : zmodZPowHom 3 k9 hk93 n = 1 := by
      rw [hfm1, one_mul] at hmn
      exact hmn
    have hm : m = 1 := by
      apply zmodZPowHom_injective 9 x hx9K hxord
      rw [hfm1, map_one]
    have hn : n = 1 := by
      apply zmodZPowHom_injective 3 k9 hk93 hk9ord
      rw [hgn1, map_one]
    rw [hm, hn]
    exact Prod.mk_one_one
  have hψbij : Function.Bijective ψ :=
    (Nat.bijective_iff_injective_and_card ψ).mpr ⟨hψinj, by
      rw [hKcard]
      exact card_order81_C9C3⟩
  -- hence the whole kernel lies in `R`
  have hKle : K ≤ R := by
    intro g hg
    obtain ⟨⟨m, n⟩, hmn⟩ := hψbij.surjective ⟨g, hg⟩
    have hfmx := zmodZPowHom_mem_zpowers 9 x hx9K m
    have hgnk := zmodZPowHom_mem_zpowers 3 k9 hk93 n
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hfmx
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hgnk
    have hg_eq : (⟨g, hg⟩ : K) = x ^ i * k9 ^ j := by
      rw [← hmn, hψdef, MonoidHom.noncommCoprod_apply, ← hi, ← hj]
    have hval : g = (x : G) ^ i * (k9 : G) ^ j := by
      have := congrArg Subtype.val hg_eq
      simpa [SubgroupClass.coe_zpow] using this
    rw [hval]
    exact mul_mem (R.zpow_mem hxR i) (R.zpow_mem hk9R j)
  -- `R` contains the kernel and an outside element, so it is everything
  have hdvd27 : (27 : ℕ) ∣ Nat.card R := by
    rw [← hKcard]
    exact Subgroup.card_dvd_of_le hKle
  have hdvd81 : Nat.card R ∣ 81 := by
    rw [← hcard]
    exact Subgroup.card_subgroup_dvd_card _
  have h81 : (81 : ℕ) = 3 ^ 4 := by norm_num
  rw [h81] at hdvd81
  rcases (Nat.dvd_prime_pow Nat.prime_three).mp hdvd81 with ⟨t, ht4, hteq⟩
  interval_cases t
  · rw [hteq] at hdvd27; norm_num at hdvd27
  · rw [hteq] at hdvd27; norm_num at hdvd27
  · rw [hteq] at hdvd27; norm_num at hdvd27
  · -- `|R| = 27` would force `R = K`, contradicting `y ∈ R \ K`
    exfalso
    have hKeq : K = R := by
      apply Subgroup.eq_of_le_of_card_ge hKle
      rw [hteq, hKcard]
      norm_num
    exact hyK (hKeq ▸ hyR)
  · apply Subgroup.eq_top_of_card_eq
    rw [hteq, hcard]
    norm_num

/-- Two elements `a, b` of a group of order `81` with `a⁹ = b⁹ = 1`, the `C_9 ⋊ C_9`
defining relation `b a b⁻¹ = a⁴`, and jointly generating the group determine an
isomorphism `G ≃* C_9 ⋊ C_9`. -/
theorem order81_caseB_c9c9_of_relation
    {G : Type*} [Group G] (hcard : Nat.card G = 81)
    {a b : G} (ha9 : a ^ 9 = 1) (hb9 : b ^ 9 = 1) (hrel : b * a * b⁻¹ = a ^ 4)
    (htop : ∀ R : Subgroup G, a ∈ R → b ∈ R → R = ⊤) :
    Nonempty (G ≃* order81_c9_semidirect_c9_rep) := by
  -- the two generator homomorphisms into `G`
  set fn := zmodZPowHom 9 a ha9 with hfndef
  set fg := zmodZPowHom 9 b hb9 with hfgdef
  have hfn1 : fn (Multiplicative.ofAdd (1 : ZMod 9)) = a := by
    have h := zmodZPowHom_intCast 9 a ha9 1
    simpa using h
  have hfg1 : fg (Multiplicative.ofAdd (1 : ZMod 9)) = b := by
    have h := zmodZPowHom_intCast 9 b hb9 1
    simpa using h
  have hfn4 : fn (Multiplicative.ofAdd (4 : ZMod 9)) = a ^ 4 := by
    have h := zmodZPowHom_intCast 9 a ha9 4
    exact_mod_cast h
  -- compatibility of the two generator maps with the `C_9`-action, at the generator
  have hφ1 : order81_c9Action (Multiplicative.ofAdd (1 : ZMod 9))
      (Multiplicative.ofAdd (1 : ZMod 9)) = Multiplicative.ofAdd (4 : ZMod 9) := by
    rw [order81_c9Action_gen, unitAutHom_apply, ZMod.coe_unitOfCoprime, mul_one]
    norm_num
  have hbase : fn.comp
        (order81_c9Action (Multiplicative.ofAdd (1 : ZMod 9))).toMonoidHom =
      (MulAut.conj (fg (Multiplicative.ofAdd (1 : ZMod 9)))).toMonoidHom.comp fn := by
    apply order81_caseB_cyclicRep9_hom_ext
    change fn (order81_c9Action (Multiplicative.ofAdd (1 : ZMod 9))
        (Multiplicative.ofAdd (1 : ZMod 9))) =
      MulAut.conj (fg (Multiplicative.ofAdd (1 : ZMod 9)))
        (fn (Multiplicative.ofAdd (1 : ZMod 9)))
    rw [hφ1, hfn4, hfg1, hfn1, MulAut.conj_apply, hrel]
  -- the compatibility condition is multiplicative in the acting element
  have hmul : ∀ g₁ g₂ : order81_C9,
      fn.comp (order81_c9Action g₁).toMonoidHom =
        (MulAut.conj (fg g₁)).toMonoidHom.comp fn →
      fn.comp (order81_c9Action g₂).toMonoidHom =
        (MulAut.conj (fg g₂)).toMonoidHom.comp fn →
      fn.comp (order81_c9Action (g₁ * g₂)).toMonoidHom =
        (MulAut.conj (fg (g₁ * g₂))).toMonoidHom.comp fn := by
    intro g₁ g₂ h₁ h₂
    apply MonoidHom.ext
    intro x
    change fn (order81_c9Action (g₁ * g₂) x) = MulAut.conj (fg (g₁ * g₂)) (fn x)
    rw [map_mul order81_c9Action g₁ g₂, map_mul fg g₁ g₂,
      map_mul (MulAut.conj (G := G)) (fg g₁) (fg g₂), MulAut.mul_apply, MulAut.mul_apply]
    have h₁' : fn (order81_c9Action g₁ (order81_c9Action g₂ x)) =
        MulAut.conj (fg g₁) (fn (order81_c9Action g₂ x)) :=
      DFunLike.congr_fun h₁ (order81_c9Action g₂ x)
    have h₂' : fn (order81_c9Action g₂ x) = MulAut.conj (fg g₂) (fn x) :=
      DFunLike.congr_fun h₂ x
    rw [h₁', h₂']
  have hcompat : ∀ g : order81_C9,
      fn.comp (order81_c9Action g).toMonoidHom =
        (MulAut.conj (fg g)).toMonoidHom.comp fn := by
    intro g
    have hg : g = (Multiplicative.ofAdd (1 : ZMod 9)) ^ (Multiplicative.toAdd g).val := by
      conv_lhs => rw [← ofAdd_toAdd g]
      exact order81_caseB_cyclicRep9_ofAdd_eq_gen_pow _
    rw [hg]
    generalize (Multiplicative.toAdd g).val = v
    induction v with
    | zero =>
      apply MonoidHom.ext
      intro x
      change fn (order81_c9Action ((Multiplicative.ofAdd (1 : ZMod 9)) ^ 0) x) =
        MulAut.conj (fg ((Multiplicative.ofAdd (1 : ZMod 9)) ^ 0)) (fn x)
      rw [pow_zero, map_one, map_one]
      simp
    | succ n ih =>
      rw [pow_succ]
      exact hmul _ _ ih hbase
  -- the lifted homomorphism out of the split extension
  set F : order81_c9_semidirect_c9_rep →* G := SemidirectProduct.lift fn fg hcompat
    with hFdef
  have haR : a ∈ F.range := by
    refine ⟨SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 9)), ?_⟩
    rw [hFdef, SemidirectProduct.lift_inl]
    exact hfn1
  have hbR : b ∈ F.range := by
    refine ⟨SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 9)), ?_⟩
    rw [hFdef, SemidirectProduct.lift_inr]
    exact hfg1
  have hrange : F.range = ⊤ := htop F.range haR hbR
  have hsurj : Function.Surjective F := MonoidHom.range_eq_top.mp hrange
  haveI : Finite order81_c9_semidirect_c9_rep :=
    Nat.finite_of_card_ne_zero (by rw [card_order81_c9_semidirect_c9_rep]; norm_num)
  have hbij : Function.Bijective F :=
    (Nat.bijective_iff_surjective_and_card F).mpr ⟨hsurj, by
      rw [card_order81_c9_semidirect_c9_rep, hcard]⟩
  exact ⟨(MulEquiv.ofBijective F hbij).symm⟩

/-- **Case B1a.** In the case-B setting, an order-`9` conjugator `B` in the kernel with
`B y B⁻¹ = y ^ 4` and `D B = (y³)⁻¹` produces an isomorphism `G ≃* C_9 ⋊ C_9`: the two
generators `y` and `B` satisfy exactly the defining relations of the split extension. -/
theorem order81_caseB_c9c9_of_conjugator
    {G : Type*} [Group G] {K : Subgroup G} [K.Normal]
    (hcard : Nat.card G = 81) (hKcard : Nat.card K = 27)
    (e : K ≃* order81_C9C3)
    (hKcomm : ∀ a b : K, a * b = b * a)
    (hns : ∀ z : G, z ∉ K → z ^ 3 ≠ 1)
    {y : G} (hyK : y ∉ K) (hy9 : y ^ 9 = 1)
    {B : K} (hBord : orderOf B = 9) (hconj : B.1 * y * B.1⁻¹ = y ^ 4)
    (hDB : order81_caseB_shiftHom hKcomm y B =
      (⟨y ^ 3, order81_cube_mem_of_normal_subgroup_card_27 hcard hKcard y⟩ : K)⁻¹) :
    Nonempty (G ≃* order81_c9_semidirect_c9_rep) := by
  have hnotmem : (⟨y ^ 3, order81_cube_mem_of_normal_subgroup_card_27 hcard hKcard y⟩ : K) ∉
      Subgroup.zpowers B :=
    order81_caseB_cube_not_mem_zpowers_conjugator hcard hKcard hKcomm hns hyK hy9 hBord hDB
  have hB9K : B ^ 9 = 1 := order81_caseB_pow_nine e B
  have hB9G : (B : G) ^ 9 = 1 := by
    have := congrArg Subtype.val hB9K
    simpa using this
  exact order81_caseB_c9c9_of_relation hcard hy9 hB9G hconj
    (fun R hyR hBR => order81_caseB_eq_top_of_kernel_gen hcard hKcard hKcomm hns hyK hy9
      hBord hnotmem hBR hyR)

/-- In the case-B setting, if `x ∈ K` has order `9` and `y x y⁻¹ = x ^ 4`, then
`y³ ∉ ⟨x⟩`: otherwise `y³ = x^(3j)` and `y·x^(−j)` would be an outside element of
order `3`, contradicting non-splitness. -/
theorem order81_caseB_cube_not_mem_zpowers_eigenvector
    {G : Type*} [Group G] {K : Subgroup G} [K.Normal]
    (hcard : Nat.card G = 81) (hKcard : Nat.card K = 27)
    (hns : ∀ z : G, z ∉ K → z ^ 3 ≠ 1)
    {y : G} (hyK : y ∉ K) (hy9 : y ^ 9 = 1)
    {x : K} (hxord : orderOf x = 9) (hconj : y * x.1 * y⁻¹ = x.1 ^ 4) :
    (⟨y ^ 3, order81_cube_mem_of_normal_subgroup_card_27 hcard hKcard y⟩ : K) ∉
      Subgroup.zpowers x := by
  set k9 : K := ⟨y ^ 3, order81_cube_mem_of_normal_subgroup_card_27 hcard hKcard y⟩
    with hk9def
  intro hmem
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hx9K : x ^ 9 = 1 := by
    rw [← hxord]
    exact pow_orderOf_eq_one x
  have hx9G : (x : G) ^ 9 = 1 := by
    have := congrArg Subtype.val hx9K
    simpa using this
  have hx9z : (x : G) ^ (9 : ℤ) = 1 := by exact_mod_cast hx9G
  have hk93 : k9 ^ 3 = 1 := by
    apply Subtype.ext
    change (y ^ 3) ^ 3 = 1
    rw [← pow_mul]
    exact hy9
  -- `3 ∣ m` since `k9` has order dividing `3` and `x` has order `9`
  obtain ⟨j, hj⟩ : ∃ j : ℤ, m = 3 * j := by
    have h3m : x ^ (m * 3) = 1 := by
      rw [zpow_mul]
      have h1 : (x ^ m) ^ (3 : ℤ) = k9 ^ (3 : ℤ) := by rw [hm]
      rw [h1]
      have h2 : k9 ^ (3 : ℤ) = k9 ^ (3 : ℕ) := by norm_cast
      rw [h2, hk93]
    have hdvd9 : ((9 : ℕ) : ℤ) ∣ m * 3 := by
      have := orderOf_dvd_iff_zpow_eq_one.mpr h3m
      rwa [hxord] at this
    obtain ⟨t, ht⟩ := hdvd9
    refine ⟨t, ?_⟩
    have : m * 3 = 9 * t := by exact_mod_cast ht
    linarith
  -- value-level form of the membership
  have hmG : (x : G) ^ m = y ^ 3 := by
    have := congrArg Subtype.val hm
    simpa [SubgroupClass.coe_zpow, hk9def] using this
  -- the inverse conjugation relation `y⁻¹ x y = x⁷`
  have hu9 : (y⁻¹ * (x : G) * y) ^ 9 = 1 := by
    calc (y⁻¹ * (x : G) * y) ^ 9
        = (y⁻¹ * (x : G) * y⁻¹⁻¹) ^ 9 := by rw [inv_inv]
      _ = y⁻¹ * (x : G) ^ 9 * y⁻¹⁻¹ := conj_pow
      _ = 1 := by rw [hx9G, inv_inv, mul_one, inv_mul_cancel]
  have hXu4 : (x : G) = (y⁻¹ * (x : G) * y) ^ 4 := by
    calc (x : G) = y⁻¹ * (y * (x : G) * y⁻¹) * y := by group
      _ = y⁻¹ * (x : G) ^ 4 * y := by rw [hconj]
      _ = y⁻¹ * (x : G) ^ 4 * y⁻¹⁻¹ := by rw [inv_inv]
      _ = (y⁻¹ * (x : G) * y⁻¹⁻¹) ^ 4 := conj_pow.symm
      _ = (y⁻¹ * (x : G) * y) ^ 4 := by rw [inv_inv]
  have hinv : y⁻¹ * (x : G) * y = (x : G) ^ 7 := by
    have h28 : ((y⁻¹ * (x : G) * y) ^ 4) ^ 7 = y⁻¹ * (x : G) * y := by
      have hsplit : (y⁻¹ * (x : G) * y) ^ (4 * 7) =
          ((y⁻¹ * (x : G) * y) ^ 9) ^ 3 * (y⁻¹ * (x : G) * y) := by
        rw [← pow_mul, ← pow_succ]
      rw [← pow_mul, hsplit, hu9, one_pow, one_mul]
    calc y⁻¹ * (x : G) * y = ((y⁻¹ * (x : G) * y) ^ 4) ^ 7 := h28.symm
      _ = (x : G) ^ 7 := by rw [← hXu4]
  -- the adjusted element `y · x^(−j)` and its cube
  set c : G := (x : G) ^ (-j) with hcdef
  have hcK : c ∈ K := by
    rw [hcdef]
    exact K.zpow_mem x.2 (-j)
  have hyc_out : y * c ∉ K := by
    intro hmem2
    apply hyK
    have hy_eq : y = (y * c) * c⁻¹ := by group
    rw [hy_eq]
    exact K.mul_mem hmem2 (K.inv_mem hcK)
  apply hns (y * c) hyc_out
  have h1conj : y⁻¹ * c * y = (x : G) ^ (-7 * j) := by
    rw [hcdef]
    calc y⁻¹ * (x : G) ^ (-j) * y = y⁻¹ * (x : G) ^ (-j) * y⁻¹⁻¹ := by rw [inv_inv]
      _ = (y⁻¹ * (x : G) * y⁻¹⁻¹) ^ (-j) := conj_zpow.symm
      _ = ((x : G) ^ 7) ^ (-j) := by rw [inv_inv, hinv]
      _ = (x : G) ^ (-7 * j) := by
          rw [← zpow_natCast ((x : G)) 7, ← zpow_mul]
          congr 1
          ring
  have h2conj : y⁻¹ * (y⁻¹ * c * y) * y = (x : G) ^ (-49 * j) := by
    rw [h1conj]
    calc y⁻¹ * (x : G) ^ (-7 * j) * y = y⁻¹ * (x : G) ^ (-7 * j) * y⁻¹⁻¹ := by
          rw [inv_inv]
      _ = (y⁻¹ * (x : G) * y⁻¹⁻¹) ^ (-7 * j) := conj_zpow.symm
      _ = ((x : G) ^ 7) ^ (-7 * j) := by rw [inv_inv, hinv]
      _ = (x : G) ^ (-49 * j) := by
          rw [← zpow_natCast ((x : G)) 7, ← zpow_mul]
          congr 1
          ring
  have hexpand : (y * c) ^ 3 = y ^ 3 * (y⁻¹ * (y⁻¹ * c * y) * y) * (y⁻¹ * c * y) * c := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, sq]
    group
  rw [hexpand, h2conj, h1conj]
  have hy3 : y ^ 3 = (x : G) ^ (3 * j) := by
    rw [← hmG, hj]
  calc y ^ 3 * (x : G) ^ (-49 * j) * (x : G) ^ (-7 * j) * c
      = (x : G) ^ (3 * j) * (x : G) ^ (-49 * j) * (x : G) ^ (-7 * j) * (x : G) ^ (-j) := by
        rw [hy3, hcdef]
    _ = (x : G) ^ (3 * j + -49 * j + -7 * j + -j) := by
        rw [← zpow_add, ← zpow_add, ← zpow_add]
    _ = ((x : G) ^ (9 : ℤ)) ^ (-6 * j) := by
        rw [← zpow_mul]
        congr 1
        ring
    _ = 1 := by rw [hx9z, one_zpow]

/-- **Case B1b.** An order-`9` kernel element `x` with `y x y⁻¹ = x ^ 4` yields
`G ≃* C_9 ⋊ C_9` directly: `x` generates the `C_9`-kernel slot and `y` the acting
slot. -/
theorem order81_caseB_c9c9_of_eigenvector
    {G : Type*} [Group G] {K : Subgroup G} [K.Normal]
    (hcard : Nat.card G = 81) (hKcard : Nat.card K = 27)
    (hKcomm : ∀ a b : K, a * b = b * a)
    (hns : ∀ z : G, z ∉ K → z ^ 3 ≠ 1)
    {y : G} (hyK : y ∉ K) (hy9 : y ^ 9 = 1)
    {x : K} (hxord : orderOf x = 9) (hconj : y * x.1 * y⁻¹ = x.1 ^ 4) :
    Nonempty (G ≃* order81_c9_semidirect_c9_rep) := by
  have hnotmem :=
    order81_caseB_cube_not_mem_zpowers_eigenvector hcard hKcard hns hyK hy9 hxord hconj
  have hx9K : x ^ 9 = 1 := by
    rw [← hxord]
    exact pow_orderOf_eq_one x
  have hx9G : (x : G) ^ 9 = 1 := by
    have := congrArg Subtype.val hx9K
    simpa using this
  exact order81_caseB_c9c9_of_relation hcard hx9G hy9 hconj
    (fun R hxR hyR => order81_caseB_eq_top_of_kernel_gen hcard hKcard hKcomm hns hyK hy9
      hxord hnotmem hxR hyR)

/-- **Case B1c.** An order-`9` kernel element `x` with `y x y⁻¹ = x ^ 7` also yields
`G ≃* C_9 ⋊ C_9`, by replacing the acting element with `y²` (since `7² ≡ 4 mod 9`). -/
theorem order81_caseB_c9c9_of_eigenvector_seven
    {G : Type*} [Group G] {K : Subgroup G} [K.Normal]
    (hcard : Nat.card G = 81) (hKcard : Nat.card K = 27)
    (hKcomm : ∀ a b : K, a * b = b * a)
    (hns : ∀ z : G, z ∉ K → z ^ 3 ≠ 1)
    {y : G} (hyK : y ∉ K) (hy9 : y ^ 9 = 1)
    {x : K} (hxord : orderOf x = 9) (hconj : y * x.1 * y⁻¹ = x.1 ^ 7) :
    Nonempty (G ≃* order81_c9_semidirect_c9_rep) := by
  have hx9K : x ^ 9 = 1 := by
    rw [← hxord]
    exact pow_orderOf_eq_one x
  have hx9G : (x : G) ^ 9 = 1 := by
    have := congrArg Subtype.val hx9K
    simpa using this
  have hy2K : y ^ 2 ∉ K := by
    intro h
    apply hyK
    have h3 : y ^ 3 ∈ K := order81_cube_mem_of_normal_subgroup_card_27 hcard hKcard y
    have hy_eq : y = y ^ 3 * (y ^ 2)⁻¹ := by group
    rw [hy_eq]
    exact K.mul_mem h3 (K.inv_mem h)
  have hy29 : (y ^ 2) ^ 9 = 1 := by
    calc (y ^ 2) ^ 9 = (y ^ 9) ^ 2 := by rw [← pow_mul, ← pow_mul]
      _ = 1 := by rw [hy9, one_pow]
  have hconj2 : (y ^ 2) * x.1 * (y ^ 2)⁻¹ = x.1 ^ 4 := by
    calc (y ^ 2) * x.1 * (y ^ 2)⁻¹ = y * (y * x.1 * y⁻¹) * y⁻¹ := by
          rw [pow_two, mul_inv_rev]
          group
      _ = y * x.1 ^ 7 * y⁻¹ := by rw [hconj]
      _ = (y * x.1 * y⁻¹) ^ 7 := conj_pow.symm
      _ = (x.1 ^ 7) ^ 7 := by rw [hconj]
      _ = x.1 ^ 49 := by rw [← pow_mul]
      _ = x.1 ^ 4 := by
          have h49 : (49 : ℕ) = 9 * 5 + 4 := by norm_num
          rw [h49, pow_add, pow_mul, hx9G, one_pow, one_mul]
  exact order81_caseB_c9c9_of_eigenvector hcard hKcard hKcomm hns hy2K hy29 hxord hconj2

/-- In the non-abelian case-B setting, no order-`9` kernel element is fixed by
conjugation by the outside element `y`: otherwise either an adjustment of `y` by a power
of `x` is an outside element of order `3` (contradicting non-splitness), or `x` and `y`
together centralize `y` in all of `G`, making `G` abelian. -/
theorem order81_caseB_no_fixed_order_nine
    {G : Type*} [Group G] {K : Subgroup G} [K.Normal]
    (hcard : Nat.card G = 81) (hKcard : Nat.card K = 27)
    (hKcomm : ∀ a b : K, a * b = b * a)
    (hns : ∀ z : G, z ∉ K → z ^ 3 ≠ 1)
    (hnoncomm : ¬ ∀ a b : G, a * b = b * a)
    {y : G} (hyK : y ∉ K) (hy9 : y ^ 9 = 1)
    {x : K} (hxord : orderOf x = 9)
    (hfix : y * x.1 * y⁻¹ = x.1) : False := by
  have hcomm : (x : G) * y = y * (x : G) := by
    have h := congrArg (· * y) hfix
    simp only [inv_mul_cancel_right] at h
    exact h.symm
  set k9 : K := ⟨y ^ 3, order81_cube_mem_of_normal_subgroup_card_27 hcard hKcard y⟩
    with hk9def
  by_cases hmem : k9 ∈ Subgroup.zpowers x
  · -- `y³ = x^(3j)`: then `y·x^(−j)` is an outside element of order dividing `3`
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hx9K : x ^ 9 = 1 := by
      rw [← hxord]
      exact pow_orderOf_eq_one x
    have hx9G : (x : G) ^ 9 = 1 := by
      have := congrArg Subtype.val hx9K
      simpa using this
    have hk93 : k9 ^ 3 = 1 := by
      apply Subtype.ext
      change (y ^ 3) ^ 3 = 1
      rw [← pow_mul]
      exact hy9
    obtain ⟨j, hj⟩ : ∃ j : ℤ, m = 3 * j := by
      have h3m : x ^ (m * 3) = 1 := by
        rw [zpow_mul]
        have h1 : (x ^ m) ^ (3 : ℤ) = k9 ^ (3 : ℤ) := by rw [hm]
        rw [h1]
        have h2 : k9 ^ (3 : ℤ) = k9 ^ (3 : ℕ) := by norm_cast
        rw [h2, hk93]
      have hdvd9 : ((9 : ℕ) : ℤ) ∣ m * 3 := by
        have := orderOf_dvd_iff_zpow_eq_one.mpr h3m
        rwa [hxord] at this
      obtain ⟨t, ht⟩ := hdvd9
      refine ⟨t, ?_⟩
      have : m * 3 = 9 * t := by exact_mod_cast ht
      linarith
    have hmG : (x : G) ^ m = y ^ 3 := by
      have := congrArg Subtype.val hm
      simpa [SubgroupClass.coe_zpow, hk9def] using this
    have hy3 : y ^ 3 = (x : G) ^ (3 * j) := by rw [← hmG, hj]
    set c : G := (x : G) ^ (-j) with hcdef
    have hcK : c ∈ K := by
      rw [hcdef]
      exact K.zpow_mem x.2 (-j)
    have hyc_out : y * c ∉ K := by
      intro hmem2
      apply hyK
      have hy_eq : y = (y * c) * c⁻¹ := by group
      rw [hy_eq]
      exact K.mul_mem hmem2 (K.inv_mem hcK)
    apply hns (y * c) hyc_out
    have hcy : Commute y c := by
      have hyx : Commute y ((x : G)) := hcomm.symm
      exact hyx.zpow_right (-j)
    have hc3 : c ^ 3 = (x : G) ^ (-(3 * j)) := by
      rw [hcdef, ← zpow_natCast ((x : G) ^ (-j)) 3, ← zpow_mul]
      congr 1
      ring
    rw [hcy.mul_pow, hy3, hc3, ← zpow_add]
    simp
  · -- `y³ ∉ ⟨x⟩`: the centralizer of `y` contains `x` and `y`, hence is everything
    have hxC : (x : G) ∈ Subgroup.centralizer {y} := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact hcomm.symm
    have hyC : y ∈ Subgroup.centralizer {y} := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      rfl
    have htop : Subgroup.centralizer {y} = ⊤ :=
      order81_caseB_eq_top_of_kernel_gen hcard hKcard hKcomm hns hyK hy9 hxord hmem hxC hyC
    apply hnoncomm
    have hcentral : ∀ g : G, y * g = g * y := by
      intro g
      have hg : g ∈ Subgroup.centralizer {y} := htop ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_iff.mp hg y (Set.mem_singleton y)
    have habel : IsMulCommutative G := by
      apply order81_caseB_comm_of_shift_trivial hcard hKcard hKcomm hyK
      intro k
      apply order81_caseB_shift_eq_one_of_commute
      exact hcentral k.1
    exact fun a b => habel.is_comm.comm a b

/-! ### Case-B dispatcher infrastructure

The remaining sub-case analysis transports the conjugation action to `C_9 × C_3` via
`e` and classifies it as a parameter automorphism `paramAut r s t`; the following
finite computations support the resulting case split. -/

/-- The standard order-`9` generator `(1, 0)` of `C_9 × C_3` has order `9`. -/
theorem order81_caseB_cubeSource_orderOf : orderOf order81_C9C3_cubeSource = 9 := by
  have h9 : order81_C9C3_cubeSource ^ 9 = 1 := by decide +kernel
  have h3 : order81_C9C3_cubeSource ^ 3 ≠ 1 := by decide +kernel
  have hdvd : orderOf order81_C9C3_cubeSource ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num]
    exact orderOf_dvd_iff_pow_eq_one.mpr h9
  rcases (Nat.dvd_prime_pow Nat.prime_three).mp hdvd with ⟨j, hj2, hj⟩
  interval_cases j
  · exfalso
    apply h3
    have h1 : order81_C9C3_cubeSource = 1 := orderOf_eq_one_iff.mp (by simpa using hj)
    rw [h1]
    simp
  · exfalso
    apply h3
    have h1 : orderOf order81_C9C3_cubeSource = 3 := by simpa using hj
    have := pow_orderOf_eq_one order81_C9C3_cubeSource
    rwa [h1] at this
  · simpa using hj

/-- With `r = 0`, `t = 0` the parameter automorphism fixes the standard generator. -/
theorem order81_caseB_paramAut_gen_fixed :
    ∀ s : ZMod 3, order81_c9c3_paramAut 0 s 0 order81_C9C3_cubeSource =
      order81_C9C3_cubeSource := by
  decide +kernel

/-- With `r = 1`, `t = 0` the parameter automorphism raises the standard generator to
the fourth power. -/
theorem order81_caseB_paramAut_gen_pow_four :
    ∀ s : ZMod 3, order81_c9c3_paramAut 1 s 0 order81_C9C3_cubeSource =
      order81_C9C3_cubeSource ^ 4 := by
  decide +kernel

/-- With `r = 2`, `t = 0` the parameter automorphism raises the standard generator to
the seventh power. -/
theorem order81_caseB_paramAut_gen_pow_seven :
    ∀ s : ZMod 3, order81_c9c3_paramAut 2 s 0 order81_C9C3_cubeSource =
      order81_C9C3_cubeSource ^ 7 := by
  decide +kernel

set_option maxHeartbeats 4000000 in -- large finite decide over C9C3 (729+ cases)
/-- For `s = 0`, `t ≠ 0` the parameter automorphism has exactly `9` fixed points. -/
theorem order81_caseB_paramAut_fix_card :
    ∀ r t : ZMod 3, t ≠ 0 →
      Fintype.card {v : order81_C9C3 // order81_c9c3_paramAut r 0 t v = v} = 9 := by
  decide +kernel

set_option maxHeartbeats 4000000 in -- large finite decide over C9C3 (729+ cases)
/-- Norm formula for `s = 0` parameter automorphisms: `v·σ(v)·σ²(v)` is the cube of the
first coordinate. -/
theorem order81_caseB_paramAut_norm_s0 :
    ∀ (r t : ZMod 3) (a : ZMod 9) (b : ZMod 3),
      ((Multiplicative.ofAdd a, Multiplicative.ofAdd b) : order81_C9C3) *
        order81_c9c3_paramAut r 0 t (Multiplicative.ofAdd a, Multiplicative.ofAdd b) *
        order81_c9c3_paramAut r 0 t (order81_c9c3_paramAut r 0 t
          (Multiplicative.ofAdd a, Multiplicative.ofAdd b)) =
      (Multiplicative.ofAdd (3 * a), 1) := by
  decide +kernel

set_option maxHeartbeats 4000000 in -- large finite decide over C9C3 (729+ cases)
/-- Solvability of the conjugator equation for `s = 0`, `t ≠ 0` parameter actions when
the `C_3`-component `β` of the cube is nonzero: some tuning `ka` of the cube and shift
argument `wa` realize the inverted tuned cube as a shift value. -/
theorem order81_caseB_paramAut_solution :
    ∀ (r t : ZMod 3), t ≠ 0 → ∀ (A : ZMod 9), order81_zmod9To3 A = 0 →
      ∀ (β : ZMod 3), β ≠ 0 →
      ∃ ka wa : ZMod 9,
        order81_c9c3_paramAut r 0 t (Multiplicative.ofAdd wa, 1) *
          ((Multiplicative.ofAdd wa, 1) : order81_C9C3)⁻¹ =
        ((Multiplicative.ofAdd (3 * ka + A), Multiplicative.ofAdd β) : order81_C9C3)⁻¹ := by
  decide +kernel

/-- Cube-tuning for the `β = 0` branch: some `ka` cancels the tuned cube entirely. -/
theorem order81_caseB_paramAut_cube_zero :
    ∀ A : ZMod 9, order81_zmod9To3 A = 0 → ∃ ka : ZMod 9, 3 * ka + A = 0 := by
  decide +kernel

/-- The shift homomorphism only depends on the coset of the outside element. -/
theorem order81_caseB_shiftHom_mul_left
    {G : Type*} [Group G] {K : Subgroup G} [K.Normal]
    (hKcomm : ∀ a b : K, a * b = b * a) (k : K) (y : G) :
    order81_caseB_shiftHom hKcomm (k.1 * y) = order81_caseB_shiftHom hKcomm y := by
  apply MonoidHom.ext
  intro w
  rw [order81_caseB_shiftHom_apply, order81_caseB_shiftHom_apply]
  congr 1
  apply Subtype.ext
  change (k.1 * y) * w.1 * (k.1 * y)⁻¹ = y * w.1 * y⁻¹
  have hmemc : y * w.1 * y⁻¹ ∈ K :=
    (inferInstance : K.Normal).conj_mem w.1 w.2 y
  have hcomm2 : k.1 * (y * w.1 * y⁻¹) = (y * w.1 * y⁻¹) * k.1 := by
    have := hKcomm k ⟨y * w.1 * y⁻¹, hmemc⟩
    exact congrArg Subtype.val this
  calc (k.1 * y) * w.1 * (k.1 * y)⁻¹ = k.1 * (y * w.1 * y⁻¹) * k.1⁻¹ := by
        rw [mul_inv_rev]
        group
    _ = (y * w.1 * y⁻¹) * k.1 * k.1⁻¹ := by rw [hcomm2]
    _ = y * w.1 * y⁻¹ := by group

/-- The kernel of the shift is carried by `e` onto the fixed points of the transported
action. -/
theorem order81_caseB_shift_ker_card_eq_fix
    {G : Type*} [Group G] {K : Subgroup G} [K.Normal]
    (hKcomm : ∀ a b : K, a * b = b * a) {y : G}
    (e : K ≃* order81_C9C3) {σE : MulAut order81_C9C3}
    (hval : ∀ k : K, MulAut.conjNormal (H := K) y k = e.symm (σE (e k))) :
    Nat.card (order81_caseB_shiftHom hKcomm y).ker =
      Nat.card {v : order81_C9C3 // σE v = v} := by
  apply Nat.card_congr
  apply Equiv.subtypeEquiv e.toEquiv
  intro k
  rw [MonoidHom.mem_ker, order81_caseB_shiftHom_apply, mul_inv_eq_one, hval k]
  constructor
  · intro h
    have := congrArg e h
    simpa using this
  · intro h
    have : e.symm (σE (e k)) = e.symm (e k) := by
      simpa using congrArg e.symm h
    simpa using this

/-- Case analysis over `ZMod 3`. -/
theorem order81_caseB_zmod3_cases : ∀ u : ZMod 3, u = 0 ∨ u = 1 ∨ u = 2 := by
  decide

/-- The cube of a tuned outside element `kk · y` expands in terms of the iterated
conjugation action, for any abelian normal `K` and any `y`. -/
theorem order81_caseB_cube_formula
    {G : Type*} [Group G] {K : Subgroup G} [K.Normal] (y : G) (kk : K) :
    (kk.1 * y) ^ 3 =
      (kk * MulAut.conjNormal (H := K) y kk *
        MulAut.conjNormal (H := K) y (MulAut.conjNormal (H := K) y kk)).1 * y ^ 3 := by
  have hσ1 : y * kk.1 * y⁻¹ = (MulAut.conjNormal (H := K) y kk).1 := rfl
  have hσ2 : y * (MulAut.conjNormal (H := K) y kk).1 * y⁻¹ =
      (MulAut.conjNormal (H := K) y (MulAut.conjNormal (H := K) y kk)).1 := rfl
  calc (kk.1 * y) ^ 3
      = kk.1 * (y * kk.1 * y⁻¹) * (y * (y * kk.1 * y⁻¹) * y⁻¹) * y ^ 3 := by
        rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, sq]
        group
    _ = (kk * MulAut.conjNormal (H := K) y kk *
          MulAut.conjNormal (H := K) y (MulAut.conjNormal (H := K) y kk)).1 *
          y ^ 3 := by
        rw [hσ1, hσ2, Subgroup.coe_mul, Subgroup.coe_mul]

set_option maxHeartbeats 4000000 in -- large finite decide over C9C3 (729+ cases)
/-- The `doubleShear`-family parameter automorphisms (`s = t ≠ 0`) have Norm surjective
onto their fixed points: every fixed point is realized as `k · σ(k) · σ²(k)` for some
`k`. This is the finite core fact behind "`doubleShear`-conjugate extensions always
split". -/
theorem order81_caseB_paramAut_doubleShear_splits (r s : ZMod 3) (hs : s ≠ 0)
    (f : order81_C9C3) (hf : order81_c9c3_paramAut r s s f = f) :
    ∃ k : order81_C9C3,
      k * order81_c9c3_paramAut r s s k *
        order81_c9c3_paramAut r s s (order81_c9c3_paramAut r s s k) = f⁻¹ := by
  rcases order81_caseB_zmod3_cases s with hs0 | hs1 | hs2
  · exact absurd hs0 hs
  · subst hs1
    revert hf
    fin_cases r <;> revert f <;> decide +kernel
  · subst hs2
    revert hf
    fin_cases r <;> revert f <;> decide +kernel

/-- **Case-B dispatcher (the `C_9 ⋊ C_9` half).** In the non-abelian case-B setting,
either `G ≅ C_9 ⋊ C_9`, or the action transported along `e` is a parameter automorphism
with `s ≠ 0` and `t ≠ 0` (the `sixShear` family, which the non-split representative
construction will absorb). -/
theorem order81_caseB_c9c9_or_param_marker
    {G : Type*} [Group G] {K : Subgroup G} [K.Normal]
    (hcard : Nat.card G = 81) (hKcard : Nat.card K = 27)
    (e : K ≃* order81_C9C3)
    (hKcomm : ∀ a b : K, a * b = b * a)
    (hns : ∀ z : G, z ∉ K → z ^ 3 ≠ 1)
    (h27 : ∀ g : G, orderOf g ≠ 27)
    (hnoncomm : ¬ ∀ a b : G, a * b = b * a)
    {y : G} (hyK : y ∉ K) (hy9 : y ^ 9 = 1) :
    Nonempty (G ≃* order81_c9_semidirect_c9_rep) ∨
      ∃ r s t : ZMod 3, s ≠ 0 ∧ t ≠ 0 ∧ s ≠ t ∧
        e.symm.trans ((MulAut.conjNormal (H := K) y).trans e) =
          order81_c9c3_paramAut r s t := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKcommutative : IsMulCommutative K := IsMulCommutative.of_comm hKcomm
  -- the transported action has order dividing `3`
  have hρ3 : (MulAut.conjNormal (H := K) y) ^ 3 = 1 :=
    order81_conjNormal_cube_eq_one_of_abelian_normal_subgroup_card_27 hcard hKcard
      hKcommutative y
  have hσE3 : (e.symm.trans ((MulAut.conjNormal (H := K) y).trans e)) ^ 3 = 1 := by
    apply MulEquiv.ext
    intro v
    have hpow0 : ((MulAut.conjNormal (H := K) y) ^ 3) (e.symm v) = e.symm v := by
      rw [hρ3]
      rfl
    have hpow : (MulAut.conjNormal (H := K) y) ((MulAut.conjNormal (H := K) y)
        ((MulAut.conjNormal (H := K) y) (e.symm v))) = e.symm v := by
      simpa [pow_succ] using hpow0
    calc ((e.symm.trans ((MulAut.conjNormal (H := K) y).trans e)) ^ 3) v
        = e ((MulAut.conjNormal (H := K) y) ((MulAut.conjNormal (H := K) y)
            ((MulAut.conjNormal (H := K) y) (e.symm v)))) := by
          simp [pow_succ]
      _ = v := by
          rw [hpow]
          simp
  obtain ⟨r, s, t, hparam⟩ :=
    order81_C9C3_aut_eq_paramAut_of_pow_three _ hσE3
  -- value-level transport of the action
  have hval : ∀ k : K, MulAut.conjNormal (H := K) y k =
      e.symm (order81_c9c3_paramAut r s t (e k)) := by
    intro k
    have h1 : order81_c9c3_paramAut r s t (e k) =
        (e.symm.trans ((MulAut.conjNormal (H := K) y).trans e)) (e k) := by
      rw [hparam]
    rw [h1]
    simp
  have hvalE : ∀ w : K, e (MulAut.conjNormal (H := K) y w) =
      order81_c9c3_paramAut r s t (e w) := by
    intro w
    rw [hval w]
    simp
  -- the standard order-`9` kernel element and its conjugate
  set x₀ : K := e.symm order81_C9C3_cubeSource with hx₀def
  have hx₀ord : orderOf x₀ = 9 := by
    rw [hx₀def, MulEquiv.orderOf_eq e.symm]
    exact order81_caseB_cubeSource_orderOf
  have hEx₀ : e x₀ = order81_C9C3_cubeSource := by
    rw [hx₀def]
    simp
  have hvalx₀ : y * x₀.1 * y⁻¹ =
      (e.symm (order81_c9c3_paramAut r s t (e x₀))).1 :=
    congrArg Subtype.val (hval x₀)
  rw [hEx₀] at hvalx₀
  by_cases ht : t = 0
  · -- `t = 0`: eigenvector analysis on `x₀`
    subst ht
    rcases order81_caseB_zmod3_cases r with hr | hr | hr <;> subst hr
    · -- `r = 0`: `x₀` is fixed, contradiction
      exfalso
      apply order81_caseB_no_fixed_order_nine hcard hKcard hKcomm hns hnoncomm hyK hy9
        hx₀ord
      rw [hvalx₀, order81_caseB_paramAut_gen_fixed s, ← hx₀def]
    · -- `r = 1`: fourth-power eigenvector
      left
      apply order81_caseB_c9c9_of_eigenvector hcard hKcard hKcomm hns hyK hy9 hx₀ord
      rw [hvalx₀, order81_caseB_paramAut_gen_pow_four s, map_pow, ← hx₀def]
      simp
    · -- `r = 2`: seventh-power eigenvector
      left
      apply order81_caseB_c9c9_of_eigenvector_seven hcard hKcard hKcomm hns hyK hy9 hx₀ord
      rw [hvalx₀, order81_caseB_paramAut_gen_pow_seven s, map_pow, ← hx₀def]
      simp
  · by_cases hs : s = 0
    · -- `s = 0`, `t ≠ 0`: tune `y` into the conjugator case
      subst hs
      left
      have hker9 : Nat.card (order81_caseB_shiftHom hKcomm y).ker = 9 := by
        rw [order81_caseB_shift_ker_card_eq_fix hKcomm e hval, Nat.card_eq_fintype_card]
        exact order81_caseB_paramAut_fix_card r t ht
      -- coordinates of `y³`
      set k9 : K := ⟨y ^ 3, order81_cube_mem_of_normal_subgroup_card_27 hcard hKcard y⟩
        with hk9def
      obtain ⟨A, β, hAβ⟩ : ∃ A β,
          e k9 = (Multiplicative.ofAdd A, Multiplicative.ofAdd β) :=
        ⟨Multiplicative.toAdd (e k9).1, Multiplicative.toAdd (e k9).2, by
          rw [ofAdd_toAdd, ofAdd_toAdd]⟩
      have hk9fix : MulAut.conjNormal (H := K) y k9 = k9 := by
        apply Subtype.ext
        change y * (y ^ 3) * y⁻¹ = y ^ 3
        group
      have hfixE : order81_c9c3_paramAut r 0 t (e k9) = e k9 := by
        rw [← hvalE, hk9fix]
      have hA0 : order81_zmod9To3 A = 0 := by
        rw [hAβ, order81_c9c3_paramAut_apply] at hfixE
        have h2 := congrArg Prod.snd hfixE
        simp only at h2
        have h3 : β + t * order81_zmod9To3 A = β := by
          have := congrArg Multiplicative.toAdd h2
          simpa using this
        have h4 : t * order81_zmod9To3 A = 0 :=
          add_left_cancel (a := β) (by rw [add_zero]; exact h3)
        rcases mul_eq_zero.mp h4 with h | h
        · exact absurd h ht
        · exact h
      -- generic cube formula for tuned outside elements
      have hcube_formula := fun kk : K => order81_caseB_cube_formula (K := K) y kk
      have hnormE : ∀ ka' : ZMod 9,
          (e.symm (Multiplicative.ofAdd ka', Multiplicative.ofAdd (0 : ZMod 3)) : K) *
            MulAut.conjNormal (H := K) y
              (e.symm (Multiplicative.ofAdd ka', Multiplicative.ofAdd (0 : ZMod 3))) *
            MulAut.conjNormal (H := K) y (MulAut.conjNormal (H := K) y
              (e.symm (Multiplicative.ofAdd ka', Multiplicative.ofAdd (0 : ZMod 3)))) =
          e.symm (Multiplicative.ofAdd (3 * ka'), 1) := by
        intro ka'
        apply e.injective
        rw [map_mul, map_mul, hvalE, hvalE, hvalE]
        simp only [MulEquiv.apply_symm_apply]
        exact order81_caseB_paramAut_norm_s0 r t ka' 0
      have hcube_val : ∀ ka' : ZMod 9,
          ((e.symm (Multiplicative.ofAdd ka', Multiplicative.ofAdd (0 : ZMod 3)) : K).1 *
            y) ^ 3 =
          (e.symm (Multiplicative.ofAdd (3 * ka'), 1)).1 * y ^ 3 := by
        intro ka'
        rw [hcube_formula _, hnormE ka']
      have houtside : ∀ kk : K, kk.1 * y ∉ K := by
        intro kk hmem2
        apply hyK
        have hy_eq : y = kk.1⁻¹ * (kk.1 * y) := by group
        rw [hy_eq]
        exact K.mul_mem (K.inv_mem kk.2) hmem2
      by_cases hβ : β = 0
      · -- `β = 0`: the tuned cube is trivial, contradicting non-splitness
        exfalso
        subst hβ
        obtain ⟨ka, hka⟩ := order81_caseB_paramAut_cube_zero A hA0
        apply hns ((e.symm (Multiplicative.ofAdd ka, Multiplicative.ofAdd (0 : ZMod 3)) :
            K).1 * y) (houtside _)
        rw [hcube_val ka]
        have hprod : (e.symm (Multiplicative.ofAdd (3 * ka), 1) : K) * k9 = 1 := by
          apply e.injective
          rw [map_mul, map_one, hAβ]
          simp only [MulEquiv.apply_symm_apply]
          rw [Prod.mk_mul_mk, one_mul, ← ofAdd_add, hka]
          rfl
        calc (e.symm (Multiplicative.ofAdd (3 * ka), 1) : K).1 * y ^ 3
            = ((e.symm (Multiplicative.ofAdd (3 * ka), 1) : K) * k9).1 := by
              rw [Subgroup.coe_mul]
          _ = 1 := by
              rw [hprod]
              rfl
      · -- `β ≠ 0`: solve for the conjugator after tuning
        obtain ⟨ka, wa, hsol⟩ := order81_caseB_paramAut_solution r t ht A hA0 β hβ
        set kk : K := e.symm (Multiplicative.ofAdd ka, Multiplicative.ofAdd (0 : ZMod 3))
          with hkkdef
        have hy'K : kk.1 * y ∉ K := houtside kk
        have hy'ord : orderOf (kk.1 * y) = 9 :=
          order81_caseB_orderOf_eq_nine hcard hKcard hns h27 hy'K
        have hy'9 : (kk.1 * y) ^ 9 = 1 := by
          rw [← hy'ord]
          exact pow_orderOf_eq_one _
        have hshift_eq : order81_caseB_shiftHom hKcomm (kk.1 * y) =
            order81_caseB_shiftHom hKcomm y :=
          order81_caseB_shiftHom_mul_left hKcomm kk y
        have hker9' : Nat.card (order81_caseB_shiftHom hKcomm (kk.1 * y)).ker = 9 := by
          rw [hshift_eq]
          exact hker9
        set k9' : K := ⟨(kk.1 * y) ^ 3,
          order81_cube_mem_of_normal_subgroup_card_27 hcard hKcard (kk.1 * y)⟩
          with hk9'def
        have hk9'eq : k9' = e.symm (Multiplicative.ofAdd (3 * ka), 1) * k9 := by
          apply Subtype.ext
          rw [Subgroup.coe_mul]
          change (kk.1 * y) ^ 3 = _ * y ^ 3
          rw [hkkdef]
          exact hcube_val ka
        have hk9'E : e k9' =
            (Multiplicative.ofAdd (3 * ka + A), Multiplicative.ofAdd β) := by
          rw [hk9'eq, map_mul, hAβ]
          simp only [MulEquiv.apply_symm_apply]
          rw [Prod.mk_mul_mk, one_mul, ← ofAdd_add]
        have hmem : k9'⁻¹ ∈ (order81_caseB_shiftHom hKcomm (kk.1 * y)).range := by
          refine ⟨e.symm (Multiplicative.ofAdd wa, 1), ?_⟩
          rw [hshift_eq, order81_caseB_shiftHom_apply]
          apply e.injective
          rw [map_mul, map_inv, map_inv, hvalE, hk9'E]
          simp only [MulEquiv.apply_symm_apply]
          exact hsol
        obtain ⟨B, hBord, hDB, hconj⟩ := order81_caseB_exists_conjugator hcard hKcard e
          hKcomm hns hy'K hker9' hmem
        exact order81_caseB_c9c9_of_conjugator hcard hKcard e hKcomm hns hy'K hy'9 hBord
          hconj hDB
    · -- `s ≠ 0`, `t ≠ 0`: split further on whether `s = t` (the `doubleShear` orbit,
      -- which always splits) or `s ≠ t` (the genuine `sixShear`/non-split orbit)
      by_cases hst : s = t
      · -- `s = t`: `doubleShear`-conjugate, hence Norm is onto `Fix`, contradicting `hns`
        exfalso
        subst hst
        set k9 : K := ⟨y ^ 3, order81_cube_mem_of_normal_subgroup_card_27 hcard hKcard y⟩
          with hk9def
        have hk9fix : MulAut.conjNormal (H := K) y k9 = k9 := by
          apply Subtype.ext
          change y * (y ^ 3) * y⁻¹ = y ^ 3
          group
        have hfixE : order81_c9c3_paramAut r s s (e k9) = e k9 := by
          rw [← hvalE, hk9fix]
        obtain ⟨f, hf⟩ :=
          order81_caseB_paramAut_doubleShear_splits r s hs (e k9) hfixE
        set kk : K := e.symm f with hkkdef
        have hkke : e kk = f := by rw [hkkdef]; simp
        have hnormE : kk * MulAut.conjNormal (H := K) y kk *
            MulAut.conjNormal (H := K) y (MulAut.conjNormal (H := K) y kk) =
            k9⁻¹ := by
          apply e.injective
          rw [map_mul, map_mul, hvalE, hvalE, hvalE, hkke]
          rw [map_inv, ← hf]
        have hcube_val : (kk.1 * y) ^ 3 = 1 := by
          rw [order81_caseB_cube_formula y kk, hnormE, hk9def]
          simp
        have houtside : kk.1 * y ∉ K := by
          intro hmem2
          apply hyK
          have hy_eq : y = kk.1⁻¹ * (kk.1 * y) := by group
          rw [hy_eq]
          exact K.mul_mem (K.inv_mem kk.2) hmem2
        exact hns (kk.1 * y) houtside hcube_val
      · -- `s ≠ t`: the genuine `sixShear`-family marker
        right
        exact ⟨r, s, t, hs, ht, hst, hparam⟩

end Smallgroups.UsefulTheorems

/-! ### `B2`: conjugating the surviving action to the standard `sixShear` form -/

namespace Smallgroups.UsefulTheorems

set_option maxHeartbeats 4000000 in -- large finite decide over C9C3 (729+ cases)
/-- For any `r`, `paramAut r 2 1` (the `sixShear`-family action with `r` un-normalized)
is conjugate, by an explicit automorphism built from `liftAut`, to the standard
`sixShearAut = paramAut 0 2 1`. -/
theorem order81_caseB_paramAut_conj_to_sixShear (r' : ZMod 3) :
    ∃ φ : MulAut order81_C9C3,
      MulAut.conj φ (order81_c9c3_paramAut r' 2 1) = order81_c9c3_sixShearAut := by
  rcases order81_caseB_zmod3_cases r' with hr | hr | hr <;> subst hr
  · exact ⟨1, by
      rw [order81_c9c3_sixShearAut_eq_param, MulAut.conj_apply, one_mul, inv_one, mul_one]⟩
  · exact ⟨order81_c9c3_liftAut * order81_c9c3_liftAut, by
      rw [order81_c9c3_sixShearAut_eq_param]
      ext x <;> revert x <;> decide +kernel⟩
  · exact ⟨order81_c9c3_liftAut, by
      rw [order81_c9c3_sixShearAut_eq_param]
      ext x <;> revert x <;> decide +kernel⟩

set_option maxHeartbeats 4000000 in -- large finite decide over C9C3 (729+ cases)
/-- For any `r` and the swapped-orbit action `paramAut r 1 2`, squaring the action
(replacing the acting generator by its square) lands in the `paramAut _ 2 1` family. -/
theorem order81_caseB_paramAut_sq_swap (r : ZMod 3) :
    (order81_c9c3_paramAut r 1 2) ^ 2 = order81_c9c3_paramAut (2 * r + 2) 2 1 := by
  rw [order81_c9c3_paramAut_sq_eq]
  have h1 : (1 : ZMod 3) * 2 = 2 := by decide
  have h2 : (2 : ZMod 3) * 1 = 2 := by decide
  have h3 : (2 : ZMod 3) * 2 = 1 := by decide
  rw [h1, h2, h3]

/-- Combining the two previous facts: for any `r, r'` with `(r', s, t) ∈ {(r,2,1), (r,1,2)}`
(the surviving `sixShear`-family orbit), some power (`1` or `2`) of the action and some
conjugating automorphism together reach the standard `sixShearAut`. -/
theorem order81_caseB_paramAut_reduce_to_sixShear (r s t : ZMod 3) (hs : s ≠ 0) (ht : t ≠ 0)
    (hst : s ≠ t) :
    ∃ (n : ℕ) (φ : MulAut order81_C9C3), (n = 1 ∨ n = 2) ∧
      MulAut.conj φ ((order81_c9c3_paramAut r s t) ^ n) = order81_c9c3_sixShearAut := by
  rcases order81_caseB_zmod3_cases s with hs0 | hs1 | hs2
  · exact absurd hs0 hs
  · -- `s = 1`: since `s ≠ t` and `t ≠ 0`, `t = 2`
    subst hs1
    have ht2 : t = 2 := by
      rcases order81_caseB_zmod3_cases t with h | h | h
      · exact absurd h ht
      · exact absurd h.symm hst
      · exact h
    subst ht2
    obtain ⟨φ, hφ⟩ := order81_caseB_paramAut_conj_to_sixShear (2 * r + 2)
    refine ⟨2, φ, Or.inr rfl, ?_⟩
    rw [order81_caseB_paramAut_sq_swap]
    exact hφ
  · -- `s = 2`: since `s ≠ t` and `t ≠ 0`, `t = 1`
    subst hs2
    have ht1 : t = 1 := by
      rcases order81_caseB_zmod3_cases t with h | h | h
      · exact absurd h ht
      · exact h
      · exact absurd h.symm hst
    subst ht1
    obtain ⟨φ, hφ⟩ := order81_caseB_paramAut_conj_to_sixShear r
    exact ⟨1, φ, Or.inl rfl, by rwa [pow_one]⟩

end Smallgroups.UsefulTheorems

/-! ### `B2` final assembly: normal-form decomposition and the `nonSplit_rep` isomorphism -/

namespace Smallgroups.UsefulTheorems

/-- The quotient of an order-`81` group by a normal subgroup of order `27` has order `3`. -/
theorem order81_caseB_quotient_card
    {G : Type*} [Group G] {K : Subgroup G} [K.Normal]
    (hcard : Nat.card G = 81) (hKcard : Nat.card K = 27) :
    Nat.card (G ⧸ K) = 3 := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hKindex : K.index = 3 := by
    have hmul := K.index_mul_card
    rw [hKcard, hcard] at hmul
    omega
  rw [← K.index_eq_card, hKindex]

/-- An outside element's image in the quotient has order exactly `3`. -/
theorem order81_caseB_quotient_orderOf
    {G : Type*} [Group G] {K : Subgroup G} [K.Normal]
    (hcard : Nat.card G = 81) (hKcard : Nat.card K = 27) {g : G} (hgK : g ∉ K) :
    orderOf (QuotientGroup.mk' K g) = 3 := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hcardq := order81_caseB_quotient_card hcard hKcard
  haveI : Finite (G ⧸ K) := Nat.finite_of_card_ne_zero (by rw [hcardq]; norm_num)
  have hne : QuotientGroup.mk' K g ≠ 1 := by
    intro h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    exact hgK h
  have hdvd : orderOf (QuotientGroup.mk' K g) ∣ 3 := by
    have := orderOf_dvd_natCard (QuotientGroup.mk' K g)
    rwa [hcardq] at this
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact absurd (orderOf_eq_one_iff.mp h1) hne
  · exact h3

/-- A power of an outside element lies in `K` iff `3` divides the exponent. -/
theorem order81_caseB_zpow_mem_iff
    {G : Type*} [Group G] {K : Subgroup G} [K.Normal]
    (hcard : Nat.card G = 81) (hKcard : Nat.card K = 27) {g : G} (hgK : g ∉ K) (m : ℤ) :
    g ^ m ∈ K ↔ (3 : ℤ) ∣ m := by
  have hord := order81_caseB_quotient_orderOf hcard hKcard hgK
  constructor
  · intro hmem
    have hq : (QuotientGroup.mk' K g) ^ m = 1 := by
      rw [← map_zpow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hmem
    have := orderOf_dvd_iff_zpow_eq_one.mpr hq
    rwa [hord] at this
  · intro hdvd
    obtain ⟨c, hc⟩ := hdvd
    have hg3 : g ^ (3 : ℤ) ∈ K := by
      have h1 : g ^ (3 : ℕ) ∈ K := order81_cube_mem_of_normal_subgroup_card_27 hcard hKcard g
      exact_mod_cast h1
    rw [hc, zpow_mul]
    exact K.zpow_mem hg3 c

/-- Normal-form existence: every element decomposes as `k * g ^ i` for some `k ∈ K` and
`i : ZMod 3` (using the natural-number power via `i.val`). -/
theorem order81_caseB_normal_form_exists
    {G : Type*} [Group G] {K : Subgroup G} [K.Normal]
    (hcard : Nat.card G = 81) (hKcard : Nat.card K = 27) {g : G} (hgK : g ∉ K) (x : G) :
    ∃ (k : K) (i : ZMod 3), x = k.1 * g ^ i.val := by
  obtain ⟨k, hkK, n, hn⟩ := order81_normal_layer_exists_mul_zpow_of_not_mem_card_27
    hcard hKcard (g := g) (x := x) hgK
  have hg3 : g ^ (3 : ℤ) ∈ K := by
    have h1 : g ^ (3 : ℕ) ∈ K := order81_cube_mem_of_normal_subgroup_card_27 hcard hKcard g
    exact_mod_cast h1
  set i : ZMod 3 := (n : ZMod 3) with hidef
  have hsplit : n = 3 * (n / 3) + i.val := by
    have hval : (i.val : ℤ) = n % 3 := by
      rw [hidef, ZMod.val_intCast]
      norm_num
    have := Int.mul_ediv_add_emod n 3
    omega
  refine ⟨⟨k * (g ^ (3 : ℤ)) ^ (n / 3), K.mul_mem hkK (K.zpow_mem hg3 _)⟩, i, ?_⟩
  change x = (k * (g ^ (3 : ℤ)) ^ (n / 3)) * g ^ (i.val : ℕ)
  rw [mul_assoc, ← zpow_mul, ← zpow_natCast g i.val, ← zpow_add]
  rw [show 3 * (n / 3) + (i.val : ℤ) = n by exact_mod_cast hsplit.symm]
  exact hn

/-- Normal-form uniqueness: the decomposition of the previous lemma is unique. -/
theorem order81_caseB_normal_form_unique
    {G : Type*} [Group G] {K : Subgroup G} [K.Normal]
    (hcard : Nat.card G = 81) (hKcard : Nat.card K = 27) {g : G} (hgK : g ∉ K)
    {k l : K} {i j : ZMod 3} (h : k.1 * g ^ i.val = l.1 * g ^ j.val) :
    i = j ∧ k = l := by
  have hg_eq : (l.1⁻¹ * k.1) = g ^ (j.val : ℤ) * (g ^ (i.val : ℤ))⁻¹ := by
    have h1 : l.1⁻¹ * (k.1 * g ^ i.val) = l.1⁻¹ * (l.1 * g ^ j.val) := by rw [h]
    have h2 : l.1⁻¹ * (l.1 * g ^ j.val) = g ^ j.val := by group
    rw [h2] at h1
    have h3 : l.1⁻¹ * (k.1 * g ^ i.val) = (l.1⁻¹ * k.1) * g ^ i.val := by group
    rw [h3] at h1
    have h4 := congrArg (· * (g ^ i.val)⁻¹) h1
    simp only [mul_inv_cancel_right] at h4
    rw [h4, zpow_natCast, zpow_natCast]
  have hmem : g ^ ((j.val : ℤ) - i.val) ∈ K := by
    rw [zpow_sub]
    have hlk : (l.1⁻¹ * k.1) ∈ K := K.mul_mem (K.inv_mem l.2) k.2
    rwa [← hg_eq]
  have hdvd : (3 : ℤ) ∣ ((j.val : ℤ) - i.val) :=
    (order81_caseB_zpow_mem_iff hcard hKcard hgK _).mp hmem
  have hij : i.val = j.val := by
    have hb1 : (i.val : ℤ) < 3 := by exact_mod_cast ZMod.val_lt i
    have hb2 : (j.val : ℤ) < 3 := by exact_mod_cast ZMod.val_lt j
    have hb3 : (0 : ℤ) ≤ i.val := by positivity
    have hb4 : (0 : ℤ) ≤ j.val := by positivity
    omega
  have hij' : i = j := by
    have := congrArg (Nat.cast : ℕ → ZMod 3) hij
    rwa [ZMod.natCast_val, ZMod.natCast_val, ZMod.cast_id, ZMod.cast_id] at this
  refine ⟨hij', ?_⟩
  subst hij'
  have h5 : k.1 * g ^ i.val = l.1 * g ^ i.val := h
  exact Subtype.ext (mul_right_cancel h5)

/-- Conjugation by a product decomposes as an iteration. -/
theorem order81_caseB_conjNormal_mul
    {G : Type*} [Group G] {K : Subgroup G} [K.Normal] (a b : G) (k : K) :
    MulAut.conjNormal (H := K) (a * b) k =
      MulAut.conjNormal (H := K) a (MulAut.conjNormal (H := K) b k) := by
  apply Subtype.ext
  change (a * b) * k.1 * (a * b)⁻¹ = a * (b * k.1 * b⁻¹) * a⁻¹
  group

/-- Given that conjugation by `y'` transports (via `e'`) to `sixShearAut`, conjugation by
any power `y' ^ i.val` (`i : ZMod 3`) transports to the corresponding power of
`sixShearAut`. -/
theorem order81_caseB_action_iterate
    {G : Type*} [Group G] {K : Subgroup G} [K.Normal]
    {y' : G} {e' : K ≃* order81_C9C3}
    (haction : ∀ k : K, MulAut.conjNormal (H := K) y' k =
      e'.symm (order81_c9c3_sixShearAut (e' k)))
    (i : ZMod 3) (k : K) :
    MulAut.conjNormal (H := K) (y' ^ i.val) k =
      e'.symm ((order81_c9c3_sixShearAut ^ i.val) (e' k)) := by
  have hv0 : (0 : ZMod 3).val = 0 := rfl
  have hv1 : (1 : ZMod 3).val = 1 := rfl
  have hv2 : (2 : ZMod 3).val = 2 := rfl
  rcases order81_caseB_zmod3_cases i with hi | hi | hi <;> subst hi
  · rw [hv0]; simp
  · rw [hv1]; simpa using haction k
  · rw [hv2]
    have h1 : MulAut.conjNormal (H := K) (y' ^ 2) k =
        MulAut.conjNormal (H := K) y' (MulAut.conjNormal (H := K) y' k) := by
      rw [sq]
      exact order81_caseB_conjNormal_mul y' y' k
    rw [h1, haction, haction, MulEquiv.apply_symm_apply, sq]
    rfl

/-- The pointwise additive-side pairing of an element of `order81_C9C3`. -/
noncomputable def order81_caseB_fromAddPair (n : order81_C9C3Add) : order81_C9C3 :=
  (Multiplicative.ofAdd n.1, Multiplicative.ofAdd n.2)

@[simp] theorem order81_caseB_fromAddPair_add (a b : order81_C9C3Add) :
    order81_caseB_fromAddPair (a + b) =
      order81_caseB_fromAddPair a * order81_caseB_fromAddPair b := by
  ext <;> simp [order81_caseB_fromAddPair]

@[simp] theorem order81_caseB_fromAddPair_zero :
    order81_caseB_fromAddPair 0 = 1 := rfl

theorem order81_caseB_fromAddPair_nonSplitTwist :
    order81_caseB_fromAddPair order81_c9c3_nonSplitTwist = order81_C9C3_cubeGen := rfl

/-- The `t`-component exponents of the `nonSplit_rep` multiplication satisfy the same
carry arithmetic as natural-number powers of a fixed order-`9` element. -/
theorem order81_caseB_val_add_eq (t t' : ZMod 3) :
    t.val + t'.val = 3 * (if 3 ≤ t.val + t'.val then 1 else 0) + (t + t').val := by
  fin_cases t <;> fin_cases t' <;> decide

/-- `fromAddPair` intertwines `sixShearAddEquiv` with `sixShearAut`. -/
theorem order81_caseB_fromAddPair_sixShear (v : order81_C9C3Add) :
    order81_caseB_fromAddPair (order81_c9c3_sixShearAddEquiv v) =
      order81_c9c3_sixShearAut (order81_caseB_fromAddPair v) := by
  rcases v with ⟨a, b⟩
  rfl

/-- The `nonSplitAct` iterate of the intertwining, matching `order81_c9c3_nonSplitAct`'s
own `t = 0, 1, 2` case definition. -/
theorem order81_caseB_fromAddPair_nonSplitAct (t : ZMod 3) (v : order81_C9C3Add) :
    order81_caseB_fromAddPair (order81_c9c3_nonSplitAct t v) =
      (order81_c9c3_sixShearAut ^ t.val) (order81_caseB_fromAddPair v) := by
  have hv0 : (0 : ZMod 3).val = 0 := rfl
  have hv1 : (1 : ZMod 3).val = 1 := rfl
  have hv2 : (2 : ZMod 3).val = 2 := rfl
  rcases order81_caseB_zmod3_cases t with ht | ht | ht <;> subst ht
  · rw [hv0, pow_zero]
    simp [order81_c9c3_nonSplitAct]
  · rw [hv1, pow_one, show order81_c9c3_nonSplitAct 1 v = order81_c9c3_sixShearAddEquiv v by
      simp [order81_c9c3_nonSplitAct]]
    exact order81_caseB_fromAddPair_sixShear v
  · rw [hv2, sq, MulAut.mul_apply,
      show order81_c9c3_nonSplitAct 2 v =
        order81_c9c3_sixShearAddEquiv (order81_c9c3_sixShearAddEquiv v) by
        simp only [order81_c9c3_nonSplitAct]
        rw [if_neg (by decide), if_neg (by decide)]
        rfl,
      order81_caseB_fromAddPair_sixShear, order81_caseB_fromAddPair_sixShear]

/-- **Case B2, final construction.** Given a case-B setting where the transported
conjugation action of an outside order-`9` element `y'` is exactly `sixShearAut`, and the
cube of `y'` matches the standard `nonSplit_rep` twist, `G ≅ order81_c9c3_nonSplit_rep`. -/
theorem order81_caseB_nonSplit_of_sixShear_action
    {G : Type*} [Group G] {K : Subgroup G} [K.Normal]
    (hcard : Nat.card G = 81) (hKcard : Nat.card K = 27)
    (_hns : ∀ z : G, z ∉ K → z ^ 3 ≠ 1)
    {y' : G} (hy'K : y' ∉ K) (_hy'9 : y' ^ 9 = 1)
    (e' : K ≃* order81_C9C3)
    (haction : ∀ k : K, MulAut.conjNormal (H := K) y' k =
      e'.symm (order81_c9c3_sixShearAut (e' k)))
    (hcube : e' ⟨y' ^ 3, order81_cube_mem_of_normal_subgroup_card_27 hcard hKcard y'⟩ =
      order81_C9C3_cubeGen) :
    Nonempty (G ≃* order81_c9c3_nonSplit_rep) := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  -- value-level form of the iterated action, for any `i : ZMod 3`
  have hval_conj : ∀ (i : ZMod 3) (k : K),
      y' ^ i.val * k.1 * (y' ^ i.val)⁻¹ =
        (e'.symm ((order81_c9c3_sixShearAut ^ i.val) (e' k))).1 := by
    intro i k
    have h := order81_caseB_action_iterate (y' := y') (e' := e') haction i k
    exact congrArg Subtype.val h
  -- the cube, as a `G`-value
  set k9 : K := ⟨y' ^ 3, order81_cube_mem_of_normal_subgroup_card_27 hcard hKcard y'⟩
    with hk9def
  have hk9val : (e'.symm order81_C9C3_cubeGen).1 = y' ^ 3 := by
    rw [← hcube]
    show (e'.symm (e' k9)).1 = y' ^ 3
    rw [MulEquiv.symm_apply_apply]
  -- the homomorphism `Ψ : nonSplit_rep →* G`
  set Ψ : order81_c9c3_nonSplit_rep →* G := MonoidHom.mk'
      (fun x => e'.symm (order81_caseB_fromAddPair x.n) * y' ^ x.t.val)
      (by
        intro x y
        change e'.symm (order81_caseB_fromAddPair (x * y).n) * y' ^ ((x * y).t.val) =
          e'.symm (order81_caseB_fromAddPair x.n) * y' ^ x.t.val *
            (e'.symm (order81_caseB_fromAddPair y.n) * y' ^ y.t.val)
        rw [Order81C9C3NonSplit.mul_n, Order81C9C3NonSplit.mul_t,
          order81_caseB_fromAddPair_add, order81_caseB_fromAddPair_add, map_mul, map_mul,
          order81_caseB_fromAddPair_nonSplitAct]
        -- move `y'^x.t.val` past `e'.symm (fromAddPair y.n)`
        have hmove : e'.symm ((order81_c9c3_sixShearAut ^ x.t.val)
            (order81_caseB_fromAddPair y.n)) * y' ^ x.t.val =
            y' ^ x.t.val * e'.symm (order81_caseB_fromAddPair y.n) := by
          have hv := hval_conj x.t (e'.symm (order81_caseB_fromAddPair y.n))
          rw [MulEquiv.apply_symm_apply] at hv
          have : (e'.symm ((order81_c9c3_sixShearAut ^ x.t.val)
              (order81_caseB_fromAddPair y.n))).1 =
              y' ^ x.t.val * (e'.symm (order81_caseB_fromAddPair y.n)).1 *
                (y' ^ x.t.val)⁻¹ := hv.symm
          have h2 := congrArg (· * y' ^ x.t.val) this
          simp only [inv_mul_cancel_right] at h2
          exact h2
        -- carry bookkeeping
        have hcarry : (e'.symm (order81_caseB_fromAddPair
            (order81_c9c3_nonSplitCarry x.t y.t))).1 * y' ^ (x.t + y.t).val =
            y' ^ (x.t.val + y.t.val) := by
          unfold order81_c9c3_nonSplitCarry
          by_cases hle : 3 ≤ x.t.val + y.t.val
          · rw [if_pos hle, order81_caseB_fromAddPair_nonSplitTwist, hk9val,
              order81_caseB_val_add_eq x.t y.t, if_pos hle]
            rw [pow_add, pow_mul, pow_one]
          · rw [if_neg hle]
            have h0 : order81_caseB_fromAddPair (0 : order81_C9C3Add) = 1 := rfl
            rw [h0, map_one, order81_caseB_val_add_eq x.t y.t, if_neg hle]
            simp
        rw [Subgroup.coe_mul, Subgroup.coe_mul,
          mul_assoc (e'.symm (order81_caseB_fromAddPair x.n) : G)]
        calc (e'.symm (order81_caseB_fromAddPair x.n) : G) *
              (e'.symm ((order81_c9c3_sixShearAut ^ x.t.val) (order81_caseB_fromAddPair y.n)) *
                e'.symm (order81_caseB_fromAddPair (order81_c9c3_nonSplitCarry x.t y.t))) *
              y' ^ (x.t + y.t).val
            = e'.symm (order81_caseB_fromAddPair x.n) *
              e'.symm ((order81_c9c3_sixShearAut ^ x.t.val) (order81_caseB_fromAddPair y.n)) *
              ((e'.symm (order81_caseB_fromAddPair (order81_c9c3_nonSplitCarry x.t y.t))).1 *
                y' ^ (x.t + y.t).val) := by
              group
          _ = e'.symm (order81_caseB_fromAddPair x.n) *
              e'.symm ((order81_c9c3_sixShearAut ^ x.t.val) (order81_caseB_fromAddPair y.n)) *
              y' ^ (x.t.val + y.t.val) := by rw [hcarry]
          _ = e'.symm (order81_caseB_fromAddPair x.n) *
              e'.symm ((order81_c9c3_sixShearAut ^ x.t.val) (order81_caseB_fromAddPair y.n)) *
              (y' ^ x.t.val * y' ^ y.t.val) := by rw [pow_add]
          _ = e'.symm (order81_caseB_fromAddPair x.n) *
              (e'.symm ((order81_c9c3_sixShearAut ^ x.t.val) (order81_caseB_fromAddPair y.n)) *
                y' ^ x.t.val) *
              y' ^ y.t.val := by group
          _ = e'.symm (order81_caseB_fromAddPair x.n) *
              (y' ^ x.t.val * e'.symm (order81_caseB_fromAddPair y.n)) *
              y' ^ y.t.val := by rw [hmove]
          _ = e'.symm (order81_caseB_fromAddPair x.n) * y' ^ x.t.val *
              (e'.symm (order81_caseB_fromAddPair y.n) * y' ^ y.t.val) := by
              group)
  have hfromAddPair_inj : Function.Injective order81_caseB_fromAddPair := by
    intro a b hab
    have h1 := congrArg Prod.fst hab
    have h2 := congrArg Prod.snd hab
    simp only [order81_caseB_fromAddPair] at h1 h2
    exact Prod.ext (Multiplicative.ofAdd.injective h1) (Multiplicative.ofAdd.injective h2)
  have hinj : Function.Injective Ψ := by
    intro x y hxy
    have h : (e'.symm (order81_caseB_fromAddPair x.n)).1 * y' ^ x.t.val =
        (e'.symm (order81_caseB_fromAddPair y.n)).1 * y' ^ y.t.val := hxy
    obtain ⟨hij, hkl⟩ := order81_caseB_normal_form_unique hcard hKcard hy'K h
    have hnn : x.n = y.n := hfromAddPair_inj (e'.symm.injective hkl)
    exact Order81C9C3NonSplit.ext hnn hij
  haveI : Finite order81_c9c3_nonSplit_rep :=
    Nat.finite_of_card_ne_zero (by rw [card_order81_c9c3_nonSplit_rep]; norm_num)
  have hbij : Function.Bijective Ψ :=
    (Nat.bijective_iff_injective_and_card Ψ).mpr ⟨hinj, by
      rw [card_order81_c9c3_nonSplit_rep, hcard]⟩
  exact ⟨(MulEquiv.ofBijective Ψ hbij).symm⟩

/-! ### Connecting the reduction lemma to the final construction -/

/-- The inversion automorphism of `order81_C9C3` (well-defined since the group is
abelian). -/
noncomputable def order81_caseB_negAut : MulAut order81_C9C3 where
  toFun x := x⁻¹
  invFun x := x⁻¹
  left_inv := inv_inv
  right_inv := inv_inv
  map_mul' x y := by rw [mul_inv_rev, mul_comm]

theorem order81_caseB_negAut_comm_sixShear (x : order81_C9C3) :
    order81_caseB_negAut (order81_c9c3_sixShearAut (order81_caseB_negAut.symm x)) =
      order81_c9c3_sixShearAut x := by
  fin_cases x <;> decide

theorem order81_caseB_negAut_cubeGen :
    order81_caseB_negAut order81_C9C3_cubeGen =
      (Multiplicative.ofAdd (6 : ZMod 9), 1) := by
  decide

theorem order81_caseB_negAut_of_six :
    order81_caseB_negAut (Multiplicative.ofAdd (6 : ZMod 9), (1 : Multiplicative (ZMod 3))) =
      order81_C9C3_cubeGen := by
  decide

theorem order81_caseB_negAut_symm_eq : order81_caseB_negAut.symm = order81_caseB_negAut := rfl

/-- The fixed points of `sixShearAut` are exactly the elements of the order-`3` cube
subgroup. -/
theorem order81_caseB_sixShear_fix_cases (w : order81_C9C3)
    (h : order81_c9c3_sixShearAut w = w) :
    w = 1 ∨ w = order81_C9C3_cubeGen ∨ w = (Multiplicative.ofAdd (6 : ZMod 9), 1) := by
  revert h
  revert w
  decide +kernel

/-- Given the outputs of the marker dichotomy and the `sixShear`-reduction, `G` is
isomorphic to the non-split representative. -/
theorem order81_caseB_of_param_marker
    {G : Type*} [Group G] {K : Subgroup G} [K.Normal]
    (hcard : Nat.card G = 81) (hKcard : Nat.card K = 27)
    (e : K ≃* order81_C9C3)
    (_hKcomm : ∀ a b : K, a * b = b * a)
    (hns : ∀ z : G, z ∉ K → z ^ 3 ≠ 1)
    {y : G} (hyK : y ∉ K) (hy9 : y ^ 9 = 1)
    (r s t : ZMod 3)
    (hparam : e.symm.trans ((MulAut.conjNormal (H := K) y).trans e) =
      order81_c9c3_paramAut r s t)
    (hs : s ≠ 0) (ht : t ≠ 0) (hst : s ≠ t) :
    Nonempty (G ≃* order81_c9c3_nonSplit_rep) := by
  have hval : ∀ k : K, MulAut.conjNormal (H := K) y k =
      e.symm (order81_c9c3_paramAut r s t (e k)) := by
    intro k
    have h1 : order81_c9c3_paramAut r s t (e k) =
        (e.symm.trans ((MulAut.conjNormal (H := K) y).trans e)) (e k) := by rw [hparam]
    rw [h1]
    simp
  obtain ⟨n, φ, hn, hφ⟩ := order81_caseB_paramAut_reduce_to_sixShear r s t hs ht hst
  set y' : G := y ^ n with hy'def
  have hy'9 : y' ^ 9 = 1 := by
    rw [hy'def, ← pow_mul, mul_comm, pow_mul, hy9, one_pow]
  have hy'K : y' ∉ K := by
    intro hmem
    have hmemz : y ^ (n : ℤ) ∈ K := by rw [zpow_natCast]; exact hmem
    have h3 := (order81_caseB_zpow_mem_iff hcard hKcard hyK (n : ℤ)).mp hmemz
    rcases hn with hn1 | hn2
    · rw [hn1] at h3; norm_num at h3
    · rw [hn2] at h3; norm_num at h3
  set e' : K ≃* order81_C9C3 := e.trans φ with he'def
  have haction : ∀ k : K, MulAut.conjNormal (H := K) y' k =
      e'.symm (order81_c9c3_sixShearAut (e' k)) := by
    intro k
    rcases hn with hn1 | hn2
    · subst hn1
      have hy' : y' = y := by rw [hy'def, pow_one]
      rw [hy', hval k, he'def, MulEquiv.trans_apply, MulEquiv.symm_trans_apply]
      congr 1
      have hφ1 : φ (order81_c9c3_paramAut r s t (e k)) =
          order81_c9c3_sixShearAut (φ (e k)) := by
        have h1 := congrArg (fun f => f (φ (e k))) hφ
        simp only [pow_one] at h1
        rw [MulAut.conj_apply] at h1
        rwa [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
          at h1
      rw [← hφ1, MulEquiv.symm_apply_apply]
    · subst hn2
      have hy' : y' = y * y := by rw [hy'def, sq]
      have hconj2 : MulAut.conjNormal (H := K) y' k =
          MulAut.conjNormal (H := K) y (MulAut.conjNormal (H := K) y k) := by
        rw [hy']
        exact order81_caseB_conjNormal_mul y y k
      rw [hconj2, hval k, hval (e.symm (order81_c9c3_paramAut r s t (e k)))]
      simp only [MulEquiv.apply_symm_apply]
      rw [he'def, MulEquiv.trans_apply, MulEquiv.symm_trans_apply]
      congr 1
      have hφ2 : φ ((order81_c9c3_paramAut r s t) ((order81_c9c3_paramAut r s t) (e k))) =
          order81_c9c3_sixShearAut (φ (e k)) := by
        have h2 := congrArg (fun f => f (φ (e k))) hφ
        rw [MulAut.conj_apply] at h2
        rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply,
          sq, MulAut.mul_apply] at h2
        exact h2
      rw [← hφ2, MulEquiv.symm_apply_apply]
  -- twist adjustment
  set k9' : K := ⟨y' ^ 3, order81_cube_mem_of_normal_subgroup_card_27 hcard hKcard y'⟩
    with hk9'def
  by_cases htwist : e' k9' = order81_C9C3_cubeGen
  · exact order81_caseB_nonSplit_of_sixShear_action hcard hKcard hns hy'K hy'9 e' haction htwist
  · set e'' : K ≃* order81_C9C3 := e'.trans order81_caseB_negAut with he''def
    have haction' : ∀ k : K, MulAut.conjNormal (H := K) y' k =
        e''.symm (order81_c9c3_sixShearAut (e'' k)) := by
      intro k
      rw [he''def]
      change MulAut.conjNormal (H := K) y' k =
        e'.symm (order81_caseB_negAut.symm
          (order81_c9c3_sixShearAut (order81_caseB_negAut (e' k))))
      have hcomm : order81_caseB_negAut.symm
          (order81_c9c3_sixShearAut (order81_caseB_negAut (e' k))) =
          order81_c9c3_sixShearAut (e' k) := by
        rw [order81_caseB_negAut_symm_eq]
        exact order81_caseB_negAut_comm_sixShear (e' k)
      rw [hcomm]
      exact haction k
    have htwist' : e'' k9' = order81_C9C3_cubeGen := by
      have hk9'fix : MulAut.conjNormal (H := K) y' k9' = k9' := by
        apply Subtype.ext
        change y' * y' ^ 3 * y'⁻¹ = y' ^ 3
        group
      have heq : k9' = e'.symm (order81_c9c3_sixShearAut (e' k9')) := by
        conv_lhs => rw [← hk9'fix]
        exact haction k9'
      have hmemFix : order81_c9c3_sixShearAut (e' k9') = e' k9' := by
        have h1 := congrArg e' heq
        rw [MulEquiv.apply_symm_apply] at h1
        exact h1.symm
      have hcases := order81_caseB_sixShear_fix_cases (e' k9') hmemFix
      rcases hcases with h1 | h | h
      · exfalso
        apply hns y' hy'K
        have hk9'1 : k9' = 1 := e'.injective (by rw [h1, map_one])
        have := congrArg Subtype.val hk9'1
        simpa [hk9'def] using this
      · exact absurd h htwist
      · rw [he''def]
        change order81_caseB_negAut (e' k9') = order81_C9C3_cubeGen
        rw [h]
        exact order81_caseB_negAut_of_six
    exact order81_caseB_nonSplit_of_sixShear_action hcard hKcard hns hy'K hy'9 e'' haction' htwist'

/-- **Case-B dispatcher, fully closed.** Every non-abelian, non-split extension of `G`
over a `C_9 × C_3` kernel with no element of order `27` is isomorphic to `C_9 ⋊ C_9` or
to the non-split representative. -/
theorem order81_caseB_dispatch
    {G : Type*} [Group G] {K : Subgroup G} [K.Normal]
    (hcard : Nat.card G = 81) (hKcard : Nat.card K = 27)
    (e : K ≃* order81_C9C3)
    (hKcomm : ∀ a b : K, a * b = b * a)
    (hns : ∀ z : G, z ∉ K → z ^ 3 ≠ 1)
    (h27 : ∀ g : G, orderOf g ≠ 27)
    (hnoncomm : ¬ ∀ a b : G, a * b = b * a)
    {y : G} (hyK : y ∉ K) (hy9 : y ^ 9 = 1) :
    Nonempty (G ≃* order81_c9_semidirect_c9_rep) ∨
      Nonempty (G ≃* order81_c9c3_nonSplit_rep) := by
  rcases order81_caseB_c9c9_or_param_marker hcard hKcard e hKcomm hns h27 hnoncomm hyK hy9
    with hc9c9 | ⟨r, s, t, hs, ht, hst, hparam⟩
  · exact Or.inl hc9c9
  · exact Or.inr (order81_caseB_of_param_marker hcard hKcard e hKcomm hns hyK hy9 r s t
      hparam hs ht hst)

/-! ### Final assembly: exhaustiveness and `IsClassif 81` -/

/-- Every non-abelian group of order `81` is isomorphic to one of the ten certified
non-abelian representatives. -/
theorem order81_nonabelian_complete
    (G : Type*) [Group G] (hcard : Nat.card G = 81) (hnoncomm : ¬ IsMulCommutative G) :
    ∃ i : Fin 9 ⊕ Fin 1, Nonempty (G ≃* order81_nonabelian_reps i) := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  rcases order81_nonabelian_cases_or_c9c3_nonsplit_no27 G hcard hnoncomm with
    h8 | ⟨⟨K, hKnorm, hKcard, ⟨e⟩, hns⟩, h27⟩
  · rcases h8 with h | h | h | h | h | h | h | h
    · exact ⟨Sum.inl 0, h⟩
    · exact ⟨Sum.inl 5, h⟩
    · exact ⟨Sum.inl 1, h⟩
    · exact ⟨Sum.inl 2, h⟩
    · exact ⟨Sum.inl 6, h⟩
    · exact ⟨Sum.inl 7, h⟩
    · exact ⟨Sum.inl 8, h⟩
    · exact ⟨Sum.inl 3, h⟩
  · haveI : K.Normal := hKnorm
    have hKcomm : ∀ a b : K, a * b = b * a := by
      intro a b
      apply e.injective
      rw [map_mul, map_mul, mul_comm]
    have hne : K ≠ ⊤ := by
      intro htop
      rw [htop, Subgroup.card_top, hcard] at hKcard
      norm_num at hKcard
    obtain ⟨y, hyK⟩ : ∃ y : G, y ∉ K := by
      by_contra hall
      push Not at hall
      apply hne
      ext x
      simp [hall x]
    have hy9 : y ^ 9 = 1 := by
      have hord := order81_caseB_orderOf_eq_nine hcard hKcard hns h27 hyK
      rw [← hord]
      exact pow_orderOf_eq_one y
    have hnoncomm' : ¬ ∀ a b : G, a * b = b * a := by
      intro h
      exact hnoncomm (IsMulCommutative.of_comm h)
    rcases order81_caseB_dispatch hcard hKcard e hKcomm hns h27 hnoncomm' hyK hy9 with
      hc9c9 | hnonsplit
    · exact ⟨Sum.inl 4, hc9c9⟩
    · exact ⟨Sum.inr 0, hnonsplit⟩

/-- Every group of order `81` is isomorphic to one of the fifteen certified
representatives. -/
theorem order81_complete (G : Type) [Group G] (hcard : Nat.card G = 81) :
    ∃ i, Nonempty (G ≃* order81_reps i) := by
  by_cases hcomm : ∀ a b : G, a * b = b * a
  · letI : CommGroup G := { mul_comm := hcomm }
    obtain ⟨i, hi⟩ := order81_abelian_complete G hcard
    refine ⟨order81_fin15Equiv.symm (Sum.inl i), ?_⟩
    have heq : order81_fin15Equiv (order81_fin15Equiv.symm (Sum.inl i)) = Sum.inl i :=
      order81_fin15Equiv.apply_symm_apply _
    exact cast (congrArg (fun j => Nonempty (G ≃* order81_known_reps j)) heq.symm) hi
  · have hnoncomm : ¬ IsMulCommutative G := by
      intro h
      exact hcomm h.is_comm.comm
    obtain ⟨i, hi⟩ := order81_nonabelian_complete G hcard hnoncomm
    refine ⟨order81_fin15Equiv.symm (Sum.inr i), ?_⟩
    have heq : order81_fin15Equiv (order81_fin15Equiv.symm (Sum.inr i)) = Sum.inr i :=
      order81_fin15Equiv.apply_symm_apply _
    exact cast (congrArg (fun j => Nonempty (G ≃* order81_known_reps j)) heq.symm) hi

/-- **The full classification of groups of order `81`.** -/
theorem order81_isClassif : IsClassif 81 order81_reps where
  card := card_order81_reps
  complete := order81_complete
  distinct := order81_reps_pairwise

end Smallgroups.UsefulTheorems
