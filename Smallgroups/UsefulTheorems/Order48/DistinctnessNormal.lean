/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.UniqueSylowThree_Summary

/-!
# Distinctness in the unique-Sylow-three branch of order 48

This file starts the invariant layer for the `42` representatives assembled in
`UniqueSylowThree_Summary`.  Kernel cardinality separates the direct product
(trivial action) from every nontrivial action for each of the fourteen
complements.  Orders of elements inside the character kernel then separate the
remaining action types whose kernels have equal cardinality; the first concrete
applications cover `C₈ × C₂`, `C₄ × C₂ × C₂`, and `Q₁₆`.
-/

namespace Smallgroups.UsefulTheorems

theorem order48_mulAut_c3_fixing_gen_eq_one
    (σ : MulAut (Multiplicative (ZMod 3)))
    (h : σ (Multiplicative.ofAdd (1 : ZMod 3)) =
      Multiplicative.ofAdd (1 : ZMod 3)) : σ = 1 := by
  have heq : σ.toMonoidHom =
      (1 : MulAut (Multiplicative (ZMod 3))).toMonoidHom :=
    multiplicative_zmod_hom_ext (by simpa using h)
  ext x
  exact DFunLike.congr_fun heq x

theorem order48_c3_zpowers_eq_top_of_orderOf_eq_three
    {n : Multiplicative (ZMod 3)} (hn : orderOf n = 3) :
    Subgroup.zpowers n = ⊤ := by
  have hcard : Nat.card (Subgroup.zpowers n) =
      Nat.card (Multiplicative (ZMod 3)) := by
    rw [Nat.card_zpowers, hn, Nat.card_eq_fintype_card]
    decide
  have hmulindex := (Subgroup.zpowers n).card_mul_index
  rw [hcard] at hmulindex
  have hgroup : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [hgroup] at hmulindex
  have hindex : (Subgroup.zpowers n).index = 1 :=
    Nat.eq_of_mul_eq_mul_left (show 0 < 3 by norm_num)
      (hmulindex.trans (by norm_num))
  exact Subgroup.index_eq_one.mp hindex

theorem order48_mulAut_c3_fixing_ord3_eq_one
    {n : Multiplicative (ZMod 3)} (hn : orderOf n = 3)
    (σ : MulAut (Multiplicative (ZMod 3))) (h : σ n = n) : σ = 1 := by
  have htop := order48_c3_zpowers_eq_top_of_orderOf_eq_three hn
  have hmem : Multiplicative.ofAdd (1 : ZMod 3) ∈ Subgroup.zpowers n :=
    htop ▸ Subgroup.mem_top _
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
  apply order48_mulAut_c3_fixing_gen_eq_one
  rw [← hj, map_zpow, h]

theorem order48_inl_gen_commute_iff {K : Type*} [Group K]
    {φ : K →* MulAut (Multiplicative (ZMod 3))}
    {n0 : Multiplicative (ZMod 3)} (hn0 : orderOf n0 = 3)
    (x : SemidirectProduct (Multiplicative (ZMod 3)) K φ) :
    Commute (SemidirectProduct.inl n0 :
      SemidirectProduct (Multiplicative (ZMod 3)) K φ) x ↔
      φ (SemidirectProduct.rightHom x) = 1 := by
  constructor
  · intro hc
    apply order48_mulAut_c3_fixing_ord3_eq_one hn0
    have hleft := congrArg SemidirectProduct.left hc
    simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, map_one, MulAut.one_apply] at hleft
    have hcancel : x.left * n0 = x.left * φ x.right n0 := by
      rw [mul_comm]
      exact hleft
    exact (mul_left_cancel hcancel).symm
  · intro hφ
    apply SemidirectProduct.ext
    · simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
        SemidirectProduct.right_inl, map_one, MulAut.one_apply,
        SemidirectProduct.rightHom_eq_right] at hφ ⊢
      rw [hφ, MulAut.one_apply, mul_comm]
    · simp

theorem order48_ord3_elt_eq_inl {K : Type*} [Group K] [Fintype K]
    (hK : Nat.Coprime 3 (Fintype.card K))
    {φ : K →* MulAut (Multiplicative (ZMod 3))}
    {x : SemidirectProduct (Multiplicative (ZMod 3)) K φ}
    (hxord : orderOf x = 3) :
    ∃ n : Multiplicative (ZMod 3), x = SemidirectProduct.inl n ∧ orderOf n = 3 := by
  have hdvdThree : orderOf (SemidirectProduct.rightHom x) ∣ 3 := by
    have h := orderOf_map_dvd SemidirectProduct.rightHom x
    rwa [hxord] at h
  have hdvdK : orderOf (SemidirectProduct.rightHom x) ∣ Fintype.card K :=
    orderOf_dvd_card
  have hgcd : orderOf (SemidirectProduct.rightHom x) ∣
      Nat.gcd 3 (Fintype.card K) := Nat.dvd_gcd hdvdThree hdvdK
  rw [hK] at hgcd
  have hright : SemidirectProduct.rightHom x = 1 :=
    orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgcd)
  have hxeq : x = SemidirectProduct.inl x.left := by
    apply SemidirectProduct.ext
    · simp
    · simpa [SemidirectProduct.rightHom_eq_right] using hright
  refine ⟨x.left, hxeq, ?_⟩
  have h := hxord
  rw [hxeq, orderOf_injective _ SemidirectProduct.inl_injective] at h
  exact h

theorem order48_inl_inr_commute_of_ker {K : Type*} [Group K]
    {φ : K →* MulAut (Multiplicative (ZMod 3))} {k : K} (hk : φ k = 1)
    (a : Multiplicative (ZMod 3)) :
    Commute (SemidirectProduct.inl a :
      SemidirectProduct (Multiplicative (ZMod 3)) K φ)
      (SemidirectProduct.inr k) := by
  apply SemidirectProduct.ext
  · simp [hk]
  · simp

theorem order48_pow_three_eq_one_c3 (x : Multiplicative (ZMod 3)) :
    x ^ 3 = 1 := by
  revert x
  decide

/-- A centralizing element whose order is prime to `3` lies in the complement,
and its complement component lies in the character kernel. -/
theorem order48_centralizer_elt_decomp {K : Type*} [Group K] [Fintype K]
    (hK : Nat.Coprime 3 (Fintype.card K)) {χ : K →* (ZMod 3)ˣ}
    {n0 : Multiplicative (ZMod 3)} (hn0 : orderOf n0 = 3)
    {d : Nat} (hd : ¬ 3 ∣ d)
    {x : SemidirectProduct (Multiplicative (ZMod 3)) K (order48_action χ)}
    (hx : Commute (SemidirectProduct.inl n0) x) (hxord : orderOf x = d) :
    x.left = 1 ∧ χ (SemidirectProduct.rightHom x) = 1 ∧
      orderOf (SemidirectProduct.rightHom x) = d := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hmem : χ (SemidirectProduct.rightHom x) = 1 := by
    have h := (order48_inl_gen_commute_iff hn0 x).mp hx
    rwa [MonoidHom.comp_apply, ← MonoidHom.map_one unitAutHom,
      Function.Injective.eq_iff (unitAutHom_injective (p := 3))] at h
  have hcommute : Commute
      (SemidirectProduct.inl x.left :
        SemidirectProduct (Multiplicative (ZMod 3)) K (order48_action χ))
      (SemidirectProduct.inr (SemidirectProduct.rightHom x)) :=
    order48_inl_inr_commute_of_ker
      (by rw [MonoidHom.comp_apply, hmem, map_one]) _
  have hdecomp : x = SemidirectProduct.inl x.left *
      SemidirectProduct.inr (SemidirectProduct.rightHom x) := by
    rw [SemidirectProduct.rightHom_eq_right,
      SemidirectProduct.inl_left_mul_inr_right]
  have hleftDvd : orderOf x.left ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (order48_pow_three_eq_one_c3 _)
  have hrightDvd : orderOf (SemidirectProduct.rightHom x) ∣
      Fintype.card K := orderOf_dvd_card
  have hrightCoprime : Nat.gcd 3 (orderOf (SemidirectProduct.rightHom x)) = 1 := by
    have hstep : Nat.gcd 3 (orderOf (SemidirectProduct.rightHom x)) ∣
        Nat.gcd 3 (Fintype.card K) :=
      Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
        ((Nat.gcd_dvd_right _ _).trans hrightDvd)
    rw [hK] at hstep
    exact Nat.dvd_one.mp hstep
  have hcop : Nat.Coprime (orderOf x.left)
      (orderOf (SemidirectProduct.rightHom x)) := by
    rcases (Nat.dvd_prime (by norm_num)).mp hleftDvd with h | h
    · rw [h]
      exact Nat.coprime_one_left _
    · rw [h]
      exact hrightCoprime
  have hord : orderOf x =
      orderOf x.left * orderOf (SemidirectProduct.rightHom x) := by
    conv_lhs => rw [hdecomp]
    rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime hcommute
      (by
        rw [orderOf_injective _ SemidirectProduct.inl_injective,
          orderOf_injective _ SemidirectProduct.inr_injective]
        exact hcop)]
    rw [orderOf_injective _ SemidirectProduct.inl_injective,
      orderOf_injective _ SemidirectProduct.inr_injective]
  rw [hxord] at hord
  have hleft : x.left = 1 := by
    rcases (Nat.dvd_prime (by norm_num)).mp hleftDvd with h | h
    · exact orderOf_eq_one_iff.mp h
    · exfalso
      apply hd
      rw [hord, h]
      exact ⟨_, rfl⟩
  refine ⟨hleft, hmem, ?_⟩
  rw [hleft, orderOf_one, one_mul] at hord
  exact hord.symm

/-- An element order occurring in one character kernel but not another
distinguishes the associated order-`48` semidirect products. -/
theorem order48_ne_of_ker_order {K : Type*} [Group K] [Fintype K]
    (hK : Nat.Coprime 3 (Fintype.card K)) {χ χ' : K →* (ZMod 3)ˣ}
    {d : Nat} (hd : ¬ 3 ∣ d)
    (h1 : ∃ k : K, χ k = 1 ∧ orderOf k = d)
    (h2 : ∀ k : K, χ' k = 1 → orderOf k ≠ d) :
    IsEmpty (SemidirectProduct (Multiplicative (ZMod 3)) K (order48_action χ) ≃*
      SemidirectProduct (Multiplicative (ZMod 3)) K (order48_action χ')) := by
  constructor
  intro e
  obtain ⟨k, hk, hkord⟩ := h1
  let n0 : Multiplicative (ZMod 3) := Multiplicative.ofAdd (1 : ZMod 3)
  have hn0 : orderOf n0 = 3 := by
    simp [n0, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  have haction : order48_action χ k = 1 := by
    rw [order48_action, MonoidHom.comp_apply, hk, map_one]
  have hcommute : Commute
      (SemidirectProduct.inl n0 :
        SemidirectProduct (Multiplicative (ZMod 3)) K (order48_action χ))
      (SemidirectProduct.inr k) :=
    order48_inl_inr_commute_of_ker haction _
  have hinrord : orderOf (SemidirectProduct.inr k :
      SemidirectProduct (Multiplicative (ZMod 3)) K (order48_action χ)) = d := by
    rw [orderOf_injective _ SemidirectProduct.inr_injective]
    exact hkord
  have hcommute' := hcommute.map e
  have heord : orderOf (e (SemidirectProduct.inr k)) = d := by
    rw [MulEquiv.orderOf_eq]
    exact hinrord
  obtain ⟨n', hne, hn'⟩ := order48_ord3_elt_eq_inl hK
    (show orderOf (e (SemidirectProduct.inl n0)) = 3 by
      rw [MulEquiv.orderOf_eq, orderOf_injective _ SemidirectProduct.inl_injective]
      exact hn0)
  have hcommute'' : Commute
      (SemidirectProduct.inl n' :
        SemidirectProduct (Multiplicative (ZMod 3)) K (order48_action χ'))
      (e (SemidirectProduct.inr k)) := by
    rw [← hne]
    exact hcommute'
  obtain ⟨_, hker, hord⟩ :=
    order48_centralizer_elt_decomp hK hn' hd hcommute'' heord
  exact h2 _ hker hord

/-- Refine the centralizer invariant by recording the order of its elements. -/
theorem order48_card_centralizer_ord_eq {K : Type*} [Group K] [Fintype K]
    (hK : Nat.Coprime 3 (Fintype.card K)) {χ : K →* (ZMod 3)ˣ}
    {n0 : Multiplicative (ZMod 3)} (hn0 : orderOf n0 = 3)
    {d : Nat} (hd : ¬ 3 ∣ d) :
    Nat.card {x : SemidirectProduct (Multiplicative (ZMod 3)) K
        (order48_action χ) // Commute (SemidirectProduct.inl n0) x ∧
          orderOf x = d} =
      Nat.card {k : K // χ k = 1 ∧ orderOf k = d} := by
  apply Nat.card_congr
  refine
    { toFun := fun x => ⟨SemidirectProduct.rightHom x.1,
        (order48_centralizer_elt_decomp hK hn0 hd x.2.1 x.2.2).2⟩
      invFun := fun p => ⟨SemidirectProduct.inr p.1, ?_, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [order48_inl_gen_commute_iff hn0]
    simp [MonoidHom.comp_apply, p.2.1]
  · rw [orderOf_injective _ SemidirectProduct.inr_injective]
    exact p.2.2
  · rintro ⟨x, hx, hxord⟩
    obtain ⟨hleft, _, _⟩ :=
      order48_centralizer_elt_decomp hK hn0 hd hx hxord
    apply Subtype.ext
    have hdecomp := SemidirectProduct.inl_left_mul_inr_right x
    rw [hleft, map_one, one_mul] at hdecomp
    exact hdecomp
  · rintro ⟨k, hk, hkord⟩
    simp

/-- Different counts of kernel elements of a fixed order distinguish the
associated semidirect products. -/
theorem order48_ne_of_ker_ord_count {K : Type*} [Group K] [Fintype K]
    (hK : Nat.Coprime 3 (Fintype.card K)) {χ χ' : K →* (ZMod 3)ˣ}
    {d : Nat} (hd : ¬ 3 ∣ d)
    (hcard : Nat.card {k : K // χ k = 1 ∧ orderOf k = d} ≠
      Nat.card {k : K // χ' k = 1 ∧ orderOf k = d}) :
    IsEmpty (SemidirectProduct (Multiplicative (ZMod 3)) K (order48_action χ) ≃*
      SemidirectProduct (Multiplicative (ZMod 3)) K (order48_action χ')) := by
  constructor
  intro e
  apply hcard
  let n0 : Multiplicative (ZMod 3) := Multiplicative.ofAdd (1 : ZMod 3)
  have hn0 : orderOf n0 = 3 := by
    simp [n0, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  have heord : orderOf (e (SemidirectProduct.inl n0)) = 3 := by
    rw [MulEquiv.orderOf_eq, orderOf_injective _ SemidirectProduct.inl_injective]
    exact hn0
  obtain ⟨n', hne, hn'⟩ := order48_ord3_elt_eq_inl hK heord
  have hequiv : {x : SemidirectProduct (Multiplicative (ZMod 3)) K
        (order48_action χ) // Commute (SemidirectProduct.inl n0) x ∧
          orderOf x = d} ≃
      {y : SemidirectProduct (Multiplicative (ZMod 3)) K
        (order48_action χ') // Commute (SemidirectProduct.inl n') y ∧
          orderOf y = d} :=
    Equiv.subtypeEquiv e (fun x => by
      constructor
      · rintro ⟨hcomm, hord⟩
        refine ⟨?_, ?_⟩
        · have hm := hcomm.map e
          rwa [hne] at hm
        · simp [hord]
      · rintro ⟨hcomm, hord⟩
        refine ⟨?_, ?_⟩
        · rw [← hne] at hcomm
          have hm := hcomm.map e.symm
          simpa using hm
        · simpa using hord)
  have hcardeq := Nat.card_congr hequiv
  rw [order48_card_centralizer_ord_eq hK hn0 hd,
    order48_card_centralizer_ord_eq hK hn' hd] at hcardeq
  exact hcardeq

theorem order48_orderOf_eq_two_iff {G : Type*} [Group G] {k : G} :
    orderOf k = 2 ↔ k ^ 2 = 1 ∧ k ≠ 1 := by
  constructor
  · intro h
    refine ⟨h ▸ pow_orderOf_eq_one k, ?_⟩
    intro hk
    rw [hk, orderOf_one] at h
    norm_num at h
  · rintro ⟨hsq, hne⟩
    have hdvd : orderOf k ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne
    · exact h

/-- Decidable form of the kernel order-`2` count invariant. -/
theorem order48_ne_of_ker_sq_count {K : Type*} [Group K] [Fintype K]
    (hK : Nat.Coprime 3 (Fintype.card K)) {χ χ' : K →* (ZMod 3)ˣ}
    (hcard : Nat.card {k : K // χ k = 1 ∧ k ^ 2 = 1 ∧ k ≠ 1} ≠
      Nat.card {k : K // χ' k = 1 ∧ k ^ 2 = 1 ∧ k ≠ 1}) :
    IsEmpty (SemidirectProduct (Multiplicative (ZMod 3)) K (order48_action χ) ≃*
      SemidirectProduct (Multiplicative (ZMod 3)) K (order48_action χ')) := by
  apply order48_ne_of_ker_ord_count hK (d := 2) (by norm_num)
  let e1 : {k : K // χ k = 1 ∧ orderOf k = 2} ≃
      {k : K // χ k = 1 ∧ k ^ 2 = 1 ∧ k ≠ 1} :=
    Equiv.subtypeEquivRight
      (fun k => and_congr_right_iff.mpr fun _ => order48_orderOf_eq_two_iff)
  let e2 : {k : K // χ' k = 1 ∧ orderOf k = 2} ≃
      {k : K // χ' k = 1 ∧ k ^ 2 = 1 ∧ k ≠ 1} :=
    Equiv.subtypeEquivRight
      (fun k => and_congr_right_iff.mpr fun _ => order48_orderOf_eq_two_iff)
  rw [Nat.card_congr e1, Nat.card_congr e2]
  exact hcard

theorem order48_orderOf_ne_of_half_pow_eq_one {G : Type*} [Group G]
    {x : G} {d : Nat} (hd : 2 ≤ d) (hpow : x ^ (d / 2) = 1) :
    orderOf x ≠ d := by
  intro heq
  have hdvd : orderOf x ∣ d / 2 := orderOf_dvd_of_pow_eq_one hpow
  rw [heq] at hdvd
  have hlt : d / 2 < d := Nat.div_lt_self (by omega) (by norm_num)
  have hpos : 0 < d / 2 := by omega
  exact absurd (Nat.le_of_dvd hpos hdvd) (by omega)

theorem order48_orderOf_eq_pow2_of {G : Type*} [Group G] {x : G}
    {d e : Nat} (hd : d = 2 ^ e) (_he : 1 ≤ e)
    (hpow : x ^ d = 1) (hhalf : x ^ (d / 2) ≠ 1) : orderOf x = d := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by rw [hd]; positivity) hpow
  intro p hp hpd
  rw [hd] at hpd
  have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow hpd
  have hpeq : p = 2 :=
    (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp2
  rwa [hpeq]

theorem order48_isEmpty_mulEquiv_symm {A B : Type*} [Mul A] [Mul B]
    (h : IsEmpty (A ≃* B)) : IsEmpty (B ≃* A) :=
  ⟨fun e => h.false e.symm⟩

/-! The first concrete nontrivial/nontrivial separations. -/

theorem order48_K1_a_orderOf :
    orderOf ((Multiplicative.ofAdd (1 : ZMod 8),
      (1 : Multiplicative (ZMod 2))) : order16_wild_G1) = 8 :=
  order48_orderOf_eq_pow2_of (e := 3) rfl (by norm_num) (by decide) (by decide)

/-- For `C₈ × C₂`, the two nontrivial reduced actions have kernels
`C₄ × C₂` and `C₈`, hence give non-isomorphic groups. -/
theorem order48_K1_ne_1_2 : IsEmpty
    (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G1
        (order48_action order48_K1_chi_1) ≃*
      SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G1
        (order48_action order48_K1_chi_2)) :=
  order48_isEmpty_mulEquiv_symm <| order48_ne_of_ker_order
    (K := order16_wild_G1) (χ := order48_K1_chi_2)
      (χ' := order48_K1_chi_1) (d := 8) (by decide) (by norm_num) (by
        exact ⟨(Multiplicative.ofAdd (1 : ZMod 8), 1), by decide,
          order48_K1_a_orderOf⟩) (by
        intro k hk
        exact order48_orderOf_ne_of_half_pow_eq_one (by norm_num)
          (show k ^ (8 / 2) = 1 by
            norm_num
            revert hk
            revert k
            decide))

theorem order48_K7_a_orderOf :
    orderOf (((Multiplicative.ofAdd (1 : ZMod 4),
      (1 : Multiplicative (ZMod 2))), (1 : Multiplicative (ZMod 2))) :
      order16_wild_G7) = 4 :=
  order48_orderOf_eq_pow2_of (e := 2) rfl (by norm_num) (by decide) (by decide)

/-- For `C₄ × C₂ × C₂`, the two nontrivial kernels are `C₂³` and
`C₄ × C₂`. -/
theorem order48_K7_ne_1_2 : IsEmpty
    (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G7
        (order48_action order48_K7_chi_1) ≃*
      SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G7
        (order48_action order48_K7_chi_2)) :=
  order48_isEmpty_mulEquiv_symm <| order48_ne_of_ker_order
    (K := order16_wild_G7) (χ := order48_K7_chi_2)
      (χ' := order48_K7_chi_1) (d := 4) (by decide) (by norm_num) (by
        exact ⟨((Multiplicative.ofAdd (1 : ZMod 4), 1), 1), by decide,
          order48_K7_a_orderOf⟩) (by
        intro k hk
        exact order48_orderOf_ne_of_half_pow_eq_one (by norm_num)
          (show k ^ (4 / 2) = 1 by
            norm_num
            revert hk
            revert k
            decide))

theorem order48_K5_a_orderOf :
    orderOf (QuaternionGroup.a (1 : ZMod (2 * 4)) : QuaternionGroup 4) = 8 :=
  order48_orderOf_eq_pow2_of (e := 3) rfl (by norm_num) (by decide) (by decide)

/-- The two nontrivial `Q₁₆` actions have kernels of types `C₈` and `Q₈`. -/
theorem order48_K5_ne_1_2 : IsEmpty
    (SemidirectProduct (Multiplicative (ZMod 3)) (QuaternionGroup 4)
        (order48_action order48_chiQ16_xa) ≃*
      SemidirectProduct (Multiplicative (ZMod 3)) (QuaternionGroup 4)
        (order48_action order48_chiQ16)) :=
  order48_ne_of_ker_order (K := QuaternionGroup 4)
    (χ := order48_chiQ16_xa) (χ' := order48_chiQ16)
      (d := 8) (by decide) (by norm_num) (by
        exact ⟨QuaternionGroup.a (1 : ZMod (2 * 4)), by decide,
          order48_K5_a_orderOf⟩) (by
        intro k hk
        exact order48_orderOf_ne_of_half_pow_eq_one (by norm_num)
          (show k ^ (8 / 2) = 1 by
            norm_num
            revert hk
            revert k
            decide))

/-! ### The `C₈ ⋊ C₂` complements -/

theorem order48_K2_g_orderOf :
    orderOf (SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 8)) :
      order16_wild_G2) = 8 :=
  order48_orderOf_eq_pow2_of (e := 3) rfl (by norm_num) (by decide) (by decide)

theorem order48_K2_ne_10_01 : IsEmpty
    (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G2
        (order48_action order48_K2_chi_10) ≃*
      SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G2
        (order48_action order48_K2_chi_01)) :=
  order48_isEmpty_mulEquiv_symm <| order48_ne_of_ker_order
    (K := order16_wild_G2) (χ := order48_K2_chi_01)
      (χ' := order48_K2_chi_10) (d := 8) (by decide) (by norm_num)
      ⟨_, by decide, order48_K2_g_orderOf⟩ (by
        intro k hk
        exact order48_orderOf_ne_of_half_pow_eq_one (by norm_num)
          (show k ^ (8 / 2) = 1 by norm_num; revert hk; revert k; decide))

theorem order48_K2_ne_01_11 : IsEmpty
    (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G2
        (order48_action order48_K2_chi_01) ≃*
      SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G2
        (order48_action order48_K2_chi_11)) :=
  order48_ne_of_ker_order (K := order16_wild_G2)
    (χ := order48_K2_chi_01) (χ' := order48_K2_chi_11)
      (d := 8) (by decide) (by norm_num)
      ⟨_, by decide, order48_K2_g_orderOf⟩ (by
        intro k hk
        exact order48_orderOf_ne_of_half_pow_eq_one (by norm_num)
          (show k ^ (8 / 2) = 1 by norm_num; revert hk; revert k; decide))

theorem order48_K2_ne_10_11 : IsEmpty
    (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G2
        (order48_action order48_K2_chi_10) ≃*
      SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G2
        (order48_action order48_K2_chi_11)) :=
  order48_ne_of_ker_sq_count (by decide) (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide)

theorem order48_K3_g_orderOf :
    orderOf (SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 8)) :
      order16_wild_G3) = 8 :=
  order48_orderOf_eq_pow2_of (e := 3) rfl (by norm_num) (by decide) (by decide)

theorem order48_K3_ne_10_01 : IsEmpty
    (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G3
        (order48_action order48_K3_chi_10) ≃*
      SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G3
        (order48_action order48_K3_chi_01)) :=
  order48_isEmpty_mulEquiv_symm <| order48_ne_of_ker_order
    (K := order16_wild_G3) (χ := order48_K3_chi_01)
      (χ' := order48_K3_chi_10) (d := 8) (by decide) (by norm_num)
      ⟨_, by decide, order48_K3_g_orderOf⟩ (by
        intro k hk
        exact order48_orderOf_ne_of_half_pow_eq_one (by norm_num)
          (show k ^ (8 / 2) = 1 by norm_num; revert hk; revert k; decide))

theorem order48_K4_g_orderOf :
    orderOf (SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 8)) :
      order16_wild_G4) = 8 :=
  order48_orderOf_eq_pow2_of (e := 3) rfl (by norm_num) (by decide) (by decide)

theorem order48_K4_ne_01_10 : IsEmpty
    (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G4
        (order48_action order48_K4_chi_01) ≃*
      SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G4
        (order48_action order48_K4_chi_10)) :=
  order48_ne_of_ker_order (K := order16_wild_G4)
    (χ := order48_K4_chi_01) (χ' := order48_K4_chi_10)
      (d := 8) (by decide) (by norm_num)
      ⟨_, by decide, order48_K4_g_orderOf⟩ (by
        intro k hk
        exact order48_orderOf_ne_of_half_pow_eq_one (by norm_num)
          (show k ^ (8 / 2) = 1 by norm_num; revert hk; revert k; decide))

/-! ### Complements `K₈` through `K₁₁` -/

theorem order48_K8_ne_f0_02 : IsEmpty
    (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G8
        (order48_action order48_K8_chi_f0) ≃*
      SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G8
        (order48_action order48_K8_chi_02)) :=
  order48_ne_of_ker_sq_count (by decide) (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide)

theorem order48_K8_ne_f0_s0 : IsEmpty
    (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G8
        (order48_action order48_K8_chi_f0) ≃*
      SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G8
        (order48_action order48_K8_chi_s0)) :=
  order48_ne_of_ker_sq_count (by decide) (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide)

theorem order48_K8_ne_02_s0 : IsEmpty
    (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G8
        (order48_action order48_K8_chi_02) ≃*
      SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G8
        (order48_action order48_K8_chi_s0)) :=
  order48_ne_of_ker_sq_count (by decide) (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide)

theorem order48_K9_ne_02_t0 : IsEmpty
    (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G9
        (order48_action order48_K9_chi_02) ≃*
      SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G9
        (order48_action order48_K9_chi_t0)) :=
  order48_ne_of_ker_sq_count (by decide) (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide)

theorem order48_K10_ne_02_f0 : IsEmpty
    (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G10
        (order48_action order48_K10_chi_02) ≃*
      SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G10
        (order48_action order48_K10_chi_f0)) :=
  order48_ne_of_ker_sq_count (by decide) (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide)

theorem order48_K10_ne_02_s2 : IsEmpty
    (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G10
        (order48_action order48_K10_chi_02) ≃*
      SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G10
        (order48_action order48_K10_chi_s2)) :=
  order48_ne_of_ker_sq_count (by decide) (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide)

theorem order48_K10_ne_f0_s2 : IsEmpty
    (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G10
        (order48_action order48_K10_chi_f0) ≃*
      SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G10
        (order48_action order48_K10_chi_s2)) :=
  order48_ne_of_ker_sq_count (by decide) (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide)

theorem order48_K11_ne_10_02 : IsEmpty
    (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G11
        (order48_action order48_K11_chi_10) ≃*
      SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G11
        (order48_action order48_K11_chi_02)) :=
  order48_ne_of_ker_sq_count (by decide) (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide)

/-! ### The residual `K₁₂` tie -/

/-- If one finite group has an element with exactly `n` square roots and the
other has none, the groups are not isomorphic. -/
theorem order48_isEmpty_mulEquiv_of_sq_fiber_count
    {G₁ G₂ : Type*} [Group G₁] [Group G₂]
    [Fintype G₁] [Fintype G₂] [DecidableEq G₁] [DecidableEq G₂] {n : Nat}
    (h1 : ∃ z : G₁, Fintype.card {x : G₁ // x * x = z} = n)
    (h2 : ∀ z : G₂, Fintype.card {x : G₂ // x * x = z} ≠ n) :
    IsEmpty (G₁ ≃* G₂) := by
  constructor
  intro e
  obtain ⟨z, hz⟩ := h1
  refine h2 (e z) ?_
  rw [← hz]
  symm
  apply Fintype.card_congr
  refine Equiv.subtypeEquiv e.toEquiv fun x => ?_
  rw [show e.toEquiv x = e x from rfl, ← map_mul]
  exact ⟨fun h => by rw [h], fun h => e.injective h⟩

set_option maxHeartbeats 1600000 in
-- The universal target-fiber check evaluates all square roots in a group of order 48.
/-- The two nontrivial `K₁₂ = C₄ ⋊ C₄` actions require the square-root
fiber profile: `chi_02` has an element with `24` square roots, whereas
`chi_20` has none. -/
theorem order48_K12_ne_02_20 : IsEmpty
    (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G12
        (order48_action order48_K12_chi_02) ≃*
      SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G12
        (order48_action order48_K12_chi_20)) :=
  order48_isEmpty_mulEquiv_of_sq_fiber_count (n := 24)
    ⟨⟨1, ⟨1, Multiplicative.ofAdd (2 : ZMod 4)⟩⟩, by decide⟩
    (by decide)

theorem order48_card_centralizer_eq {K : Type*} [Group K] [Finite K]
    {χ : K →* (ZMod 3)ˣ} {n0 : Multiplicative (ZMod 3)}
    (hn0 : orderOf n0 = 3) :
    Nat.card {x : SemidirectProduct (Multiplicative (ZMod 3)) K (order48_action χ) //
        Commute (SemidirectProduct.inl n0) x} =
      3 * Nat.card {k : K // χ k = 1} := by
  have hcard : Nat.card {x : SemidirectProduct (Multiplicative (ZMod 3)) K
        (order48_action χ) // Commute (SemidirectProduct.inl n0) x} =
      Nat.card (Multiplicative (ZMod 3) × {k : K // χ k = 1}) := by
    apply Nat.card_congr
    refine
      { toFun := fun x => (x.1.left, ⟨x.1.right, ?_⟩)
        invFun := fun p =>
          ⟨SemidirectProduct.inl p.1 * SemidirectProduct.inr p.2.1, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have hmem := (order48_inl_gen_commute_iff hn0 x.1).mp x.2
      rwa [MonoidHom.comp_apply, ← MonoidHom.map_one unitAutHom,
        Function.Injective.eq_iff (unitAutHom_injective (p := 3))] at hmem
    · rw [order48_inl_gen_commute_iff hn0]
      simp [order48_action, MonoidHom.comp_apply, p.2.2]
    · rintro ⟨x, hx⟩
      exact Subtype.ext (SemidirectProduct.inl_left_mul_inr_right x)
    · rintro ⟨a, k, hk⟩
      simp
  rw [hcard, Nat.card_prod, Nat.card_eq_fintype_card]
  congr 1

/-- Different kernel cardinalities distinguish two `C₃ ⋊ K` groups. -/
theorem order48_ne_of_ker_card {K : Type*} [Group K] [Fintype K]
    (hK : Nat.Coprime 3 (Fintype.card K)) {χ χ' : K →* (ZMod 3)ˣ}
    (hcard : Nat.card {k : K // χ k = 1} ≠
      Nat.card {k : K // χ' k = 1}) :
    IsEmpty (SemidirectProduct (Multiplicative (ZMod 3)) K (order48_action χ) ≃*
      SemidirectProduct (Multiplicative (ZMod 3)) K (order48_action χ')) := by
  constructor
  intro e
  apply hcard
  let n0 : Multiplicative (ZMod 3) := Multiplicative.ofAdd (1 : ZMod 3)
  have hn0 : orderOf n0 = 3 := by
    simp [n0, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  have heord : orderOf (e (SemidirectProduct.inl n0)) = 3 := by
    rw [MulEquiv.orderOf_eq, orderOf_injective _ SemidirectProduct.inl_injective]
    exact hn0
  obtain ⟨n', hne, hn'⟩ := order48_ord3_elt_eq_inl hK heord
  have hcent : {x : SemidirectProduct (Multiplicative (ZMod 3)) K
        (order48_action χ) // Commute (SemidirectProduct.inl n0) x} ≃
      {y : SemidirectProduct (Multiplicative (ZMod 3)) K
        (order48_action χ') // Commute (SemidirectProduct.inl n') y} :=
    Equiv.subtypeEquiv e (fun x => by
      constructor
      · intro h
        have hm := h.map e
        rwa [hne] at hm
      · intro h
        rw [← hne] at h
        have hm := h.map e.symm
        simpa using hm)
  have hcardeq := Nat.card_congr hcent
  rw [order48_card_centralizer_eq hn0,
    order48_card_centralizer_eq hn'] at hcardeq
  omega

/-- Kernel size of the character defining a normal-branch representative. -/
noncomputable def order48_normal_kernel_card (k : Fin 14)
    (i : Fin (order48_normal_counts k)) : Nat :=
  Nat.card {x : order48_normal_K k // order48_normal_chi k i x = 1}

/-- The first (trivial-action) index exists uniformly in the dependent family. -/
def order48_normal_zero (k : Fin 14) : Fin (order48_normal_counts k) :=
  ⟨0, by fin_cases k <;> decide⟩

/-- The trivial action has kernel `16`; every displayed nontrivial action has
kernel `8`. -/
theorem order48_normal_kernel_card_eq (k : Fin 14)
    (i : Fin (order48_normal_counts k)) :
    order48_normal_kernel_card k i = if i.val = 0 then 16 else 8 := by
  fin_cases k <;> fin_cases i <;>
    simp only [order48_normal_kernel_card, order48_normal_K,
      order48_normal_chi, Fin.zero_eta, Fin.isValue, ↓reduceIte] <;>
    rw [Nat.card_eq_fintype_card] <;> decide

/-- For every fixed complement, the direct product is not isomorphic to any
of its nontrivial-action representatives. -/
theorem order48_normal_zero_ne_nonzero (k : Fin 14)
    (i : Fin (order48_normal_counts k)) (hi : i ≠ order48_normal_zero k) :
    ¬ Nonempty (order48_normal_reps k (order48_normal_zero k) ≃*
      order48_normal_reps k i) := by
  intro hiso
  have hival : i.val ≠ 0 := by
    intro h
    apply hi
    apply Fin.ext
    exact h
  apply (order48_ne_of_ker_card
    (K := order48_normal_K k) (χ := order48_normal_chi k (order48_normal_zero k))
      (χ' := order48_normal_chi k i) (by
        rw [show Fintype.card (order48_normal_K k) = 16 by
          rw [← Nat.card_eq_fintype_card, order48_normal_K_card]]
        decide) (by
        change order48_normal_kernel_card k (order48_normal_zero k) ≠
          order48_normal_kernel_card k i
        rw [order48_normal_kernel_card_eq, order48_normal_kernel_card_eq]
        simp [order48_normal_zero, hival])).false
  exact hiso.some

set_option maxHeartbeats 1600000 in
-- The dependent fourteen-way split elaborates every ordered pair of the 42 representatives.
/-- Representatives with the same complement and distinct reduced-action
indices are non-isomorphic. -/
theorem order48_normal_reps_same_disjoint (k : Fin 14)
    (i j : Fin (order48_normal_counts k)) (hne : i ≠ j) :
    ¬ Nonempty (order48_normal_reps k i ≃* order48_normal_reps k j) := by
  intro hiso
  by_cases hi : i = order48_normal_zero k
  · subst i
    exact order48_normal_zero_ne_nonzero k j (Ne.symm hne) hiso
  by_cases hj : j = order48_normal_zero k
  · subst j
    exact order48_normal_zero_ne_nonzero k i hi ⟨hiso.some.symm⟩
  fin_cases k <;> fin_cases i <;> fin_cases j
  all_goals simp [order48_normal_zero] at hi hj hne
  all_goals
    first
    | exact order48_K1_ne_1_2.false hiso.some
    | exact order48_K1_ne_1_2.false hiso.some.symm
    | exact order48_K2_ne_10_01.false hiso.some
    | exact order48_K2_ne_10_01.false hiso.some.symm
    | exact order48_K2_ne_01_11.false hiso.some
    | exact order48_K2_ne_01_11.false hiso.some.symm
    | exact order48_K2_ne_10_11.false hiso.some
    | exact order48_K2_ne_10_11.false hiso.some.symm
    | exact order48_K3_ne_10_01.false hiso.some
    | exact order48_K3_ne_10_01.false hiso.some.symm
    | exact order48_K4_ne_01_10.false hiso.some
    | exact order48_K4_ne_01_10.false hiso.some.symm
    | exact order48_K5_ne_1_2.false hiso.some
    | exact order48_K5_ne_1_2.false hiso.some.symm
    | exact order48_K7_ne_1_2.false hiso.some
    | exact order48_K7_ne_1_2.false hiso.some.symm
    | exact order48_K8_ne_f0_02.false hiso.some
    | exact order48_K8_ne_f0_02.false hiso.some.symm
    | exact order48_K8_ne_f0_s0.false hiso.some
    | exact order48_K8_ne_f0_s0.false hiso.some.symm
    | exact order48_K8_ne_02_s0.false hiso.some
    | exact order48_K8_ne_02_s0.false hiso.some.symm
    | exact order48_K9_ne_02_t0.false hiso.some
    | exact order48_K9_ne_02_t0.false hiso.some.symm
    | exact order48_K10_ne_02_f0.false hiso.some
    | exact order48_K10_ne_02_f0.false hiso.some.symm
    | exact order48_K10_ne_02_s2.false hiso.some
    | exact order48_K10_ne_02_s2.false hiso.some.symm
    | exact order48_K10_ne_f0_s2.false hiso.some
    | exact order48_K10_ne_f0_s2.false hiso.some.symm
    | exact order48_K11_ne_10_02.false hiso.some
    | exact order48_K11_ne_10_02.false hiso.some.symm
    | exact order48_K12_ne_02_20.false hiso.some
    | exact order48_K12_ne_02_20.false hiso.some.symm

/-- For each fixed order-`16` complement, the reduced normal-branch
representatives are pairwise non-isomorphic. -/
theorem order48_normal_reps_same_pairwise (k : Fin 14) :
    PairwiseNonMulEquiv (order48_normal_reps k) := by
  intro i j hiso
  by_contra hne
  exact order48_normal_reps_same_disjoint k i j hne hiso

/-- The dependent family of all `42` unique-Sylow-`3` representatives. -/
noncomputable def order48_normal_sigma_reps
    (x : Σ k : Fin 14, Fin (order48_normal_counts k)) : Type :=
  order48_normal_reps x.1 x.2

noncomputable instance order48_normal_sigma_reps_group
    (x : Σ k : Fin 14, Fin (order48_normal_counts k)) :
    Group (order48_normal_sigma_reps x) :=
  order48_normal_reps_group x.1 x.2

theorem order48_normal_sigma_reps_card
    (x : Σ k : Fin 14, Fin (order48_normal_counts k)) :
    Nat.card (order48_normal_sigma_reps x) = 48 :=
  order48_normal_reps_card x.1 x.2

/-- All `42` representatives in the unique-Sylow-`3` branch are pairwise
non-isomorphic, including representatives with different complements. -/
theorem order48_normal_sigma_reps_pairwise :
    PairwiseNonMulEquiv order48_normal_sigma_reps := by
  rintro ⟨k₁, i⟩ ⟨k₂, j⟩ hiso
  by_cases hk : k₁ = k₂
  · subst k₂
    have hij := order48_normal_reps_same_pairwise k₁ i j hiso
    subst j
    rfl
  · exact (order48_normal_reps_cross_disjoint k₁ k₂ hk i j hiso).elim

/-- Every order-`48` group in the unique-Sylow-`3` branch is represented by
the `42`-entry sigma family. -/
theorem order48_normal_sigma_reps_complete {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 48) (hSyl : Nat.card (Sylow 3 G) = 1) :
    ∃ x, Nonempty (G ≃* order48_normal_sigma_reps x) := by
  obtain ⟨k, i, h⟩ := order48_normal_classification hG hSyl
  exact ⟨⟨k, i⟩, h⟩

end Smallgroups.UsefulTheorems
