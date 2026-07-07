/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order16_Wild
import Smallgroups.UsefulTheorems.PGroupGeneration
import Smallgroups.UsefulTheorems.Order32.Common

/-! ## Descendants of `order16_wild_G6` (cyclic `C₁₆`)

Since `order16_A1 ≃* Multiplicative (ZMod 16)` (`order16_A1_iso_concrete`), it suffices to
classify `G` of order 32 having a central `z` of order 2 with `G ⧸ ⟨z⟩ ≃* Multiplicative
(ZMod 16)`.  Rather than going through the general cocycle machinery, we argue directly:
lift a generator of the quotient to `g : G`; since `z` is central, `g` and `z` commute, so
`⟨g, z⟩ = G` is abelian.  The lift satisfies `g ^ 16 ∈ ⟨z⟩ = {1, z}`, giving exactly two
cases: `g ^ 16 = 1` (giving `G ≅ C₁₆ × C₂`) or `g ^ 16 = z` (giving `orderOf g = 32`, so
`G` is cyclic, `G ≅ C₃₂`). -/

namespace Smallgroups.UsefulTheorems

theorem order32_of_cyclic16_quotient {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 32) {z : G} (hzc : z ∈ Subgroup.center G) (hzp : orderOf z = 2)
    [hnorm : (Subgroup.zpowers z).Normal]
    (e : (G ⧸ Subgroup.zpowers z) ≃* Multiplicative (ZMod 16)) :
    Nonempty (G ≃* Multiplicative (ZMod 32)) ∨
      Nonempty (G ≃* Multiplicative (ZMod 16) × Multiplicative (ZMod 2)) := by
  classical
  have hz2 : z ^ 2 = 1 := by rw [← hzp]; exact pow_orderOf_eq_one z
  have hker : (QuotientGroup.mk' (Subgroup.zpowers z)).ker = Subgroup.zpowers z :=
    QuotientGroup.ker_mk' _
  set q : G ⧸ Subgroup.zpowers z := e.symm (Multiplicative.ofAdd (1 : ZMod 16)) with hqdef
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (Subgroup.zpowers z) q
  have hordq : orderOf q = 16 := by
    rw [hqdef, show e.symm (Multiplicative.ofAdd (1 : ZMod 16))
      = e.symm.toMonoidHom (Multiplicative.ofAdd (1 : ZMod 16)) from rfl,
      orderOf_injective e.symm.toMonoidHom e.symm.injective,
      orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  have hordg16 : (16 : ℕ) ∣ orderOf g := by
    have := orderOf_map_dvd (QuotientGroup.mk' (Subgroup.zpowers z)) g
    rwa [hg, hordq] at this
  have hg16mem : g ^ 16 ∈ Subgroup.zpowers z := by
    rw [← hker, MonoidHom.mem_ker, map_pow, hg]
    have : q ^ 16 = 1 := by rw [← hordq]; exact pow_orderOf_eq_one q
    exact this
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg16mem
  rcases sq_eq_one_zpow_cases hz2 k with hcase | hcase
  · -- g ^ 16 = 1 : abelian case, G ≅ C16 × C2
    rw [hcase] at hk
    right
    set fg : Multiplicative (ZMod 16) →* G := zmodZPowHom 16 g hk.symm with hfgdef
    set fz : Multiplicative (ZMod 2) →* G := zmodZPowHom 2 z hz2 with hfzdef
    have hcommgz : Commute g z := Subgroup.mem_center_iff.mp hzc g
    have hfg_val : ∀ a : Multiplicative (ZMod 16),
        fg a = g ^ (Multiplicative.toAdd a).val := by
      intro a
      have ha : a = Multiplicative.ofAdd (((Multiplicative.toAdd a).val : ZMod 16)) := by
        rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
      have hcast : ((((Multiplicative.toAdd a).val : ℕ) : ℤ) : ZMod 16)
          = ((Multiplicative.toAdd a).val : ZMod 16) := by push_cast; ring
      conv_lhs => rw [ha, ← hcast]
      rw [hfgdef, zmodZPowHom_intCast, zpow_natCast]
    have hfz_val : ∀ b : Multiplicative (ZMod 2),
        fz b = z ^ (Multiplicative.toAdd b).val := by
      intro b
      have hb : b = Multiplicative.ofAdd (((Multiplicative.toAdd b).val : ZMod 2)) := by
        rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
      have hcast : ((((Multiplicative.toAdd b).val : ℕ) : ℤ) : ZMod 2)
          = ((Multiplicative.toAdd b).val : ZMod 2) := by push_cast; ring
      conv_lhs => rw [hb, ← hcast]
      rw [hfzdef, zmodZPowHom_intCast, zpow_natCast]
    have hcomm' : ∀ (a : Multiplicative (ZMod 16)) (b : Multiplicative (ZMod 2)),
        Commute (fg a) (fz b) := by
      intro a b
      rw [hfg_val a, hfz_val b]
      exact hcommgz.pow_pow _ _
    have hinj : Function.Injective (fg.noncommCoprod fz hcomm') := by
      refine (injective_iff_map_eq_one _).mpr ?_
      rintro ⟨a, b⟩ hab
      simp only [MonoidHom.noncommCoprod_apply] at hab
      rw [hfg_val a, hfz_val b] at hab
      have hmem : g ^ (Multiplicative.toAdd a).val ∈ Subgroup.zpowers z := by
        have heq : g ^ (Multiplicative.toAdd a).val
            = (z ^ (Multiplicative.toAdd b).val)⁻¹ := eq_inv_of_mul_eq_one_left hab
        rw [heq]
        exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers z) _)
      have hπ0 : (QuotientGroup.mk' (Subgroup.zpowers z)) (g ^ (Multiplicative.toAdd a).val)
          = 1 := by
        rw [← MonoidHom.mem_ker, hker]; exact hmem
      have hqav : q ^ (Multiplicative.toAdd a).val = 1 := by
        rwa [map_pow, hg] at hπ0
      have hdvd0 : orderOf q ∣ (Multiplicative.toAdd a).val := orderOf_dvd_of_pow_eq_one hqav
      have hdvd : 16 ∣ (Multiplicative.toAdd a).val := by rw [hordq] at hdvd0; exact hdvd0
      have hav_lt : (Multiplicative.toAdd a).val < 16 := ZMod.val_lt _
      have hav0 : (Multiplicative.toAdd a).val = 0 := by omega
      rw [hav0, pow_zero, one_mul] at hab
      have hbv_lt : (Multiplicative.toAdd b).val < 2 := ZMod.val_lt _
      have hdvd2 : orderOf z ∣ (Multiplicative.toAdd b).val := orderOf_dvd_of_pow_eq_one hab
      rw [hzp] at hdvd2
      have hbv0 : (Multiplicative.toAdd b).val = 0 := by omega
      have ha1 : a = 1 := by
        have h0 : Multiplicative.toAdd a = 0 := (ZMod.val_eq_zero _).mp hav0
        rw [← ofAdd_toAdd a, h0, ofAdd_zero]
      have hb1 : b = 1 := by
        have h0 : Multiplicative.toAdd b = 0 := (ZMod.val_eq_zero _).mp hbv0
        rw [← ofAdd_toAdd b, h0, ofAdd_zero]
      rw [ha1, hb1]; rfl
    have e_range : Multiplicative (ZMod 16) × Multiplicative (ZMod 2)
        ≃* (fg.noncommCoprod fz hcomm').range := MonoidHom.ofInjective hinj
    have hcardRange : Nat.card (fg.noncommCoprod fz hcomm').range = 32 := by
      rw [← Nat.card_congr e_range.toEquiv, Nat.card_prod]
      simp [Nat.card_eq_fintype_card, ZMod.card]
    have hrange_top : (fg.noncommCoprod fz hcomm').range = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [hcardRange, hG])
    exact ⟨(e_range.trans ((MulEquiv.subgroupCongr hrange_top).trans
      Subgroup.topEquiv)).symm⟩
  · -- g ^ 16 = z : orderOf g = 32, G cyclic
    rw [hcase] at hk
    left
    have hg32 : g ^ 32 = 1 := by
      have h32 : g ^ 32 = (g ^ 16) ^ 2 := by rw [← pow_mul]
      rw [h32, ← hk, hz2]
    have hz_ne_one : z ≠ 1 := by
      intro h; rw [h, orderOf_one] at hzp; exact absurd hzp (by norm_num)
    have hordg : orderOf g = 32 := by
      have hdvd1 : orderOf g ∣ 32 := orderOf_dvd_of_pow_eq_one hg32
      have hp2 : (32 : ℕ) = 2 ^ 5 := by norm_num
      have hp4 : (16 : ℕ) = 2 ^ 4 := by norm_num
      rw [hp2] at hdvd1
      obtain ⟨m, hmle, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd1
      have hm4 : 4 ≤ m := by
        have h16 := hordg16
        rw [hm, hp4] at h16
        exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h16
      interval_cases m
      · exfalso
        have h1 : g ^ 16 = 1 := by rw [hp4, ← hm]; exact pow_orderOf_eq_one g
        rw [← hk] at h1
        exact hz_ne_one h1
      · rw [hm]; norm_num
    have hinj : Function.Injective (zmodZPowHom 32 g hg32) :=
      zmodZPowHom_injective 32 g hg32 hordg
    have e_range : Multiplicative (ZMod 32) ≃* (zmodZPowHom 32 g hg32).range :=
      MonoidHom.ofInjective hinj
    have hcardRange : Nat.card (zmodZPowHom 32 g hg32).range = 32 := by
      rw [← Nat.card_congr e_range.toEquiv]
      simp
    have hrange_top : (zmodZPowHom 32 g hg32).range = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [hcardRange, hG])
    exact ⟨(e_range.trans ((MulEquiv.subgroupCongr hrange_top).trans
      Subgroup.topEquiv)).symm⟩

end Smallgroups.UsefulTheorems
