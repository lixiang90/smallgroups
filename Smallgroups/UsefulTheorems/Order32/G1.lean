/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order16_Wild
import Smallgroups.UsefulTheorems.PGroupGeneration
import Smallgroups.UsefulTheorems.Order32.Common

/-! ## Descendants of `order16_wild_G1` (`C₈ × C₂`), abelian-lift case

`order16_wild_G1 = C8g × Multiplicative (ZMod 2)` is already concrete, with independent
generators `q1` (order `8`) and `q2` (order `2`).  Lifting each to `G` gives `g1, g2` with
`g1 ^ 8, g2 ^ 2 ∈ ⟨z⟩ = {1, z}`.  When the lifts commute, `⟨g1, g2⟩ = G` is abelian, and the
four choices of `(g1 ^ 8, g2 ^ 2)` collapse (via a generator substitution in the last case)
to exactly three isomorphism types. -/

namespace Smallgroups.UsefulTheorems

theorem order32_of_c8c2_quotient_abelian_case {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 32) {z : G} (hzc : z ∈ Subgroup.center G) (hzp : orderOf z = 2)
    [hnorm : (Subgroup.zpowers z).Normal]
    (e : (G ⧸ Subgroup.zpowers z) ≃* C8g × Multiplicative (ZMod 2))
    {g1 g2 : G}
    (hg1 : (QuotientGroup.mk' (Subgroup.zpowers z)) g1
      = e.symm (Multiplicative.ofAdd (1 : ZMod 8), 1))
    (hg2 : (QuotientGroup.mk' (Subgroup.zpowers z)) g2
      = e.symm (1, Multiplicative.ofAdd (1 : ZMod 2)))
    (hcomm : Commute g1 g2) :
    Nonempty (G ≃* Multiplicative (ZMod 16) × Multiplicative (ZMod 2)) ∨
      Nonempty (G ≃* C8g × Multiplicative (ZMod 4)) ∨
      Nonempty (G ≃* C8g × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
  classical
  have hz2 : z ^ 2 = 1 := by rw [← hzp]; exact pow_orderOf_eq_one z
  have hker : (QuotientGroup.mk' (Subgroup.zpowers z)).ker = Subgroup.zpowers z :=
    QuotientGroup.ker_mk' _
  set π := QuotientGroup.mk' (Subgroup.zpowers z) with hπdef
  have hg1pow : π (g1 ^ 8) = 1 := by
    rw [map_pow, hg1, ← map_pow, Prod.pow_mk]
    norm_num
    decide
  have hg2pow : π (g2 ^ 2) = 1 := by
    rw [map_pow, hg2, ← map_pow, Prod.pow_mk]
    norm_num
    decide
  have hg1mem : g1 ^ 8 ∈ Subgroup.zpowers z := by
    rw [← hker, MonoidHom.mem_ker]; exact hg1pow
  have hg2mem : g2 ^ 2 ∈ Subgroup.zpowers z := by
    rw [← hker, MonoidHom.mem_ker]; exact hg2pow
  have hcase1 := central_pow_cases hz2 hg1mem
  have hcase2 := central_pow_cases hz2 hg2mem
  set ψ1 : G →* C8g :=
    (MonoidHom.fst C8g (Multiplicative (ZMod 2))).comp (e.toMonoidHom.comp π) with hψ1def
  set ψ2 : G →* Multiplicative (ZMod 2) :=
    (MonoidHom.snd C8g (Multiplicative (ZMod 2))).comp (e.toMonoidHom.comp π) with hψ2def
  have hψ1g1 : ψ1 g1 = Multiplicative.ofAdd (1 : ZMod 8) := by
    change Prod.fst (e (π g1)) = _; rw [hg1, e.apply_symm_apply]
  have hψ1g2 : ψ1 g2 = 1 := by
    change Prod.fst (e (π g2)) = _; rw [hg2, e.apply_symm_apply]
  have hψ2g1 : ψ2 g1 = 1 := by
    change Prod.snd (e (π g1)) = _; rw [hg1, e.apply_symm_apply]
  have hψ2g2 : ψ2 g2 = Multiplicative.ofAdd (1 : ZMod 2) := by
    change Prod.snd (e (π g2)) = _; rw [hg2, e.apply_symm_apply]
  have hordg1_8 : (8 : ℕ) ∣ orderOf g1 := by
    have hhom : orderOf (ψ1 g1) ∣ orderOf g1 := orderOf_map_dvd _ g1
    have hord8 : orderOf (Multiplicative.ofAdd (1 : ZMod 8)) = 8 := by
      rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
    rwa [hψ1g1, hord8] at hhom
  have hordg2_2 : (2 : ℕ) ∣ orderOf g2 := by
    have hhom : orderOf (ψ2 g2) ∣ orderOf g2 := orderOf_map_dvd _ g2
    have hord2 : orderOf (Multiplicative.ofAdd (1 : ZMod 2)) = 2 := by
      rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
    rwa [hψ2g2, hord2] at hhom
  have hz_ne_one : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hzp; exact absurd hzp (by norm_num)
  have hzmem : z ∈ π.ker := by rw [hker]; exact Subgroup.mem_zpowers z
  have hπz : π z = 1 := MonoidHom.mem_ker.mp hzmem
  have hψ1z : ψ1 z = 1 := by rw [hψ1def]; change Prod.fst (e (π z)) = 1; rw [hπz, map_one]; rfl
  have hψ2z : ψ2 z = 1 := by rw [hψ2def]; change Prod.snd (e (π z)) = 1; rw [hπz, map_one]; rfl
  rcases hcase1 with hc1 | hc1 <;> rcases hcase2 with hc2 | hc2
  · -- g1 ^ 8 = 1, g2 ^ 2 = 1 : triple product C8 × C2 × C2
    right; right
    set fg1 : Multiplicative (ZMod 8) →* G := zmodZPowHom 8 g1 hc1 with hfg1def
    set fg2 : Multiplicative (ZMod 2) →* G := zmodZPowHom 2 g2 hc2 with hfg2def
    set fz : Multiplicative (ZMod 2) →* G := zmodZPowHom 2 z hz2 with hfzdef
    have hcz1 : Commute g1 z := Subgroup.mem_center_iff.mp hzc g1
    have hcz2 : Commute g2 z := Subgroup.mem_center_iff.mp hzc g2
    have hfg1_val : ∀ a : Multiplicative (ZMod 8), fg1 a = g1 ^ (Multiplicative.toAdd a).val := by
      intro a
      have ha : a = Multiplicative.ofAdd (((Multiplicative.toAdd a).val : ZMod 8)) := by
        rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
      have hcast : ((((Multiplicative.toAdd a).val : ℕ) : ℤ) : ZMod 8)
          = ((Multiplicative.toAdd a).val : ZMod 8) := by push_cast; ring
      conv_lhs => rw [ha, ← hcast]
      rw [hfg1def, zmodZPowHom_intCast, zpow_natCast]
    have hfg2_val : ∀ b : Multiplicative (ZMod 2), fg2 b = g2 ^ (Multiplicative.toAdd b).val := by
      intro b
      have hb : b = Multiplicative.ofAdd (((Multiplicative.toAdd b).val : ZMod 2)) := by
        rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
      have hcast : ((((Multiplicative.toAdd b).val : ℕ) : ℤ) : ZMod 2)
          = ((Multiplicative.toAdd b).val : ZMod 2) := by push_cast; ring
      conv_lhs => rw [hb, ← hcast]
      rw [hfg2def, zmodZPowHom_intCast, zpow_natCast]
    have hfz_val : ∀ c : Multiplicative (ZMod 2), fz c = z ^ (Multiplicative.toAdd c).val := by
      intro c
      have hcc : c = Multiplicative.ofAdd (((Multiplicative.toAdd c).val : ZMod 2)) := by
        rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
      have hcast : ((((Multiplicative.toAdd c).val : ℕ) : ℤ) : ZMod 2)
          = ((Multiplicative.toAdd c).val : ZMod 2) := by push_cast; ring
      conv_lhs => rw [hcc, ← hcast]
      rw [hfzdef, zmodZPowHom_intCast, zpow_natCast]
    have hcomm12 : ∀ (a : Multiplicative (ZMod 8)) (b : Multiplicative (ZMod 2)),
        Commute (fg1 a) (fg2 b) := by
      intro a b; rw [hfg1_val a, hfg2_val b]; exact hcomm.pow_pow _ _
    set F12 := fg1.noncommCoprod fg2 hcomm12 with hF12def
    have hcommFz : ∀ (x : Multiplicative (ZMod 8) × Multiplicative (ZMod 2))
        (c : Multiplicative (ZMod 2)), Commute (F12 x) (fz c) := by
      intro x c
      rw [hF12def, MonoidHom.noncommCoprod_apply, hfg1_val, hfg2_val, hfz_val]
      exact (hcz1.pow_pow _ _).mul_left (hcz2.pow_pow _ _)
    set Φ := F12.noncommCoprod fz hcommFz with hΦdef
    have hinj : Function.Injective Φ := by
      refine (injective_iff_map_eq_one _).mpr ?_
      rintro ⟨⟨a, b⟩, c⟩ habc
      simp only [hΦdef, hF12def, MonoidHom.noncommCoprod_apply] at habc
      rw [hfg1_val a, hfg2_val b, hfz_val c] at habc
      have hav_lt : (Multiplicative.toAdd a).val < 8 := ZMod.val_lt _
      have hbv_lt : (Multiplicative.toAdd b).val < 2 := ZMod.val_lt _
      have hcv_lt : (Multiplicative.toAdd c).val < 2 := ZMod.val_lt _
      have h1 : ψ1 (g1 ^ (Multiplicative.toAdd a).val * g2 ^ (Multiplicative.toAdd b).val
          * z ^ (Multiplicative.toAdd c).val) = 1 := by rw [habc]; exact map_one ψ1
      rw [map_mul, map_mul, map_pow, map_pow, map_pow, hψ1g1, hψ1g2, hψ1z, one_pow, one_pow,
        mul_one, mul_one] at h1
      have hav0 : (Multiplicative.toAdd a).val = 0 := by
        have hdvd : orderOf (Multiplicative.ofAdd (1 : ZMod 8)) ∣ (Multiplicative.toAdd a).val :=
          orderOf_dvd_of_pow_eq_one h1
        rw [show orderOf (Multiplicative.ofAdd (1 : ZMod 8)) = 8 from by
          rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]] at hdvd
        exact Nat.eq_zero_of_dvd_of_lt hdvd hav_lt
      have h2 : ψ2 (g1 ^ (Multiplicative.toAdd a).val * g2 ^ (Multiplicative.toAdd b).val
          * z ^ (Multiplicative.toAdd c).val) = 1 := by rw [habc]; exact map_one ψ2
      rw [map_mul, map_mul, map_pow, map_pow, map_pow, hψ2g1, hψ2g2, hψ2z, one_pow, one_pow,
        one_mul, mul_one] at h2
      have hbv0 : (Multiplicative.toAdd b).val = 0 := by
        have hdvd : orderOf (Multiplicative.ofAdd (1 : ZMod 2)) ∣ (Multiplicative.toAdd b).val :=
          orderOf_dvd_of_pow_eq_one h2
        rw [show orderOf (Multiplicative.ofAdd (1 : ZMod 2)) = 2 from by
          rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]] at hdvd
        exact Nat.eq_zero_of_dvd_of_lt hdvd hbv_lt
      rw [hav0, hbv0, pow_zero, pow_zero, one_mul, one_mul] at habc
      have hcv0 : (Multiplicative.toAdd c).val = 0 := by
        have hdvd : orderOf z ∣ (Multiplicative.toAdd c).val := orderOf_dvd_of_pow_eq_one habc
        rw [hzp] at hdvd
        exact Nat.eq_zero_of_dvd_of_lt hdvd hcv_lt
      have ha1 : a = 1 := by
        have h0 : Multiplicative.toAdd a = 0 := (ZMod.val_eq_zero _).mp hav0
        rw [← ofAdd_toAdd a, h0, ofAdd_zero]
      have hb1 : b = 1 := by
        have h0 : Multiplicative.toAdd b = 0 := (ZMod.val_eq_zero _).mp hbv0
        rw [← ofAdd_toAdd b, h0, ofAdd_zero]
      have hc1' : c = 1 := by
        have h0 : Multiplicative.toAdd c = 0 := (ZMod.val_eq_zero _).mp hcv0
        rw [← ofAdd_toAdd c, h0, ofAdd_zero]
      rw [ha1, hb1, hc1']; rfl
    have e_range : (Multiplicative (ZMod 8) × Multiplicative (ZMod 2)) × Multiplicative (ZMod 2)
        ≃* Φ.range := MonoidHom.ofInjective hinj
    have hcardRange : Nat.card Φ.range = 32 := by
      rw [← Nat.card_congr e_range.toEquiv, Nat.card_prod, Nat.card_prod]
      simp [Nat.card_eq_fintype_card, ZMod.card]
    have hrange_top : Φ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hcardRange, hG])
    have hfin :
        G ≃* (Multiplicative (ZMod 8) × Multiplicative (ZMod 2)) × Multiplicative (ZMod 2) :=
      (e_range.trans ((MulEquiv.subgroupCongr hrange_top).trans Subgroup.topEquiv)).symm
    exact ⟨hfin.trans MulEquiv.prodAssoc⟩
  · -- g1 ^ 8 = 1, g2 ^ 2 = z : C8 × C4
    right; left
    have hordg1 : orderOf g1 = 8 := Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hc1) hordg1_8
    have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hz2)
    have hindep : ∀ i j : ℕ, i < 8 → j < 4 → g1 ^ i * g2 ^ j = 1 → i = 0 ∧ j = 0 := by
      intro i j hilt hjlt hij
      have h2 : ψ2 (g1 ^ i * g2 ^ j) = 1 := by rw [hij]; exact map_one ψ2
      rw [map_mul, map_pow, map_pow, hψ2g1, one_pow, one_mul, hψ2g2] at h2
      have hjdvd : orderOf (Multiplicative.ofAdd (1 : ZMod 2)) ∣ j := orderOf_dvd_of_pow_eq_one h2
      rw [show orderOf (Multiplicative.ofAdd (1 : ZMod 2)) = 2 from by
        rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]] at hjdvd
      have hj02 : j = 0 ∨ j = 2 := by omega
      rcases hj02 with hj | hj
      · subst hj
        rw [pow_zero, mul_one] at hij
        have hdvd : orderOf g1 ∣ i := orderOf_dvd_of_pow_eq_one hij
        rw [hordg1] at hdvd
        exact ⟨Nat.eq_zero_of_dvd_of_lt hdvd hilt, rfl⟩
      · exfalso
        subst hj
        rw [hc2] at hij
        have hgiz : g1 ^ i = z := by rw [eq_inv_of_mul_eq_one_left hij, hzinv]
        have h1 : ψ1 (g1 ^ i) = 1 := by rw [hgiz]; exact hψ1z
        rw [map_pow, hψ1g1] at h1
        have hdvd : orderOf (Multiplicative.ofAdd (1 : ZMod 8)) ∣ i := orderOf_dvd_of_pow_eq_one h1
        rw [show orderOf (Multiplicative.ofAdd (1 : ZMod 8)) = 8 from by
          rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]] at hdvd
        have hi0 : i = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hilt
        rw [hi0, pow_zero] at hgiz
        exact hz_ne_one hgiz.symm
    have hordg2 : orderOf g2 = 4 := by
      have h := order_double_of_pow_eq_central (n := 2) (by norm_num) hordg2_2 hc2 hz_ne_one hz2
      norm_num at h; exact h
    exact two_commuting_gens_iso hG hc1
      (by rw [← hordg2]; exact pow_orderOf_eq_one g2) hcomm hindep (by norm_num)
  · -- g1 ^ 8 = z, g2 ^ 2 = 1 : C16 × C2
    left
    have hordg1 : orderOf g1 = 16 :=
      order_double_of_pow_eq_central (by norm_num) hordg1_8 hc1 hz_ne_one hz2
    have hindep : ∀ i j : ℕ, i < 16 → j < 2 → g1 ^ i * g2 ^ j = 1 → i = 0 ∧ j = 0 := by
      intro i j hilt hjlt hij
      have h2 : ψ2 (g1 ^ i * g2 ^ j) = 1 := by rw [hij]; exact map_one ψ2
      rw [map_mul, map_pow, map_pow, hψ2g1, one_pow, one_mul, hψ2g2] at h2
      have hjdvd : orderOf (Multiplicative.ofAdd (1 : ZMod 2)) ∣ j := orderOf_dvd_of_pow_eq_one h2
      rw [show orderOf (Multiplicative.ofAdd (1 : ZMod 2)) = 2 from by
        rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]] at hjdvd
      have hj0 : j = 0 := Nat.eq_zero_of_dvd_of_lt hjdvd hjlt
      subst hj0
      rw [pow_zero, mul_one] at hij
      have hdvd : orderOf g1 ∣ i := orderOf_dvd_of_pow_eq_one hij
      rw [hordg1] at hdvd
      exact ⟨Nat.eq_zero_of_dvd_of_lt hdvd hilt, rfl⟩
    exact two_commuting_gens_iso hG
      (by rw [← hordg1]; exact pow_orderOf_eq_one g1) hc2 hcomm hindep (by norm_num)
  · -- g1 ^ 8 = z, g2 ^ 2 = z : C16 × C2 via g2' = g2 * g1⁻⁴
    left
    have hordg1 : orderOf g1 = 16 :=
      order_double_of_pow_eq_central (by norm_num) hordg1_8 hc1 hz_ne_one hz2
    have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hz2)
    set g2' := g2 * (g1 ^ 4)⁻¹ with hg2'def
    have hcommg2ginv : Commute g2 (g1 ^ 4)⁻¹ := (hcomm.symm.pow_right 4).inv_right
    have hcommg1g2' : Commute g1 g2' := by
      rw [hg2'def]
      exact hcomm.mul_right (((Commute.refl g1).pow_right 4).inv_right)
    have hg2'sq : g2' ^ 2 = 1 := by
      have hstep : g2' ^ 2 = z * (g1 ^ 8)⁻¹ := by
        rw [hg2'def, hcommg2ginv.mul_pow, hc2, inv_pow, ← pow_mul]
      rw [hstep, hc1, hzinv, ← sq]; exact hz2
    have hψ2g2' : ψ2 g2' = Multiplicative.ofAdd (1 : ZMod 2) := by
      rw [hg2'def, map_mul, map_inv, map_pow, hψ2g1, one_pow, inv_one, mul_one, hψ2g2]
    have hindep : ∀ i j : ℕ, i < 16 → j < 2 → g1 ^ i * g2' ^ j = 1 → i = 0 ∧ j = 0 := by
      intro i j hilt hjlt hij
      have h2 : ψ2 (g1 ^ i * g2' ^ j) = 1 := by rw [hij]; exact map_one ψ2
      rw [map_mul, map_pow, map_pow, hψ2g1, one_pow, one_mul, hψ2g2'] at h2
      have hjdvd : orderOf (Multiplicative.ofAdd (1 : ZMod 2)) ∣ j := orderOf_dvd_of_pow_eq_one h2
      rw [show orderOf (Multiplicative.ofAdd (1 : ZMod 2)) = 2 from by
        rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]] at hjdvd
      have hj0 : j = 0 := Nat.eq_zero_of_dvd_of_lt hjdvd hjlt
      subst hj0
      rw [pow_zero, mul_one] at hij
      have hdvd : orderOf g1 ∣ i := orderOf_dvd_of_pow_eq_one hij
      rw [hordg1] at hdvd
      exact ⟨Nat.eq_zero_of_dvd_of_lt hdvd hilt, rfl⟩
    exact two_commuting_gens_iso hG
      (by rw [← hordg1]; exact pow_orderOf_eq_one g1) hg2'sq hcommg1g2' hindep (by norm_num)

end Smallgroups.UsefulTheorems
