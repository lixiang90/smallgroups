/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order16_Wild
import Smallgroups.UsefulTheorems.PGroupGeneration
import Smallgroups.UsefulTheorems.Order32.Common

/-! ## Descendants of `order16_wild_G13` (`C₄ × C₄`), abelian-lift case

`order16_wild_G13 = order16_A3 ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)`
(`order16_A3_iso_concrete`).  With two symmetric order-`4` generators, the four choices of
`(g1 ^ 4, g2 ^ 4)` collapse to just **two** isomorphism types: `C4 × C4 × C2` (both trivial)
and `C4 × C8` (all three other cases, via the substitution `g2' := g2 * g1` or its mirror
image, since the two generators play symmetric roles). -/

namespace Smallgroups.UsefulTheorems

theorem order32_of_c4c4_quotient_abelian_case {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 32) {z : G} (hzc : z ∈ Subgroup.center G) (hzp : orderOf z = 2)
    [hnorm : (Subgroup.zpowers z).Normal]
    (e : (G ⧸ Subgroup.zpowers z) ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
    {g1 g2 : G}
    (hg1 : (QuotientGroup.mk' (Subgroup.zpowers z)) g1
      = e.symm (Multiplicative.ofAdd (1 : ZMod 4), 1))
    (hg2 : (QuotientGroup.mk' (Subgroup.zpowers z)) g2
      = e.symm (1, Multiplicative.ofAdd (1 : ZMod 4)))
    (hcomm : Commute g1 g2) :
    Nonempty (G ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 8)) ∨
      Nonempty (G ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)
        × Multiplicative (ZMod 2)) := by
  classical
  have hz2 : z ^ 2 = 1 := by rw [← hzp]; exact pow_orderOf_eq_one z
  have hker : (QuotientGroup.mk' (Subgroup.zpowers z)).ker = Subgroup.zpowers z :=
    QuotientGroup.ker_mk' _
  set π := QuotientGroup.mk' (Subgroup.zpowers z) with hπdef
  have hg1pow : π (g1 ^ 4) = 1 := by
    rw [map_pow, hg1, ← map_pow, Prod.pow_mk]
    norm_num
    decide
  have hg2pow : π (g2 ^ 4) = 1 := by
    rw [map_pow, hg2, ← map_pow, Prod.pow_mk]
    norm_num
    decide
  have hg1mem : g1 ^ 4 ∈ Subgroup.zpowers z := by
    rw [← hker, MonoidHom.mem_ker]; exact hg1pow
  have hg2mem : g2 ^ 4 ∈ Subgroup.zpowers z := by
    rw [← hker, MonoidHom.mem_ker]; exact hg2pow
  have hcase1 := central_pow_cases hz2 hg1mem
  have hcase2 := central_pow_cases hz2 hg2mem
  set ψ1 : G →* Multiplicative (ZMod 4) :=
    (MonoidHom.fst (Multiplicative (ZMod 4)) (Multiplicative (ZMod 4))).comp
      (e.toMonoidHom.comp π) with hψ1def
  set ψ2 : G →* Multiplicative (ZMod 4) :=
    (MonoidHom.snd (Multiplicative (ZMod 4)) (Multiplicative (ZMod 4))).comp
      (e.toMonoidHom.comp π) with hψ2def
  have hψ1g1 : ψ1 g1 = Multiplicative.ofAdd (1 : ZMod 4) := by
    change Prod.fst (e (π g1)) = _; rw [hg1, e.apply_symm_apply]
  have hψ1g2 : ψ1 g2 = 1 := by
    change Prod.fst (e (π g2)) = _; rw [hg2, e.apply_symm_apply]
  have hψ2g1 : ψ2 g1 = 1 := by
    change Prod.snd (e (π g1)) = _; rw [hg1, e.apply_symm_apply]
  have hψ2g2 : ψ2 g2 = Multiplicative.ofAdd (1 : ZMod 4) := by
    change Prod.snd (e (π g2)) = _; rw [hg2, e.apply_symm_apply]
  have hordg1_4 : (4 : ℕ) ∣ orderOf g1 := by
    have hhom : orderOf (ψ1 g1) ∣ orderOf g1 := orderOf_map_dvd _ g1
    have hord4 : orderOf (Multiplicative.ofAdd (1 : ZMod 4)) = 4 := by
      rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
    rwa [hψ1g1, hord4] at hhom
  have hordg2_4 : (4 : ℕ) ∣ orderOf g2 := by
    have hhom : orderOf (ψ2 g2) ∣ orderOf g2 := orderOf_map_dvd _ g2
    have hord4 : orderOf (Multiplicative.ofAdd (1 : ZMod 4)) = 4 := by
      rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
    rwa [hψ2g2, hord4] at hhom
  have hz_ne_one : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hzp; exact absurd hzp (by norm_num)
  have hzmem : z ∈ π.ker := by rw [hker]; exact Subgroup.mem_zpowers z
  have hπz : π z = 1 := MonoidHom.mem_ker.mp hzmem
  have hψ1z : ψ1 z = 1 := by rw [hψ1def]; change Prod.fst (e (π z)) = 1; rw [hπz, map_one]; rfl
  have hψ2z : ψ2 z = 1 := by rw [hψ2def]; change Prod.snd (e (π z)) = 1; rw [hπz, map_one]; rfl
  rcases hcase1 with hc1 | hc1 <;> rcases hcase2 with hc2 | hc2
  · -- g1 ^ 4 = 1, g2 ^ 4 = 1 : triple product C4 × C4 × C2
    right
    set fg1 : Multiplicative (ZMod 4) →* G := zmodZPowHom 4 g1 hc1 with hfg1def
    set fg2 : Multiplicative (ZMod 4) →* G := zmodZPowHom 4 g2 hc2 with hfg2def
    set fz : Multiplicative (ZMod 2) →* G := zmodZPowHom 2 z hz2 with hfzdef
    have hcz1 : Commute g1 z := Subgroup.mem_center_iff.mp hzc g1
    have hcz2 : Commute g2 z := Subgroup.mem_center_iff.mp hzc g2
    have hfg1_val : ∀ a : Multiplicative (ZMod 4), fg1 a = g1 ^ (Multiplicative.toAdd a).val := by
      intro a
      have ha : a = Multiplicative.ofAdd (((Multiplicative.toAdd a).val : ZMod 4)) := by
        rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
      have hcast : ((((Multiplicative.toAdd a).val : ℕ) : ℤ) : ZMod 4)
          = ((Multiplicative.toAdd a).val : ZMod 4) := by push_cast; ring
      conv_lhs => rw [ha, ← hcast]
      rw [hfg1def, zmodZPowHom_intCast, zpow_natCast]
    have hfg2_val : ∀ b : Multiplicative (ZMod 4), fg2 b = g2 ^ (Multiplicative.toAdd b).val := by
      intro b
      have hb : b = Multiplicative.ofAdd (((Multiplicative.toAdd b).val : ZMod 4)) := by
        rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
      have hcast : ((((Multiplicative.toAdd b).val : ℕ) : ℤ) : ZMod 4)
          = ((Multiplicative.toAdd b).val : ZMod 4) := by push_cast; ring
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
    have hcomm12 : ∀ (a : Multiplicative (ZMod 4)) (b : Multiplicative (ZMod 4)),
        Commute (fg1 a) (fg2 b) := by
      intro a b; rw [hfg1_val a, hfg2_val b]; exact hcomm.pow_pow _ _
    set F12 := fg1.noncommCoprod fg2 hcomm12 with hF12def
    have hcommFz : ∀ (x : Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
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
      have hav_lt : (Multiplicative.toAdd a).val < 4 := ZMod.val_lt _
      have hbv_lt : (Multiplicative.toAdd b).val < 4 := ZMod.val_lt _
      have hcv_lt : (Multiplicative.toAdd c).val < 2 := ZMod.val_lt _
      have h1 : ψ1 (g1 ^ (Multiplicative.toAdd a).val * g2 ^ (Multiplicative.toAdd b).val
          * z ^ (Multiplicative.toAdd c).val) = 1 := by rw [habc]; exact map_one ψ1
      rw [map_mul, map_mul, map_pow, map_pow, map_pow, hψ1g1, hψ1g2, hψ1z, one_pow, one_pow,
        mul_one, mul_one] at h1
      have hav0 : (Multiplicative.toAdd a).val = 0 := by
        have hdvd : orderOf (Multiplicative.ofAdd (1 : ZMod 4)) ∣ (Multiplicative.toAdd a).val :=
          orderOf_dvd_of_pow_eq_one h1
        rw [show orderOf (Multiplicative.ofAdd (1 : ZMod 4)) = 4 from by
          rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]] at hdvd
        exact Nat.eq_zero_of_dvd_of_lt hdvd hav_lt
      have h2 : ψ2 (g1 ^ (Multiplicative.toAdd a).val * g2 ^ (Multiplicative.toAdd b).val
          * z ^ (Multiplicative.toAdd c).val) = 1 := by rw [habc]; exact map_one ψ2
      rw [map_mul, map_mul, map_pow, map_pow, map_pow, hψ2g1, hψ2g2, hψ2z, one_pow, one_pow,
        one_mul, mul_one] at h2
      have hbv0 : (Multiplicative.toAdd b).val = 0 := by
        have hdvd : orderOf (Multiplicative.ofAdd (1 : ZMod 4)) ∣ (Multiplicative.toAdd b).val :=
          orderOf_dvd_of_pow_eq_one h2
        rw [show orderOf (Multiplicative.ofAdd (1 : ZMod 4)) = 4 from by
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
    have e_range : (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) × Multiplicative (ZMod 2)
        ≃* Φ.range := MonoidHom.ofInjective hinj
    have hcardRange : Nat.card Φ.range = 32 := by
      rw [← Nat.card_congr e_range.toEquiv, Nat.card_prod, Nat.card_prod]
      simp [Nat.card_eq_fintype_card, ZMod.card]
    have hrange_top : Φ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hcardRange, hG])
    have hfin :
        G ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) × Multiplicative (ZMod 2) :=
      (e_range.trans ((MulEquiv.subgroupCongr hrange_top).trans Subgroup.topEquiv)).symm
    exact ⟨hfin.trans MulEquiv.prodAssoc⟩
  · -- g1 ^ 4 = 1, g2 ^ 4 = z : C4 × C8
    left
    have hordg2 : orderOf g2 = 8 :=
      order_double_of_pow_eq_central (by norm_num) hordg2_4 hc2 hz_ne_one hz2
    have hindep : ∀ i j : ℕ, i < 4 → j < 8 → g1 ^ i * g2 ^ j = 1 → i = 0 ∧ j = 0 := by
      intro i j hilt hjlt hij
      have h1 : ψ1 (g1 ^ i * g2 ^ j) = 1 := by rw [hij]; exact map_one ψ1
      rw [map_mul, map_pow, map_pow, hψ1g1, hψ1g2, one_pow, mul_one] at h1
      have hdvd : orderOf (Multiplicative.ofAdd (1 : ZMod 4)) ∣ i := orderOf_dvd_of_pow_eq_one h1
      rw [show orderOf (Multiplicative.ofAdd (1 : ZMod 4)) = 4 from by
        rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]] at hdvd
      have hi0 : i = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hilt
      subst hi0
      rw [pow_zero, one_mul] at hij
      have hdvd2 : orderOf g2 ∣ j := orderOf_dvd_of_pow_eq_one hij
      rw [hordg2] at hdvd2
      exact ⟨rfl, Nat.eq_zero_of_dvd_of_lt hdvd2 hjlt⟩
    exact two_commuting_gens_iso hG hc1
      (by rw [← hordg2]; exact pow_orderOf_eq_one g2) hcomm hindep (by norm_num)
  · -- g1 ^ 4 = z, g2 ^ 4 = 1 : C4 × C8 (roles swapped)
    left
    have hordg1 : orderOf g1 = 8 :=
      order_double_of_pow_eq_central (by norm_num) hordg1_4 hc1 hz_ne_one hz2
    have hindep : ∀ i j : ℕ, i < 4 → j < 8 → g2 ^ i * g1 ^ j = 1 → i = 0 ∧ j = 0 := by
      intro i j hilt hjlt hij
      have h1 : ψ2 (g2 ^ i * g1 ^ j) = 1 := by rw [hij]; exact map_one ψ2
      rw [map_mul, map_pow, map_pow, hψ2g2, hψ2g1, one_pow, mul_one] at h1
      have hdvd : orderOf (Multiplicative.ofAdd (1 : ZMod 4)) ∣ i := orderOf_dvd_of_pow_eq_one h1
      rw [show orderOf (Multiplicative.ofAdd (1 : ZMod 4)) = 4 from by
        rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]] at hdvd
      have hi0 : i = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hilt
      subst hi0
      rw [pow_zero, one_mul] at hij
      have hdvd2 : orderOf g1 ∣ j := orderOf_dvd_of_pow_eq_one hij
      rw [hordg1] at hdvd2
      exact ⟨rfl, Nat.eq_zero_of_dvd_of_lt hdvd2 hjlt⟩
    exact two_commuting_gens_iso hG hc2
      (by rw [← hordg1]; exact pow_orderOf_eq_one g1) hcomm.symm hindep (by norm_num)
  · -- g1 ^ 4 = z, g2 ^ 4 = z : C4 × C8 via g2' = g2 * g1
    left
    have hordg1 : orderOf g1 = 8 :=
      order_double_of_pow_eq_central (by norm_num) hordg1_4 hc1 hz_ne_one hz2
    set g2' := g2 * g1 with hg2'def
    have hcommg2'g1 : Commute g2' g1 := by
      rw [hg2'def]; exact hcomm.symm.mul_left (Commute.refl g1)
    have hg2'four : g2' ^ 4 = 1 := by
      have hstep : g2' ^ 4 = z * z := by
        rw [hg2'def, (hcomm.symm.mul_pow), hc2, hc1]
      rw [hstep, ← sq]; exact hz2
    have hψ2g2' : ψ2 g2' = Multiplicative.ofAdd (1 : ZMod 4) := by
      rw [hg2'def, map_mul, hψ2g2, hψ2g1, mul_one]
    have hindep : ∀ i j : ℕ, i < 4 → j < 8 → g2' ^ i * g1 ^ j = 1 → i = 0 ∧ j = 0 := by
      intro i j hilt hjlt hij
      have h1 : ψ2 (g2' ^ i * g1 ^ j) = 1 := by rw [hij]; exact map_one ψ2
      rw [map_mul, map_pow, map_pow, hψ2g2', hψ2g1, one_pow, mul_one] at h1
      have hdvd : orderOf (Multiplicative.ofAdd (1 : ZMod 4)) ∣ i := orderOf_dvd_of_pow_eq_one h1
      rw [show orderOf (Multiplicative.ofAdd (1 : ZMod 4)) = 4 from by
        rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]] at hdvd
      have hi0 : i = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hilt
      subst hi0
      rw [pow_zero, one_mul] at hij
      have hdvd2 : orderOf g1 ∣ j := orderOf_dvd_of_pow_eq_one hij
      rw [hordg1] at hdvd2
      exact ⟨rfl, Nat.eq_zero_of_dvd_of_lt hdvd2 hjlt⟩
    exact two_commuting_gens_iso hG hg2'four
      (by rw [← hordg1]; exact pow_orderOf_eq_one g1) hcommg2'g1 hindep (by norm_num)

end Smallgroups.UsefulTheorems
