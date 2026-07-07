/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order16_Wild
import Smallgroups.UsefulTheorems.PGroupGeneration
import Smallgroups.UsefulTheorems.Order32.Common

/-! ## Descendants of `order16_wild_G7` (`K₈ × C₂ = C₄ × C₂ × C₂`), abelian-lift case

`order16_wild_G7 = K8g × Multiplicative (ZMod 2)`, with `K8g = Multiplicative (ZMod 4) ×
Multiplicative (ZMod 2)`, so the quotient has three independent generators `a` (order `4`),
`b, c` (order `2`).  With commuting lifts, the eight choices of `(ga ^ 4, gb ^ 2, gc ^ 2)`
collapse to exactly three isomorphism types: `C4 × C2 × C2 × C2` (all trivial), `C8 × C2 ×
C2` (the `a`-bit set, alone or with one other), and `C4 × C4 × C2` (a `b`- or `c`-bit set,
alone or together, with `a` untouched). -/

namespace Smallgroups.UsefulTheorems

theorem order32_of_c4c2c2_quotient_abelian_case {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 32) {z : G} (hzc : z ∈ Subgroup.center G) (hzp : orderOf z = 2)
    [hnorm : (Subgroup.zpowers z).Normal]
    (e : (G ⧸ Subgroup.zpowers z)
      ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
    {ga gb gc : G}
    (hga : (QuotientGroup.mk' (Subgroup.zpowers z)) ga
      = e.symm (Multiplicative.ofAdd (1 : ZMod 4), 1, 1))
    (hgb : (QuotientGroup.mk' (Subgroup.zpowers z)) gb
      = e.symm (1, Multiplicative.ofAdd (1 : ZMod 2), 1))
    (hgc : (QuotientGroup.mk' (Subgroup.zpowers z)) gc
      = e.symm (1, 1, Multiplicative.ofAdd (1 : ZMod 2)))
    (hcab : Commute ga gb) (hcac : Commute ga gc) (hcbc : Commute gb gc) :
    Nonempty (G ≃* Multiplicative (ZMod 8) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
      ∨ Nonempty (G ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)
        × Multiplicative (ZMod 2))
      ∨ Nonempty (G ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 2)
        × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
  classical
  have hz2 : z ^ 2 = 1 := by rw [← hzp]; exact pow_orderOf_eq_one z
  have hker : (QuotientGroup.mk' (Subgroup.zpowers z)).ker = Subgroup.zpowers z :=
    QuotientGroup.ker_mk' _
  set π := QuotientGroup.mk' (Subgroup.zpowers z) with hπdef
  have hgapow : π (ga ^ 4) = 1 := by
    rw [map_pow, hga, ← map_pow, Prod.pow_mk, Prod.pow_mk]; norm_num; decide
  have hgbpow : π (gb ^ 2) = 1 := by
    rw [map_pow, hgb, ← map_pow, Prod.pow_mk, Prod.pow_mk]; norm_num; decide
  have hgcpow : π (gc ^ 2) = 1 := by
    rw [map_pow, hgc, ← map_pow, Prod.pow_mk, Prod.pow_mk]; norm_num; decide
  have hgamem : ga ^ 4 ∈ Subgroup.zpowers z := by
    rw [← hker, MonoidHom.mem_ker]; exact hgapow
  have hgbmem : gb ^ 2 ∈ Subgroup.zpowers z := by
    rw [← hker, MonoidHom.mem_ker]; exact hgbpow
  have hgcmem : gc ^ 2 ∈ Subgroup.zpowers z := by
    rw [← hker, MonoidHom.mem_ker]; exact hgcpow
  have hcaseA := central_pow_cases hz2 hgamem
  have hcaseB := central_pow_cases hz2 hgbmem
  have hcaseC := central_pow_cases hz2 hgcmem
  set ψa : G →* Multiplicative (ZMod 4) :=
    (MonoidHom.fst _ _).comp (e.toMonoidHom.comp π) with hψadef
  set ψbc : G →* Multiplicative (ZMod 2) × Multiplicative (ZMod 2) :=
    (MonoidHom.snd _ _).comp (e.toMonoidHom.comp π) with hψbcdef
  set ψb : G →* Multiplicative (ZMod 2) := (MonoidHom.fst _ _).comp ψbc with hψbdef
  set ψc : G →* Multiplicative (ZMod 2) := (MonoidHom.snd _ _).comp ψbc with hψcdef
  have hψaga : ψa ga = Multiplicative.ofAdd (1 : ZMod 4) := by
    change Prod.fst (e (π ga)) = _; rw [hga, e.apply_symm_apply]
  have hψagb : ψa gb = 1 := by
    change Prod.fst (e (π gb)) = _; rw [hgb, e.apply_symm_apply]
  have hψagc : ψa gc = 1 := by
    change Prod.fst (e (π gc)) = _; rw [hgc, e.apply_symm_apply]
  have hψbga : ψb ga = 1 := by
    rw [hψbdef]; change Prod.fst (Prod.snd (e (π ga))) = _; rw [hga, e.apply_symm_apply]
  have hψbgb : ψb gb = Multiplicative.ofAdd (1 : ZMod 2) := by
    rw [hψbdef]; change Prod.fst (Prod.snd (e (π gb))) = _; rw [hgb, e.apply_symm_apply]
  have hψbgc : ψb gc = 1 := by
    rw [hψbdef]; change Prod.fst (Prod.snd (e (π gc))) = _; rw [hgc, e.apply_symm_apply]
  have hψcga : ψc ga = 1 := by
    rw [hψcdef]; change Prod.snd (Prod.snd (e (π ga))) = _; rw [hga, e.apply_symm_apply]
  have hψcgb : ψc gb = 1 := by
    rw [hψcdef]; change Prod.snd (Prod.snd (e (π gb))) = _; rw [hgb, e.apply_symm_apply]
  have hψcgc : ψc gc = Multiplicative.ofAdd (1 : ZMod 2) := by
    rw [hψcdef]; change Prod.snd (Prod.snd (e (π gc))) = _; rw [hgc, e.apply_symm_apply]
  have hordga_4 : (4 : ℕ) ∣ orderOf ga := by
    have hhom : orderOf (ψa ga) ∣ orderOf ga := orderOf_map_dvd _ ga
    rwa [hψaga, show orderOf (Multiplicative.ofAdd (1 : ZMod 4)) = 4 from by
      rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]] at hhom
  have hordgb_2 : (2 : ℕ) ∣ orderOf gb := by
    have hhom : orderOf (ψb gb) ∣ orderOf gb := orderOf_map_dvd _ gb
    rwa [hψbgb, show orderOf (Multiplicative.ofAdd (1 : ZMod 2)) = 2 from by
      rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]] at hhom
  have hordgc_2 : (2 : ℕ) ∣ orderOf gc := by
    have hhom : orderOf (ψc gc) ∣ orderOf gc := orderOf_map_dvd _ gc
    rwa [hψcgc, show orderOf (Multiplicative.ofAdd (1 : ZMod 2)) = 2 from by
      rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]] at hhom
  have hz_ne_one : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hzp; exact absurd hzp (by norm_num)
  have hzmem : z ∈ π.ker := by rw [hker]; exact Subgroup.mem_zpowers z
  have hπz : π z = 1 := MonoidHom.mem_ker.mp hzmem
  have hψaz : ψa z = 1 := by
    rw [hψadef]; change Prod.fst (e (π z)) = 1; rw [hπz, map_one]; rfl
  have hψbz : ψb z = 1 := by
    rw [hψbdef]; change Prod.fst (Prod.snd (e (π z))) = 1; rw [hπz, map_one]; rfl
  have hψcz : ψc z = 1 := by
    rw [hψcdef]; change Prod.snd (Prod.snd (e (π z))) = 1; rw [hπz, map_one]; rfl
  have hord2 : orderOf (Multiplicative.ofAdd (1 : ZMod 2)) = 2 := by
    rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  have hord4 : orderOf (Multiplicative.ofAdd (1 : ZMod 4)) = 4 := by
    rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  rcases hcaseA with hcA | hcA <;> rcases hcaseB with hcB | hcB <;> rcases hcaseC with hcC | hcC
  · -- (0,0,0): all trivial, quadruple C4 × C2 × C2 × C2
    right; right
    set fa : Multiplicative (ZMod 4) →* G := zmodZPowHom 4 ga hcA with hfadef
    set fb : Multiplicative (ZMod 2) →* G := zmodZPowHom 2 gb hcB with hfbdef
    set fc : Multiplicative (ZMod 2) →* G := zmodZPowHom 2 gc hcC with hfcdef
    set fz : Multiplicative (ZMod 2) →* G := zmodZPowHom 2 z hz2 with hfzdef
    have hcaz : Commute ga z := Subgroup.mem_center_iff.mp hzc ga
    have hcbz : Commute gb z := Subgroup.mem_center_iff.mp hzc gb
    have hccz : Commute gc z := Subgroup.mem_center_iff.mp hzc gc
    have hfa_val : ∀ x : Multiplicative (ZMod 4), fa x = ga ^ (Multiplicative.toAdd x).val := by
      intro x
      have hx : x = Multiplicative.ofAdd (((Multiplicative.toAdd x).val : ZMod 4)) := by
        rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
      have hcast : ((((Multiplicative.toAdd x).val : ℕ) : ℤ) : ZMod 4)
          = ((Multiplicative.toAdd x).val : ZMod 4) := by push_cast; ring
      conv_lhs => rw [hx, ← hcast]
      rw [hfadef, zmodZPowHom_intCast, zpow_natCast]
    have hfb_val : ∀ x : Multiplicative (ZMod 2), fb x = gb ^ (Multiplicative.toAdd x).val := by
      intro x
      have hx : x = Multiplicative.ofAdd (((Multiplicative.toAdd x).val : ZMod 2)) := by
        rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
      have hcast : ((((Multiplicative.toAdd x).val : ℕ) : ℤ) : ZMod 2)
          = ((Multiplicative.toAdd x).val : ZMod 2) := by push_cast; ring
      conv_lhs => rw [hx, ← hcast]
      rw [hfbdef, zmodZPowHom_intCast, zpow_natCast]
    have hfc_val : ∀ x : Multiplicative (ZMod 2), fc x = gc ^ (Multiplicative.toAdd x).val := by
      intro x
      have hx : x = Multiplicative.ofAdd (((Multiplicative.toAdd x).val : ZMod 2)) := by
        rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
      have hcast : ((((Multiplicative.toAdd x).val : ℕ) : ℤ) : ZMod 2)
          = ((Multiplicative.toAdd x).val : ZMod 2) := by push_cast; ring
      conv_lhs => rw [hx, ← hcast]
      rw [hfcdef, zmodZPowHom_intCast, zpow_natCast]
    have hfz_val : ∀ x : Multiplicative (ZMod 2), fz x = z ^ (Multiplicative.toAdd x).val := by
      intro x
      have hx : x = Multiplicative.ofAdd (((Multiplicative.toAdd x).val : ZMod 2)) := by
        rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
      have hcast : ((((Multiplicative.toAdd x).val : ℕ) : ℤ) : ZMod 2)
          = ((Multiplicative.toAdd x).val : ZMod 2) := by push_cast; ring
      conv_lhs => rw [hx, ← hcast]
      rw [hfzdef, zmodZPowHom_intCast, zpow_natCast]
    have hcommab : ∀ (x : Multiplicative (ZMod 4)) (y : Multiplicative (ZMod 2)),
        Commute (fa x) (fb y) := by
      intro x y; rw [hfa_val x, hfb_val y]; exact hcab.pow_pow _ _
    set Fab := fa.noncommCoprod fb hcommab with hFabdef
    have hcommFabc : ∀ (x : Multiplicative (ZMod 4) × Multiplicative (ZMod 2))
        (y : Multiplicative (ZMod 2)), Commute (Fab x) (fc y) := by
      intro x y
      rw [hFabdef, MonoidHom.noncommCoprod_apply, hfa_val, hfb_val, hfc_val]
      exact (hcac.pow_pow _ _).mul_left (hcbc.pow_pow _ _)
    set Fabc := Fab.noncommCoprod fc hcommFabc with hFabcdef
    have hcommFabcz : ∀ (x : (Multiplicative (ZMod 4) × Multiplicative (ZMod 2))
        × Multiplicative (ZMod 2)) (y : Multiplicative (ZMod 2)), Commute (Fabc x) (fz y) := by
      intro x y
      rw [hFabcdef, MonoidHom.noncommCoprod_apply, hFabdef, MonoidHom.noncommCoprod_apply,
        hfa_val, hfb_val, hfc_val, hfz_val]
      exact ((hcaz.pow_pow _ _).mul_left (hcbz.pow_pow _ _)).mul_left (hccz.pow_pow _ _)
    set Φ := Fabc.noncommCoprod fz hcommFabcz with hΦdef
    have hinj : Function.Injective Φ := by
      refine (injective_iff_map_eq_one _).mpr ?_
      rintro ⟨⟨⟨x, y⟩, u⟩, v⟩ habcd
      simp only [hΦdef, hFabcdef, hFabdef, MonoidHom.noncommCoprod_apply] at habcd
      rw [hfa_val x, hfb_val y, hfc_val u, hfz_val v] at habcd
      have hxv_lt : (Multiplicative.toAdd x).val < 4 := ZMod.val_lt _
      have hyv_lt : (Multiplicative.toAdd y).val < 2 := ZMod.val_lt _
      have huv_lt : (Multiplicative.toAdd u).val < 2 := ZMod.val_lt _
      have hvv_lt : (Multiplicative.toAdd v).val < 2 := ZMod.val_lt _
      have h1 : ψa (ga ^ (Multiplicative.toAdd x).val * gb ^ (Multiplicative.toAdd y).val
          * gc ^ (Multiplicative.toAdd u).val * z ^ (Multiplicative.toAdd v).val) = 1 := by
        rw [habcd]; exact map_one ψa
      simp only [map_mul, map_pow, hψaga, hψagb, hψagc, hψaz, one_pow, mul_one] at h1
      have hxv0 : (Multiplicative.toAdd x).val = 0 := by
        have hdvd : orderOf (Multiplicative.ofAdd (1 : ZMod 4)) ∣ (Multiplicative.toAdd x).val :=
          orderOf_dvd_of_pow_eq_one h1
        rw [hord4] at hdvd; exact Nat.eq_zero_of_dvd_of_lt hdvd hxv_lt
      rw [hxv0, pow_zero, one_mul] at habcd
      have h2 : ψb (gb ^ (Multiplicative.toAdd y).val * gc ^ (Multiplicative.toAdd u).val
          * z ^ (Multiplicative.toAdd v).val) = 1 := by rw [habcd]; exact map_one ψb
      simp only [map_mul, map_pow, hψbgb, hψbgc, hψbz, one_pow, mul_one] at h2
      have hyv0 : (Multiplicative.toAdd y).val = 0 := by
        have hdvd : orderOf (Multiplicative.ofAdd (1 : ZMod 2)) ∣ (Multiplicative.toAdd y).val :=
          orderOf_dvd_of_pow_eq_one h2
        rw [hord2] at hdvd; exact Nat.eq_zero_of_dvd_of_lt hdvd hyv_lt
      rw [hyv0, pow_zero, one_mul] at habcd
      have h3 : ψc (gc ^ (Multiplicative.toAdd u).val * z ^ (Multiplicative.toAdd v).val) = 1 := by
        rw [habcd]; exact map_one ψc
      simp only [map_mul, map_pow, hψcgc, hψcz, one_pow, mul_one] at h3
      have huv0 : (Multiplicative.toAdd u).val = 0 := by
        have hdvd : orderOf (Multiplicative.ofAdd (1 : ZMod 2)) ∣ (Multiplicative.toAdd u).val :=
          orderOf_dvd_of_pow_eq_one h3
        rw [hord2] at hdvd; exact Nat.eq_zero_of_dvd_of_lt hdvd huv_lt
      rw [huv0, pow_zero, one_mul] at habcd
      have hvv0 : (Multiplicative.toAdd v).val = 0 := by
        have hdvd : orderOf z ∣ (Multiplicative.toAdd v).val := orderOf_dvd_of_pow_eq_one habcd
        rw [hzp] at hdvd; exact Nat.eq_zero_of_dvd_of_lt hdvd hvv_lt
      have hx1 : x = 1 := by
        have h0 : Multiplicative.toAdd x = 0 := (ZMod.val_eq_zero _).mp hxv0
        rw [← ofAdd_toAdd x, h0, ofAdd_zero]
      have hy1 : y = 1 := by
        have h0 : Multiplicative.toAdd y = 0 := (ZMod.val_eq_zero _).mp hyv0
        rw [← ofAdd_toAdd y, h0, ofAdd_zero]
      have hu1 : u = 1 := by
        have h0 : Multiplicative.toAdd u = 0 := (ZMod.val_eq_zero _).mp huv0
        rw [← ofAdd_toAdd u, h0, ofAdd_zero]
      have hv1 : v = 1 := by
        have h0 : Multiplicative.toAdd v = 0 := (ZMod.val_eq_zero _).mp hvv0
        rw [← ofAdd_toAdd v, h0, ofAdd_zero]
      rw [hx1, hy1, hu1, hv1]; rfl
    have e_range : ((Multiplicative (ZMod 4) × Multiplicative (ZMod 2))
        × Multiplicative (ZMod 2)) × Multiplicative (ZMod 2) ≃* Φ.range :=
      MonoidHom.ofInjective hinj
    have hcardRange : Nat.card Φ.range = 32 := by
      rw [← Nat.card_congr e_range.toEquiv, Nat.card_prod, Nat.card_prod, Nat.card_prod]
      simp [Nat.card_eq_fintype_card, ZMod.card]
    have hrange_top : Φ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hcardRange, hG])
    have hfin : G ≃* ((Multiplicative (ZMod 4) × Multiplicative (ZMod 2))
        × Multiplicative (ZMod 2)) × Multiplicative (ZMod 2) :=
      (e_range.trans ((MulEquiv.subgroupCongr hrange_top).trans Subgroup.topEquiv)).symm
    exact ⟨(hfin.trans MulEquiv.prodAssoc).trans MulEquiv.prodAssoc⟩
  · -- (0,0,1): a untouched=4, c doubled=4, b untouched=2
    right; left
    have hordgc : orderOf gc = 4 :=
      order_double_of_pow_eq_central (by norm_num) hordgc_2 hcC hz_ne_one hz2
    have hindep : ∀ i j l : ℕ, i < 4 → j < 4 → l < 2 →
        ga ^ i * gc ^ j * gb ^ l = 1 → i = 0 ∧ j = 0 ∧ l = 0 := by
      intro i j l hilt hjlt hllt hijl
      have h1 : ψa (ga ^ i * gc ^ j * gb ^ l) = 1 := by rw [hijl]; exact map_one ψa
      simp only [map_mul, map_pow, hψaga, hψagc, hψagb, one_pow, mul_one] at h1
      have hi0 : i = 0 := by
        have hdvd : orderOf (Multiplicative.ofAdd (1 : ZMod 4)) ∣ i := orderOf_dvd_of_pow_eq_one h1
        rw [hord4] at hdvd; exact Nat.eq_zero_of_dvd_of_lt hdvd hilt
      subst hi0
      rw [pow_zero, one_mul] at hijl
      have h2 : ψb (gc ^ j * gb ^ l) = 1 := by rw [hijl]; exact map_one ψb
      simp only [map_mul, map_pow, hψbgc, hψbgb, one_pow, one_mul] at h2
      have hl0 : l = 0 := by
        have hdvd : orderOf (Multiplicative.ofAdd (1 : ZMod 2)) ∣ l := orderOf_dvd_of_pow_eq_one h2
        rw [hord2] at hdvd; exact Nat.eq_zero_of_dvd_of_lt hdvd hllt
      subst hl0
      rw [pow_zero, mul_one] at hijl
      have hdvd3 : orderOf gc ∣ j := orderOf_dvd_of_pow_eq_one hijl
      rw [hordgc] at hdvd3
      exact ⟨rfl, Nat.eq_zero_of_dvd_of_lt hdvd3 hjlt, rfl⟩
    exact three_commuting_gens_iso hG hcA
      (by rw [← hordgc]; exact pow_orderOf_eq_one gc) hcB hcac hcab hcbc.symm hindep
      (by norm_num)
  · -- (0,1,0): a untouched=4, b doubled=4, c untouched=2
    right; left
    have hordgb : orderOf gb = 4 :=
      order_double_of_pow_eq_central (by norm_num) hordgb_2 hcB hz_ne_one hz2
    have hindep : ∀ i j l : ℕ, i < 4 → j < 4 → l < 2 →
        ga ^ i * gb ^ j * gc ^ l = 1 → i = 0 ∧ j = 0 ∧ l = 0 := by
      intro i j l hilt hjlt hllt hijl
      have h1 : ψa (ga ^ i * gb ^ j * gc ^ l) = 1 := by rw [hijl]; exact map_one ψa
      simp only [map_mul, map_pow, hψaga, hψagb, hψagc, one_pow, mul_one] at h1
      have hi0 : i = 0 := by
        have hdvd : orderOf (Multiplicative.ofAdd (1 : ZMod 4)) ∣ i := orderOf_dvd_of_pow_eq_one h1
        rw [hord4] at hdvd; exact Nat.eq_zero_of_dvd_of_lt hdvd hilt
      subst hi0
      rw [pow_zero, one_mul] at hijl
      have h2 : ψc (gb ^ j * gc ^ l) = 1 := by rw [hijl]; exact map_one ψc
      simp only [map_mul, map_pow, hψcgb, hψcgc, one_pow, one_mul] at h2
      have hl0 : l = 0 := by
        have hdvd : orderOf (Multiplicative.ofAdd (1 : ZMod 2)) ∣ l := orderOf_dvd_of_pow_eq_one h2
        rw [hord2] at hdvd; exact Nat.eq_zero_of_dvd_of_lt hdvd hllt
      subst hl0
      rw [pow_zero, mul_one] at hijl
      have hdvd3 : orderOf gb ∣ j := orderOf_dvd_of_pow_eq_one hijl
      rw [hordgb] at hdvd3
      exact ⟨rfl, Nat.eq_zero_of_dvd_of_lt hdvd3 hjlt, rfl⟩
    exact three_commuting_gens_iso hG hcA
      (by rw [← hordgb]; exact pow_orderOf_eq_one gb) hcC hcab hcac hcbc hindep (by norm_num)
  · -- (0,1,1): a untouched=4, b doubled=4, c merges with b
    right; left
    have hordgb : orderOf gb = 4 :=
      order_double_of_pow_eq_central (by norm_num) hordgb_2 hcB hz_ne_one hz2
    set gc' := gc * gb with hgc'def
    have hcommagc' : Commute ga gc' := by
      rw [hgc'def]; exact hcac.mul_right hcab
    have hgc'sq : gc' ^ 2 = 1 := by
      have hstep : gc' ^ 2 = z * z := by rw [hgc'def, hcbc.symm.mul_pow, hcC, hcB]
      rw [hstep, ← sq]; exact hz2
    have hψagc' : ψa gc' = 1 := by rw [hgc'def, map_mul, hψagc, hψagb, mul_one]
    have hψcgc' : ψc gc' = Multiplicative.ofAdd (1 : ZMod 2) := by
      rw [hgc'def, map_mul, hψcgc, hψcgb, mul_one]
    have hcommbgc' : Commute gb gc' := by
      rw [hgc'def]; exact hcbc.mul_right (Commute.refl gb)
    have hindep : ∀ i j l : ℕ, i < 4 → j < 4 → l < 2 →
        ga ^ i * gb ^ j * gc' ^ l = 1 → i = 0 ∧ j = 0 ∧ l = 0 := by
      intro i j l hilt hjlt hllt hijl
      have h1 : ψa (ga ^ i * gb ^ j * gc' ^ l) = 1 := by rw [hijl]; exact map_one ψa
      simp only [map_mul, map_pow, hψaga, hψagb, hψagc', one_pow, mul_one] at h1
      have hi0 : i = 0 := by
        have hdvd : orderOf (Multiplicative.ofAdd (1 : ZMod 4)) ∣ i := orderOf_dvd_of_pow_eq_one h1
        rw [hord4] at hdvd; exact Nat.eq_zero_of_dvd_of_lt hdvd hilt
      subst hi0
      rw [pow_zero, one_mul] at hijl
      have h2 : ψc (gb ^ j * gc' ^ l) = 1 := by rw [hijl]; exact map_one ψc
      simp only [map_mul, map_pow, hψcgb, hψcgc', one_pow, one_mul] at h2
      have hl0 : l = 0 := by
        have hdvd : orderOf (Multiplicative.ofAdd (1 : ZMod 2)) ∣ l := orderOf_dvd_of_pow_eq_one h2
        rw [hord2] at hdvd; exact Nat.eq_zero_of_dvd_of_lt hdvd hllt
      subst hl0
      rw [pow_zero, mul_one] at hijl
      have hdvd3 : orderOf gb ∣ j := orderOf_dvd_of_pow_eq_one hijl
      rw [hordgb] at hdvd3
      exact ⟨rfl, Nat.eq_zero_of_dvd_of_lt hdvd3 hjlt, rfl⟩
    exact three_commuting_gens_iso hG hcA
      (by rw [← hordgb]; exact pow_orderOf_eq_one gb) hgc'sq
      hcab hcommagc' hcommbgc' hindep (by norm_num)
  · -- (1,0,0): a doubled=8, b,c untouched
    left
    have hordga : orderOf ga = 8 :=
      order_double_of_pow_eq_central (by norm_num) hordga_4 hcA hz_ne_one hz2
    have hindep : ∀ i j l : ℕ, i < 8 → j < 2 → l < 2 →
        ga ^ i * gb ^ j * gc ^ l = 1 → i = 0 ∧ j = 0 ∧ l = 0 := by
      intro i j l hilt hjlt hllt hijl
      have h1 : ψb (ga ^ i * gb ^ j * gc ^ l) = 1 := by rw [hijl]; exact map_one ψb
      simp only [map_mul, map_pow, hψbga, hψbgb, hψbgc, one_pow, one_mul, mul_one] at h1
      have hj0 : j = 0 := by
        have hdvd : orderOf (Multiplicative.ofAdd (1 : ZMod 2)) ∣ j := orderOf_dvd_of_pow_eq_one h1
        rw [hord2] at hdvd; exact Nat.eq_zero_of_dvd_of_lt hdvd hjlt
      subst hj0
      rw [pow_zero, mul_one] at hijl
      have h2 : ψc (ga ^ i * gc ^ l) = 1 := by rw [hijl]; exact map_one ψc
      simp only [map_mul, map_pow, hψcga, hψcgc, one_pow, one_mul] at h2
      have hl0 : l = 0 := by
        have hdvd : orderOf (Multiplicative.ofAdd (1 : ZMod 2)) ∣ l := orderOf_dvd_of_pow_eq_one h2
        rw [hord2] at hdvd; exact Nat.eq_zero_of_dvd_of_lt hdvd hllt
      subst hl0
      rw [pow_zero, mul_one] at hijl
      have hdvd3 : orderOf ga ∣ i := orderOf_dvd_of_pow_eq_one hijl
      rw [hordga] at hdvd3
      exact ⟨Nat.eq_zero_of_dvd_of_lt hdvd3 hilt, rfl, rfl⟩
    exact three_commuting_gens_iso hG
      (by rw [← hordga]; exact pow_orderOf_eq_one ga) hcB hcC
      hcab hcac hcbc hindep (by norm_num)
  · -- (1,0,1): a doubled=8, c merges with a, b untouched
    left
    have hordga : orderOf ga = 8 :=
      order_double_of_pow_eq_central (by norm_num) hordga_4 hcA hz_ne_one hz2
    set gc' := gc * (ga ^ 2)⁻¹ with hgc'def
    have hcommgc' : Commute ga gc' := by
      rw [hgc'def]; exact hcac.mul_right (((Commute.refl ga).pow_right 2).inv_right)
    have hga2sq : (ga ^ 2) ^ 2 = z := by rw [← pow_mul]; exact hcA
    have hgc'sq : gc' ^ 2 = 1 := by
      have hcommgagc2 : Commute gc ((ga ^ 2)⁻¹) := (hcac.symm.pow_right 2).inv_right
      have hstep : gc' ^ 2 = z * ((ga ^ 2) ^ 2)⁻¹ := by
        rw [hgc'def, hcommgagc2.mul_pow, hcC, inv_pow]
      have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hz2)
      rw [hstep, hga2sq, hzinv, ← sq]; exact hz2
    have hψcgc' : ψc gc' = Multiplicative.ofAdd (1 : ZMod 2) := by
      rw [hgc'def, map_mul, map_inv, map_pow, hψcga, one_pow, inv_one, mul_one, hψcgc]
    have hcommbc' : Commute gb gc' := by
      rw [hgc'def]; exact hcbc.mul_right ((hcab.symm.pow_right 2).inv_right)
    have hψbgc' : ψb gc' = 1 := by
      rw [hgc'def, map_mul, map_inv, map_pow, hψbga, one_pow, inv_one, mul_one, hψbgc]
    have hindep : ∀ i j l : ℕ, i < 8 → j < 2 → l < 2 →
        ga ^ i * gb ^ j * gc' ^ l = 1 → i = 0 ∧ j = 0 ∧ l = 0 := by
      intro i j l hilt hjlt hllt hijl
      have h1 : ψb (ga ^ i * gb ^ j * gc' ^ l) = 1 := by rw [hijl]; exact map_one ψb
      simp only [map_mul, map_pow, hψbga, hψbgb, hψbgc', one_pow, one_mul, mul_one] at h1
      have hj0 : j = 0 := by
        have hdvd : orderOf (Multiplicative.ofAdd (1 : ZMod 2)) ∣ j := orderOf_dvd_of_pow_eq_one h1
        rw [hord2] at hdvd; exact Nat.eq_zero_of_dvd_of_lt hdvd hjlt
      subst hj0
      rw [pow_zero, mul_one] at hijl
      have h2 : ψc (ga ^ i * gc' ^ l) = 1 := by rw [hijl]; exact map_one ψc
      simp only [map_mul, map_pow, hψcga, hψcgc', one_pow, one_mul] at h2
      have hl0 : l = 0 := by
        have hdvd : orderOf (Multiplicative.ofAdd (1 : ZMod 2)) ∣ l := orderOf_dvd_of_pow_eq_one h2
        rw [hord2] at hdvd; exact Nat.eq_zero_of_dvd_of_lt hdvd hllt
      subst hl0
      rw [pow_zero, mul_one] at hijl
      have hdvd3 : orderOf ga ∣ i := orderOf_dvd_of_pow_eq_one hijl
      rw [hordga] at hdvd3
      exact ⟨Nat.eq_zero_of_dvd_of_lt hdvd3 hilt, rfl, rfl⟩
    exact three_commuting_gens_iso hG
      (by rw [← hordga]; exact pow_orderOf_eq_one ga) hcB hgc'sq
      hcab hcommgc' hcommbc' hindep (by norm_num)
  · -- (1,1,0): a doubled=8, b merges with a, c untouched
    left
    have hordga : orderOf ga = 8 :=
      order_double_of_pow_eq_central (by norm_num) hordga_4 hcA hz_ne_one hz2
    set gb' := gb * (ga ^ 2)⁻¹ with hgb'def
    have hcommgb' : Commute ga gb' := by
      rw [hgb'def]; exact hcab.mul_right (((Commute.refl ga).pow_right 2).inv_right)
    have hga2sq : (ga ^ 2) ^ 2 = z := by rw [← pow_mul]; exact hcA
    have hgb'sq : gb' ^ 2 = 1 := by
      have hcommgagb2 : Commute gb ((ga ^ 2)⁻¹) := (hcab.symm.pow_right 2).inv_right
      have hstep : gb' ^ 2 = z * ((ga ^ 2) ^ 2)⁻¹ := by
        rw [hgb'def, hcommgagb2.mul_pow, hcB, inv_pow]
      have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hz2)
      rw [hstep, hga2sq, hzinv, ← sq]; exact hz2
    have hψbgb' : ψb gb' = Multiplicative.ofAdd (1 : ZMod 2) := by
      rw [hgb'def, map_mul, map_inv, map_pow, hψbga, one_pow, inv_one, mul_one, hψbgb]
    have hcommb'c : Commute gb' gc := by
      rw [hgb'def]
      have h2 : Commute gc ((ga ^ 2)⁻¹) := (hcac.symm.pow_right 2).inv_right
      exact hcbc.mul_left h2.symm
    have hindep : ∀ i j l : ℕ, i < 8 → j < 2 → l < 2 →
        ga ^ i * gb' ^ j * gc ^ l = 1 → i = 0 ∧ j = 0 ∧ l = 0 := by
      intro i j l hilt hjlt hllt hijl
      have h1 : ψb (ga ^ i * gb' ^ j * gc ^ l) = 1 := by rw [hijl]; exact map_one ψb
      simp only [map_mul, map_pow, hψbga, hψbgb', hψbgc, one_pow, one_mul, mul_one] at h1
      have hj0 : j = 0 := by
        have hdvd : orderOf (Multiplicative.ofAdd (1 : ZMod 2)) ∣ j := orderOf_dvd_of_pow_eq_one h1
        rw [hord2] at hdvd; exact Nat.eq_zero_of_dvd_of_lt hdvd hjlt
      subst hj0
      rw [pow_zero, mul_one] at hijl
      have h2 : ψc (ga ^ i * gc ^ l) = 1 := by rw [hijl]; exact map_one ψc
      simp only [map_mul, map_pow, hψcga, hψcgc, one_pow, one_mul] at h2
      have hl0 : l = 0 := by
        have hdvd : orderOf (Multiplicative.ofAdd (1 : ZMod 2)) ∣ l := orderOf_dvd_of_pow_eq_one h2
        rw [hord2] at hdvd; exact Nat.eq_zero_of_dvd_of_lt hdvd hllt
      subst hl0
      rw [pow_zero, mul_one] at hijl
      have hdvd3 : orderOf ga ∣ i := orderOf_dvd_of_pow_eq_one hijl
      rw [hordga] at hdvd3
      exact ⟨Nat.eq_zero_of_dvd_of_lt hdvd3 hilt, rfl, rfl⟩
    exact three_commuting_gens_iso hG
      (by rw [← hordga]; exact pow_orderOf_eq_one ga) hgb'sq hcC
      hcommgb' hcac hcommb'c hindep (by norm_num)
  · -- (1,1,1): a doubled=8, b,c merge with a
    left
    have hordga : orderOf ga = 8 :=
      order_double_of_pow_eq_central (by norm_num) hordga_4 hcA hz_ne_one hz2
    set gb' := gb * (ga ^ 2)⁻¹ with hgb'def
    set gc' := gc * (ga ^ 2)⁻¹ with hgc'def
    have hcommgb' : Commute ga gb' := by
      rw [hgb'def]; exact hcab.mul_right (((Commute.refl ga).pow_right 2).inv_right)
    have hcommgc' : Commute ga gc' := by
      rw [hgc'def]; exact hcac.mul_right (((Commute.refl ga).pow_right 2).inv_right)
    have hcommbc' : Commute gb' gc' := by
      have h1 : Commute gb ((ga ^ 2)⁻¹) := (hcab.symm.pow_right 2).inv_right
      have h2 : Commute gc ((ga ^ 2)⁻¹) := (hcac.symm.pow_right 2).inv_right
      have h3 : Commute ((ga ^ 2)⁻¹ : G) ((ga ^ 2)⁻¹) := Commute.refl _
      have hb'c : Commute gb' gc := by rw [hgb'def]; exact hcbc.mul_left h2.symm
      have hb'ginv : Commute gb' ((ga ^ 2)⁻¹) := by rw [hgb'def]; exact h1.mul_left h3
      rw [hgc'def]; exact hb'c.mul_right hb'ginv
    have hga2sq : (ga ^ 2) ^ 2 = z := by rw [← pow_mul]; exact hcA
    have hgb'sq : gb' ^ 2 = 1 := by
      have hcommgagb2 : Commute gb ((ga ^ 2)⁻¹) := (hcab.symm.pow_right 2).inv_right
      have hstep : gb' ^ 2 = z * ((ga ^ 2) ^ 2)⁻¹ := by
        rw [hgb'def, hcommgagb2.mul_pow, hcB, inv_pow]
      have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hz2)
      rw [hstep, hga2sq, hzinv, ← sq]; exact hz2
    have hgc'sq : gc' ^ 2 = 1 := by
      have hcommgagc2 : Commute gc ((ga ^ 2)⁻¹) := (hcac.symm.pow_right 2).inv_right
      have hstep : gc' ^ 2 = z * ((ga ^ 2) ^ 2)⁻¹ := by
        rw [hgc'def, hcommgagc2.mul_pow, hcC, inv_pow]
      have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hz2)
      rw [hstep, hga2sq, hzinv, ← sq]; exact hz2
    have hψbgb' : ψb gb' = Multiplicative.ofAdd (1 : ZMod 2) := by
      rw [hgb'def, map_mul, map_inv, map_pow, hψbga, one_pow, inv_one, mul_one, hψbgb]
    have hψcgc' : ψc gc' = Multiplicative.ofAdd (1 : ZMod 2) := by
      rw [hgc'def, map_mul, map_inv, map_pow, hψcga, one_pow, inv_one, mul_one, hψcgc]
    have hψbgc' : ψb gc' = 1 := by
      rw [hgc'def, map_mul, map_inv, map_pow, hψbga, one_pow, inv_one, mul_one, hψbgc]
    have hindep : ∀ i j l : ℕ, i < 8 → j < 2 → l < 2 →
        ga ^ i * gb' ^ j * gc' ^ l = 1 → i = 0 ∧ j = 0 ∧ l = 0 := by
      intro i j l hilt hjlt hllt hijl
      have h1 : ψb (ga ^ i * gb' ^ j * gc' ^ l) = 1 := by rw [hijl]; exact map_one ψb
      simp only [map_mul, map_pow, hψbga, hψbgb', hψbgc', one_pow, one_mul, mul_one] at h1
      have hj0 : j = 0 := by
        have hdvd : orderOf (Multiplicative.ofAdd (1 : ZMod 2)) ∣ j := orderOf_dvd_of_pow_eq_one h1
        rw [hord2] at hdvd; exact Nat.eq_zero_of_dvd_of_lt hdvd hjlt
      subst hj0
      rw [pow_zero, mul_one] at hijl
      have h2 : ψc (ga ^ i * gc' ^ l) = 1 := by rw [hijl]; exact map_one ψc
      simp only [map_mul, map_pow, hψcga, hψcgc', one_pow, one_mul] at h2
      have hl0 : l = 0 := by
        have hdvd : orderOf (Multiplicative.ofAdd (1 : ZMod 2)) ∣ l := orderOf_dvd_of_pow_eq_one h2
        rw [hord2] at hdvd; exact Nat.eq_zero_of_dvd_of_lt hdvd hllt
      subst hl0
      rw [pow_zero, mul_one] at hijl
      have hdvd3 : orderOf ga ∣ i := orderOf_dvd_of_pow_eq_one hijl
      rw [hordga] at hdvd3
      exact ⟨Nat.eq_zero_of_dvd_of_lt hdvd3 hilt, rfl, rfl⟩
    exact three_commuting_gens_iso hG
      (by rw [← hordga]; exact pow_orderOf_eq_one ga) hgb'sq hgc'sq
      hcommgb' hcommgc' hcommbc' hindep (by norm_num)

end Smallgroups.UsefulTheorems
