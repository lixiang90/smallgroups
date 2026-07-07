/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order16_Wild
import Smallgroups.UsefulTheorems.PGroupGeneration
import Smallgroups.UsefulTheorems.Order32.GenericTools

/-! ## Descendants of `order16_wild_G9` (`K₈ ⋊ C₂` via `ψ₅`, `K₄ ⋊ C₄`)

`order16_wild_G9 = K₈ ⋊[ψ₅] C₂` where `ψ₅ : (x,y) ↦ (x, π(x)·y)` (`π : C₄ → C₂` the natural
projection), i.e. `bxb⁻¹ = xy`, `byb⁻¹ = y`. Only the trivial-cocycle branch is recorded. -/

namespace Smallgroups.UsefulTheorems

/-- The trivial-cocycle branch over `order16_wild_G9`: all relator bits vanish and the
conjugation defects vanish, so `G` splits as `order16_wild_G9 × C₂`. -/
theorem order32_of_k8c2_psi5_quotient_trivial_case {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 32) {z : G} (hzc : z ∈ Subgroup.center G) (hzp : orderOf z = 2)
    [hnorm : (Subgroup.zpowers z).Normal]
    (e : (G ⧸ Subgroup.zpowers z) ≃* order16_wild_G9)
    {ga gb gc : G}
    (hga : (QuotientGroup.mk' (Subgroup.zpowers z)) ga
      = e.symm (SemidirectProduct.inl (xK8 : K8g)))
    (hgb : (QuotientGroup.mk' (Subgroup.zpowers z)) gb
      = e.symm (SemidirectProduct.inl (yK8 : K8g)))
    (hgc : (QuotientGroup.mk' (Subgroup.zpowers z)) gc
      = e.symm (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))))
    (hga4 : ga ^ 4 = 1) (hgb2 : gb ^ 2 = 1) (hgc2 : gc ^ 2 = 1) (hcommab : Commute ga gb)
    (hrelgca : gc * ga * gc⁻¹ = ga * gb) (hcommgcb : Commute gc gb) :
    Nonempty (G ≃* order16_wild_G9 × Multiplicative (ZMod 2)) := by
  classical
  set φ := c2Action_psi5 with hφdef
  set fg1 : Multiplicative (ZMod 4) →* G := zmodZPowHom 4 ga hga4 with hfg1def
  set fg2 : Multiplicative (ZMod 2) →* G := zmodZPowHom 2 gb hgb2 with hfg2def
  have hfg1_val : ∀ a : Multiplicative (ZMod 4), fg1 a = ga ^ (Multiplicative.toAdd a).val := by
    intro a
    have ha : a = Multiplicative.ofAdd (((Multiplicative.toAdd a).val : ZMod 4)) := by
      rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
    have hcast : ((((Multiplicative.toAdd a).val : ℕ) : ℤ) : ZMod 4)
        = ((Multiplicative.toAdd a).val : ZMod 4) := by push_cast; ring
    conv_lhs => rw [ha, ← hcast]
    rw [hfg1def, zmodZPowHom_intCast, zpow_natCast]
  have hfg2_val : ∀ b : Multiplicative (ZMod 2), fg2 b = gb ^ (Multiplicative.toAdd b).val := by
    intro b
    have hb : b = Multiplicative.ofAdd (((Multiplicative.toAdd b).val : ZMod 2)) := by
      rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
    have hcast : ((((Multiplicative.toAdd b).val : ℕ) : ℤ) : ZMod 2)
        = ((Multiplicative.toAdd b).val : ZMod 2) := by push_cast; ring
    conv_lhs => rw [hb, ← hcast]
    rw [hfg2def, zmodZPowHom_intCast, zpow_natCast]
  have hcomm' : ∀ (a : Multiplicative (ZMod 4)) (b : Multiplicative (ZMod 2)),
      Commute (fg1 a) (fg2 b) := by
    intro a b; rw [hfg1_val, hfg2_val]; exact hcommab.pow_pow _ _
  set fn : K8g →* G := fg1.noncommCoprod fg2 hcomm' with hfndef
  set fg : Multiplicative (ZMod 2) →* G := zmodZPowHom 2 gc hgc2 with hfgdef
  have hfnxK8 : fn (xK8 : K8g) = ga := by
    rw [hfndef, MonoidHom.noncommCoprod_apply]
    change fg1 (Multiplicative.ofAdd (1 : ZMod 4)) * fg2 1 = ga
    have hfg1g : fg1 (Multiplicative.ofAdd (1 : ZMod 4)) = ga := by
      rw [hfg1def]
      have h := zmodZPowHom_intCast 4 ga hga4 1
      simp only [Int.cast_one, zpow_one] at h
      exact h
    rw [fg2.map_one, mul_one, hfg1g]
  have hfnyK8 : fn (yK8 : K8g) = gb := by
    rw [hfndef, MonoidHom.noncommCoprod_apply]
    change fg1 1 * fg2 (Multiplicative.ofAdd (1 : ZMod 2)) = gb
    have hfg2g : fg2 (Multiplicative.ofAdd (1 : ZMod 2)) = gb := by
      rw [hfg2def]
      have h := zmodZPowHom_intCast 2 gb hgb2 1
      simp only [Int.cast_one, zpow_one] at h
      exact h
    rw [fg1.map_one, one_mul, hfg2g]
  have hfgc : fg (Multiplicative.ofAdd (1 : ZMod 2)) = gc := by
    rw [hfgdef]
    have h := zmodZPowHom_intCast 2 gc hgc2 1
    simp only [Int.cast_one, zpow_one] at h
    exact h
  have hcomp : ∀ t : Multiplicative (ZMod 2),
      fn.comp (φ t).toMonoidHom = (MulAut.conj (fg t)).toMonoidHom.comp fn := by
    have hc2cases : ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = Multiplicative.ofAdd (1 : ZMod 2) :=
      by decide
    have hphi1 : ∀ p : K8g, φ (1 : Multiplicative (ZMod 2)) p = p := by rw [hφdef]; decide
    have hxK8val : φ (Multiplicative.ofAdd (1 : ZMod 2)) (xK8 : K8g) = xK8 * yK8 := by
      rw [hφdef]; decide
    have hyK8val : φ (Multiplicative.ofAdd (1 : ZMod 2)) (yK8 : K8g) = yK8 := by
      rw [hφdef]; decide
    intro t
    rcases hc2cases t with rfl | rfl
    · apply monoidHom_ext_prod_ofAdd_one
      · change fn (φ (1 : Multiplicative (ZMod 2)) (xK8 : K8g))
            = fg 1 * fn (xK8 : K8g) * (fg 1)⁻¹
        rw [hphi1, fg.map_one, one_mul, inv_one, mul_one]
      · change fn (φ (1 : Multiplicative (ZMod 2)) (yK8 : K8g))
            = fg 1 * fn (yK8 : K8g) * (fg 1)⁻¹
        rw [hphi1, fg.map_one, one_mul, inv_one, mul_one]
    · apply monoidHom_ext_prod_ofAdd_one
      · change fn (φ (Multiplicative.ofAdd (1 : ZMod 2)) (xK8 : K8g))
            = fg (Multiplicative.ofAdd (1 : ZMod 2)) * fn (xK8 : K8g)
              * (fg (Multiplicative.ofAdd (1 : ZMod 2)))⁻¹
        rw [hxK8val, map_mul, hfnxK8, hfnyK8, hfgc, hrelgca]
      · change fn (φ (Multiplicative.ofAdd (1 : ZMod 2)) (yK8 : K8g))
            = fg (Multiplicative.ofAdd (1 : ZMod 2)) * fn (yK8 : K8g)
              * (fg (Multiplicative.ofAdd (1 : ZMod 2)))⁻¹
        have hcommpow : gc * gb = gb * gc := hcommgcb
        rw [hyK8val, hfnyK8, hfgc, hcommpow, mul_inv_cancel_right]
  set s : order16_wild_G9 →* G := SemidirectProduct.lift fn fg hcomp with hsdef
  have hs_inl : ∀ p : K8g, s (SemidirectProduct.inl p) = fn p := by
    intro p; rw [hsdef]; exact SemidirectProduct.lift_inl fn fg hcomp p
  have hs_inr : ∀ t : Multiplicative (ZMod 2), s (SemidirectProduct.inr t) = fg t := by
    intro t; rw [hsdef]; exact SemidirectProduct.lift_inr fn fg hcomp t
  have hz2 : z ^ 2 = 1 := by rw [← hzp]; exact pow_orderOf_eq_one z
  have hzne1 : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hzp; exact absurd hzp (by norm_num)
  have hzker : z ∈ (QuotientGroup.mk' (Subgroup.zpowers z)).ker := by
    rw [QuotientGroup.ker_mk']; exact Subgroup.mem_zpowers z
  have hπz : (QuotientGroup.mk' (Subgroup.zpowers z)) z = 1 := MonoidHom.mem_ker.mp hzker
  have hπga : (QuotientGroup.mk' (Subgroup.zpowers z)) ga
      = e.symm (SemidirectProduct.inl (xK8 : K8g)) := hga
  have hπgb : (QuotientGroup.mk' (Subgroup.zpowers z)) gb
      = e.symm (SemidirectProduct.inl (yK8 : K8g)) := hgb
  have hπgc : (QuotientGroup.mk' (Subgroup.zpowers z)) gc
      = e.symm (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))) := hgc
  have hπs : ∀ q : order16_wild_G9,
      (QuotientGroup.mk' (Subgroup.zpowers z)) (s q) = e.symm q := by
    have hgen : (QuotientGroup.mk' (Subgroup.zpowers z)).comp s = e.symm.toMonoidHom := by
      apply SemidirectProduct.hom_ext
      · apply monoidHom_ext_prod_ofAdd_one
        · change (QuotientGroup.mk' (Subgroup.zpowers z)) (s (SemidirectProduct.inl (xK8 : K8g)))
              = e.symm (SemidirectProduct.inl (xK8 : K8g))
          rw [hs_inl, hfnxK8, hπga]
        · change (QuotientGroup.mk' (Subgroup.zpowers z)) (s (SemidirectProduct.inl (yK8 : K8g)))
              = e.symm (SemidirectProduct.inl (yK8 : K8g))
          rw [hs_inl, hfnyK8, hπgb]
      · apply MonoidHom.ext; intro t
        rw [zmod_pow_eq_ofAdd_one_pow t, map_pow, map_pow]
        simp only [MonoidHom.comp_apply, hs_inr, hfgdef, MulEquiv.coe_toMonoidHom]
        have hb : (zmodZPowHom 2 gc hgc2) (Multiplicative.ofAdd (1 : ZMod 2)) = gc := by
          rw [← hfgdef]; exact hfgc
        rw [hb, hπgc]
    intro q
    have := DFunLike.congr_fun hgen q
    simpa using this
  have hs_inj : Function.Injective s := by
    intro q1 q2 hq
    have h1 := hπs q1
    have h2 := hπs q2
    rw [hq] at h1
    have : e.symm q1 = e.symm q2 := h1.symm.trans h2
    exact e.symm.injective this
  have hzrange : ∀ q : order16_wild_G9, s q = z → q = 1 := by
    intro q hqz
    have h1 := hπs q
    rw [hqz, hπz] at h1
    have h2 : q = e 1 := by
      have := congrArg e h1.symm
      simpa using this
    rw [h2, map_one]
  exact central_ext_split_iso_prod hG (card_order16_wild_G9) hzc hzp s hs_inj hzrange

end Smallgroups.UsefulTheorems
