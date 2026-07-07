/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order16_Wild
import Smallgroups.UsefulTheorems.PGroupGeneration
import Smallgroups.UsefulTheorems.Order32.GenericTools

/-! ## Descendants of `order16_wild_G12` (`C₄ ⋊ C₄` via inversion)

`order16_wild_G12 = order16_N3 = C₄ ⋊[φ] C₄` where `φ` sends the generator `b` of the acting
`C₄` to the automorphism `x ↦ x⁻¹` of the normal `C₄` (Wild's modular-type group built from
two order-`4` generators `a, b` with `b a b⁻¹ = a⁻¹`).  Since `a ≠ a⁻¹` generically, every
lift of this relation to `G` keeps `G` non-abelian: there is no "abelian-lift" branch here.
We record the simplest of the eight cocycle-bit combinations — all three relator bits
(`a⁴`, `b⁴`, and the conjugation defect) trivial — which realizes the split extension
`G ≃* order16_wild_G12 × C₂`. The other seven combinations (twisted conjugation and/or
`a`/`b` doubling to order `8`) are deferred. -/

namespace Smallgroups.UsefulTheorems

/-- The trivial-cocycle branch over `order16_wild_G12`: both relator bits `a⁴, b⁴` vanish
and the conjugation defect vanishes, so `G` splits as `order16_wild_G12 × C₂`. -/
theorem order32_of_c4c4inv_quotient_trivial_case {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 32) {z : G} (hzc : z ∈ Subgroup.center G) (hzp : orderOf z = 2)
    [hnorm : (Subgroup.zpowers z).Normal]
    (e : (G ⧸ Subgroup.zpowers z) ≃* order16_wild_G12)
    {ga gb : G}
    (hga : (QuotientGroup.mk' (Subgroup.zpowers z)) ga
      = e.symm (SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 4))))
    (hgb : (QuotientGroup.mk' (Subgroup.zpowers z)) gb
      = e.symm (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 4))))
    (hga4 : ga ^ 4 = 1) (hgb4 : gb ^ 4 = 1) (hrel : gb * ga * gb⁻¹ = ga⁻¹) :
    Nonempty (G ≃* order16_wild_G12 × Multiplicative (ZMod 2)) := by
  classical
  set φ := c4ActionAut 4 zmod4_unit_3 zmod4_unit_3_pow4 with hφdef
  set fn : Multiplicative (ZMod 4) →* G := zmodZPowHom 4 ga hga4 with hfndef
  set fg : Multiplicative (ZMod 4) →* G := zmodZPowHom 4 gb hgb4 with hfgdef
  have hfn_val : ∀ a : Multiplicative (ZMod 4), fn a = ga ^ (Multiplicative.toAdd a).val := by
    intro a
    have ha : a = Multiplicative.ofAdd (((Multiplicative.toAdd a).val : ZMod 4)) := by
      rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
    have hcast : ((((Multiplicative.toAdd a).val : ℕ) : ℤ) : ZMod 4)
        = ((Multiplicative.toAdd a).val : ZMod 4) := by push_cast; ring
    conv_lhs => rw [ha, ← hcast]
    rw [hfndef, zmodZPowHom_intCast, zpow_natCast]
  have hfg_val : ∀ b : Multiplicative (ZMod 4), fg b = gb ^ (Multiplicative.toAdd b).val := by
    intro b
    have hb : b = Multiplicative.ofAdd (((Multiplicative.toAdd b).val : ZMod 4)) := by
      rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
    have hcast : ((((Multiplicative.toAdd b).val : ℕ) : ℤ) : ZMod 4)
        = ((Multiplicative.toAdd b).val : ZMod 4) := by push_cast; ring
    conv_lhs => rw [hb, ← hcast]
    rw [hfgdef, zmodZPowHom_intCast, zpow_natCast]
  have hga3 : ga ^ 3 = ga⁻¹ := by
    have h34 : ga ^ 3 * ga ^ 1 = ga ^ 4 := by rw [← pow_add]
    rw [pow_one] at h34
    exact eq_inv_of_mul_eq_one_left (h34.trans hga4)
  have hgb3 : gb ^ 3 = gb⁻¹ := by
    have h34 : gb ^ 3 * gb ^ 1 = gb ^ 4 := by rw [← pow_add]
    rw [pow_one] at h34
    exact eq_inv_of_mul_eq_one_left (h34.trans hgb4)
  have hstep : ga = gb⁻¹ * ga⁻¹ * gb := by
    have h1 : gb⁻¹ * (gb * ga * gb⁻¹) * gb = gb⁻¹ * ga⁻¹ * gb := by rw [hrel]
    have h2 : gb⁻¹ * (gb * ga * gb⁻¹) * gb = ga := by group
    rw [h2] at h1
    exact h1
  have hrelinv : gb⁻¹ * ga * gb = ga⁻¹ := by
    have h3 : ga⁻¹ = (gb⁻¹ * ga⁻¹ * gb)⁻¹ := by rw [← hstep]
    rw [h3]; group
  have hrelinv2 : gb * ga⁻¹ * gb⁻¹ = ga := by
    have h1 : gb * (gb⁻¹ * ga * gb) * gb⁻¹ = gb * ga⁻¹ * gb⁻¹ := by rw [hrelinv]
    have h2 : gb * (gb⁻¹ * ga * gb) * gb⁻¹ = ga := by group
    rw [h2] at h1; exact h1.symm
  have hcomp : ∀ t : Multiplicative (ZMod 4),
      fn.comp (φ t).toMonoidHom = (MulAut.conj (fg t)).toMonoidHom.comp fn := by
    intro t
    apply monoidHom_ext_ofAdd_one
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hc4cases : ∀ x : Multiplicative (ZMod 4), x = 1 ∨ x = Multiplicative.ofAdd (1 : ZMod 4) ∨
        x = Multiplicative.ofAdd (2 : ZMod 4) ∨ x = Multiplicative.ofAdd (3 : ZMod 4) := by decide
    rcases hc4cases t with rfl | rfl | rfl | rfl
    · have e1 : φ (1 : Multiplicative (ZMod 4)) (Multiplicative.ofAdd (1 : ZMod 4))
          = Multiplicative.ofAdd (1 : ZMod 4) := by rw [hφdef]; decide
      simp only [e1, hfn_val, hfg_val]
      have hv0 : (Multiplicative.toAdd (1 : Multiplicative (ZMod 4))).val = 0 := by decide
      rw [hv0, pow_zero, one_mul, inv_one, mul_one]
    · have e1 : φ (Multiplicative.ofAdd (1 : ZMod 4)) (Multiplicative.ofAdd (1 : ZMod 4))
          = Multiplicative.ofAdd (3 : ZMod 4) := by rw [hφdef]; decide
      simp only [e1, hfn_val, hfg_val]
      have hv3 : (Multiplicative.toAdd (Multiplicative.ofAdd (3 : ZMod 4))).val = 3 := by decide
      have hv1 : (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 4))).val = 1 := by decide
      rw [hv3, hv1]
      simp only [pow_one]
      rw [hga3]
      exact hrel.symm
    · have e1 : φ (Multiplicative.ofAdd (2 : ZMod 4)) (Multiplicative.ofAdd (1 : ZMod 4))
          = Multiplicative.ofAdd (1 : ZMod 4) := by rw [hφdef]; decide
      simp only [e1, hfn_val, hfg_val]
      have hv1 : (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 4))).val = 1 := by decide
      have hv2 : (Multiplicative.toAdd (Multiplicative.ofAdd (2 : ZMod 4))).val = 2 := by decide
      rw [hv1, hv2]
      simp only [pow_one]
      have hstep2 : gb ^ 2 * ga * (gb ^ 2)⁻¹ = gb * (gb * ga * gb⁻¹) * gb⁻¹ := by
        rw [sq]; group
      rw [hstep2, hrel]
      exact hrelinv2.symm
    · have e1 : φ (Multiplicative.ofAdd (3 : ZMod 4)) (Multiplicative.ofAdd (1 : ZMod 4))
          = Multiplicative.ofAdd (3 : ZMod 4) := by rw [hφdef]; decide
      simp only [e1, hfn_val, hfg_val]
      have hv3 : (Multiplicative.toAdd (Multiplicative.ofAdd (3 : ZMod 4))).val = 3 := by decide
      have hv1 : (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 4))).val = 1 := by decide
      rw [hv3, hv1]
      simp only [pow_one]
      rw [hga3, hgb3, inv_inv]
      exact hrelinv.symm
  set s : order16_wild_G12 →* G := SemidirectProduct.lift fn fg hcomp with hsdef
  have hs_inl : ∀ a : Multiplicative (ZMod 4), s (SemidirectProduct.inl a) = fn a := by
    intro a; rw [hsdef]; exact SemidirectProduct.lift_inl fn fg hcomp a
  have hs_inr : ∀ b : Multiplicative (ZMod 4), s (SemidirectProduct.inr b) = fg b := by
    intro b; rw [hsdef]; exact SemidirectProduct.lift_inr fn fg hcomp b
  have hz2 : z ^ 2 = 1 := by rw [← hzp]; exact pow_orderOf_eq_one z
  have hzne1 : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hzp; exact absurd hzp (by norm_num)
  have hzker : z ∈ (QuotientGroup.mk' (Subgroup.zpowers z)).ker := by
    rw [QuotientGroup.ker_mk']; exact Subgroup.mem_zpowers z
  have hπz : (QuotientGroup.mk' (Subgroup.zpowers z)) z = 1 := MonoidHom.mem_ker.mp hzker
  have hπga : (QuotientGroup.mk' (Subgroup.zpowers z)) ga
      = e.symm (SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 4))) := hga
  have hπgb : (QuotientGroup.mk' (Subgroup.zpowers z)) gb
      = e.symm (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 4))) := hgb
  have hπs : ∀ q : order16_wild_G12,
      (QuotientGroup.mk' (Subgroup.zpowers z)) (s q) = e.symm q := by
    have hgen : (QuotientGroup.mk' (Subgroup.zpowers z)).comp s = e.symm.toMonoidHom := by
      apply SemidirectProduct.hom_ext
      · apply MonoidHom.ext; intro a
        rw [zmod_pow_eq_ofAdd_one_pow a, map_pow, map_pow]
        simp only [MonoidHom.comp_apply, hs_inl, hfn_val, MulEquiv.coe_toMonoidHom]
        rw [show (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 4))).val = 1 from by
          decide, pow_one, hπga]
      · apply MonoidHom.ext; intro b
        rw [zmod_pow_eq_ofAdd_one_pow b, map_pow, map_pow]
        simp only [MonoidHom.comp_apply, hs_inr, hfg_val, MulEquiv.coe_toMonoidHom]
        rw [show (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 4))).val = 1 from by
          decide, pow_one, hπgb]
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
  have hzrange : ∀ q : order16_wild_G12, s q = z → q = 1 := by
    intro q hqz
    have h1 := hπs q
    rw [hqz, hπz] at h1
    have h2 : q = e 1 := by
      have := congrArg e h1.symm
      simpa using this
    rw [h2, map_one]
  exact central_ext_split_iso_prod hG (card_order16_wild_G12) hzc hzp s hs_inj hzrange

end Smallgroups.UsefulTheorems
