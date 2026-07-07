/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order16_Wild
import Smallgroups.UsefulTheorems.PGroupGeneration
import Smallgroups.UsefulTheorems.Order32.GenericTools

/-! ## Descendants of `order16_wild_G8` (`K₈ ⋊ C₂` via `ψ₃`, `D₈ × C₂`)

`order16_wild_G8 = K₈ ⋊[ψ₃] C₂` where `K₈ = C₄ × C₂` (generators `x` order `4`, `y` order
`2`, commuting) and `ψ₃ : (x,y) ↦ (x⁻¹,y)`, i.e. `bxb⁻¹ = x⁻¹`, `byb⁻¹ = y`. Only the
trivial-cocycle branch is recorded: all three relator bits (`x⁴`, `y²`, `b²`) vanish, the
lifts of `x,y` commute exactly, and the two conjugation relations hold exactly. -/

namespace Smallgroups.UsefulTheorems

/-- The trivial-cocycle branch over `order16_wild_G8`: all relator bits vanish and the
conjugation defects vanish, so `G` splits as `order16_wild_G8 × C₂`. -/
theorem order32_of_k8c2_d8xc2_quotient_trivial_case {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 32) {z : G} (hzc : z ∈ Subgroup.center G) (hzp : orderOf z = 2)
    [hnorm : (Subgroup.zpowers z).Normal]
    (e : (G ⧸ Subgroup.zpowers z) ≃* order16_wild_G8)
    {ga gb gc : G}
    (hga : (QuotientGroup.mk' (Subgroup.zpowers z)) ga
      = e.symm (SemidirectProduct.inl (xK8 : K8g)))
    (hgb : (QuotientGroup.mk' (Subgroup.zpowers z)) gb
      = e.symm (SemidirectProduct.inl (yK8 : K8g)))
    (hgc : (QuotientGroup.mk' (Subgroup.zpowers z)) gc
      = e.symm (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))))
    (hga4 : ga ^ 4 = 1) (hgb2 : gb ^ 2 = 1) (hgc2 : gc ^ 2 = 1) (hcommab : Commute ga gb)
    (hrelgca : gc * ga * gc⁻¹ = ga⁻¹) (hcommgcb : Commute gc gb) :
    Nonempty (G ≃* order16_wild_G8 × Multiplicative (ZMod 2)) := by
  classical
  set φ := c2Action_psi3 with hφdef
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
  have hconjpow : ∀ k : ℕ, gc * ga ^ k * gc⁻¹ = (gc * ga * gc⁻¹) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
      have hstep : gc * ga ^ (n + 1) * gc⁻¹ = (gc * ga ^ n * gc⁻¹) * (gc * ga * gc⁻¹) := by
        rw [pow_succ]; group
      rw [hstep, ih, ← pow_succ]
  have hconjga : ∀ a : Multiplicative (ZMod 4), gc * fg1 a * gc⁻¹ = (fg1 a)⁻¹ := by
    intro a
    rw [hfg1_val, hconjpow, hrelgca, inv_pow]
  have hconjgb : ∀ b : Multiplicative (ZMod 2), gc * fg2 b * gc⁻¹ = fg2 b := by
    intro b
    rw [hfg2_val]
    have hcommpow : gc * gb ^ (Multiplicative.toAdd b).val
        = gb ^ (Multiplicative.toAdd b).val * gc := hcommgcb.pow_right _
    rw [hcommpow, mul_inv_cancel_right]
  have hcomp : ∀ t : Multiplicative (ZMod 2),
      fn.comp (φ t).toMonoidHom = (MulAut.conj (fg t)).toMonoidHom.comp fn := by
    have hc2cases : ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = Multiplicative.ofAdd (1 : ZMod 2) :=
      by decide
    have hphi1 : ∀ p : K8g, φ (1 : Multiplicative (ZMod 2)) p = p := by rw [hφdef]; decide
    have hpsi : ∀ p : K8g, φ (Multiplicative.ofAdd (1 : ZMod 2)) p = (p.1⁻¹, p.2) := by
      rw [hφdef]; decide
    intro t
    rcases hc2cases t with rfl | rfl
    · apply MonoidHom.ext; rintro ⟨a, b⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hphi1]
      rw [map_one, one_mul, inv_one, mul_one]
    · apply MonoidHom.ext; rintro ⟨a, b⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hpsi]
      have hfgc : fg (Multiplicative.ofAdd (1 : ZMod 2)) = gc := by
        rw [hfgdef]
        have h := zmodZPowHom_intCast 2 gc hgc2 1
        simp only [Int.cast_one, zpow_one] at h
        exact h
      have hfna : fn (a⁻¹, b) = (fg1 a)⁻¹ * fg2 b := by
        rw [hfndef, MonoidHom.noncommCoprod_apply, map_inv]
      have hfnab : fn (a, b) = fg1 a * fg2 b := by rw [hfndef, MonoidHom.noncommCoprod_apply]
      rw [hfgc, hfna, hfnab]
      rw [show gc * (fg1 a * fg2 b) * gc⁻¹ = (gc * fg1 a * gc⁻¹) * (gc * fg2 b * gc⁻¹) from by
        group]
      rw [hconjga a, hconjgb b]
  set s : order16_wild_G8 →* G := SemidirectProduct.lift fn fg hcomp with hsdef
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
  have hπs : ∀ q : order16_wild_G8,
      (QuotientGroup.mk' (Subgroup.zpowers z)) (s q) = e.symm q := by
    have hgen : (QuotientGroup.mk' (Subgroup.zpowers z)).comp s = e.symm.toMonoidHom := by
      apply SemidirectProduct.hom_ext
      · apply monoidHom_ext_prod_ofAdd_one
        · change (QuotientGroup.mk' (Subgroup.zpowers z)) (s (SemidirectProduct.inl (xK8 : K8g)))
              = e.symm (SemidirectProduct.inl (xK8 : K8g))
          rw [hs_inl]
          change (QuotientGroup.mk' (Subgroup.zpowers z)) (fg1 (Multiplicative.ofAdd (1 : ZMod 4))
              * fg2 1) = _
          rw [fg2.map_one, mul_one]
          have hfg1g : fg1 (Multiplicative.ofAdd (1 : ZMod 4)) = ga := by
            rw [hfg1def]
            have h := zmodZPowHom_intCast 4 ga hga4 1
            simp only [Int.cast_one, zpow_one] at h
            exact h
          rw [hfg1g, hπga]
        · change (QuotientGroup.mk' (Subgroup.zpowers z)) (s (SemidirectProduct.inl (yK8 : K8g)))
              = e.symm (SemidirectProduct.inl (yK8 : K8g))
          rw [hs_inl]
          change (QuotientGroup.mk' (Subgroup.zpowers z)) (fg1 1
              * fg2 (Multiplicative.ofAdd (1 : ZMod 2))) = _
          rw [fg1.map_one, one_mul]
          have hfg2g : fg2 (Multiplicative.ofAdd (1 : ZMod 2)) = gb := by
            rw [hfg2def]
            have h := zmodZPowHom_intCast 2 gb hgb2 1
            simp only [Int.cast_one, zpow_one] at h
            exact h
          rw [hfg2g, hπgb]
      · apply MonoidHom.ext; intro t
        rw [zmod_pow_eq_ofAdd_one_pow t, map_pow, map_pow]
        simp only [MonoidHom.comp_apply, hs_inr, hfgdef, MulEquiv.coe_toMonoidHom]
        have hb : (zmodZPowHom 2 gc hgc2) (Multiplicative.ofAdd (1 : ZMod 2)) = gc := by
          have h := zmodZPowHom_intCast 2 gc hgc2 1
          simp only [Int.cast_one, zpow_one] at h
          exact h
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
  have hzrange : ∀ q : order16_wild_G8, s q = z → q = 1 := by
    intro q hqz
    have h1 := hπs q
    rw [hqz, hπz] at h1
    have h2 : q = e 1 := by
      have := congrArg e h1.symm
      simpa using this
    rw [h2, map_one]
  exact central_ext_split_iso_prod hG (card_order16_wild_G8) hzc hzp s hs_inj hzrange

end Smallgroups.UsefulTheorems
