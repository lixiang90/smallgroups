/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order16_Wild
import Smallgroups.UsefulTheorems.PGroupGeneration
import Smallgroups.UsefulTheorems.Order32.GenericTools

/-! ## Descendants of `order16_wild_G3` (`C₈ ⋊ C₂` via unit `5`)

`order16_wild_G3 = C₈ ⋊[φ₃] C₂` where `φ₃` sends the generator `b` of `C₂` to the
automorphism `x ↦ x⁵` of `C₈` (`bab⁻¹ = a⁵`). Same shape as `G2`; only the trivial-cocycle
branch is recorded. -/

namespace Smallgroups.UsefulTheorems

/-- The trivial-cocycle branch over `order16_wild_G3`: both relator bits `a⁸, b²` vanish
and the conjugation defect vanishes, so `G` splits as `order16_wild_G3 × C₂`. -/
theorem order32_of_c8c2u5_quotient_trivial_case {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 32) {z : G} (hzc : z ∈ Subgroup.center G) (hzp : orderOf z = 2)
    [hnorm : (Subgroup.zpowers z).Normal]
    (e : (G ⧸ Subgroup.zpowers z) ≃* order16_wild_G3)
    {ga gb : G}
    (hga : (QuotientGroup.mk' (Subgroup.zpowers z)) ga
      = e.symm (SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 8))))
    (hgb : (QuotientGroup.mk' (Subgroup.zpowers z)) gb
      = e.symm (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))))
    (hga8 : ga ^ 8 = 1) (hgb2 : gb ^ 2 = 1) (hrel : gb * ga * gb⁻¹ = ga ^ 5) :
    Nonempty (G ≃* order16_wild_G3 × Multiplicative (ZMod 2)) := by
  classical
  set φ := c2Action_phi3 with hφdef
  set fn : Multiplicative (ZMod 8) →* G := zmodZPowHom 8 ga hga8 with hfndef
  set fg : Multiplicative (ZMod 2) →* G := zmodZPowHom 2 gb hgb2 with hfgdef
  have hfn_val : ∀ a : Multiplicative (ZMod 8), fn a = ga ^ (Multiplicative.toAdd a).val := by
    intro a
    have ha : a = Multiplicative.ofAdd (((Multiplicative.toAdd a).val : ZMod 8)) := by
      rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
    have hcast : ((((Multiplicative.toAdd a).val : ℕ) : ℤ) : ZMod 8)
        = ((Multiplicative.toAdd a).val : ZMod 8) := by push_cast; ring
    conv_lhs => rw [ha, ← hcast]
    rw [hfndef, zmodZPowHom_intCast, zpow_natCast]
  have hfg_val : ∀ b : Multiplicative (ZMod 2), fg b = gb ^ (Multiplicative.toAdd b).val := by
    intro b
    have hb : b = Multiplicative.ofAdd (((Multiplicative.toAdd b).val : ZMod 2)) := by
      rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
    have hcast : ((((Multiplicative.toAdd b).val : ℕ) : ℤ) : ZMod 2)
        = ((Multiplicative.toAdd b).val : ZMod 2) := by push_cast; ring
    conv_lhs => rw [hb, ← hcast]
    rw [hfgdef, zmodZPowHom_intCast, zpow_natCast]
  have hcomp : ∀ t : Multiplicative (ZMod 2),
      fn.comp (φ t).toMonoidHom = (MulAut.conj (fg t)).toMonoidHom.comp fn := by
    intro t
    apply monoidHom_ext_ofAdd_one
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hc2cases : ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = Multiplicative.ofAdd (1 : ZMod 2) :=
      by decide
    rcases hc2cases t with rfl | rfl
    · have e1 : φ (1 : Multiplicative (ZMod 2)) (Multiplicative.ofAdd (1 : ZMod 8))
          = Multiplicative.ofAdd (1 : ZMod 8) := by rw [hφdef]; decide
      simp only [e1, hfn_val, hfg_val]
      have hv0 : (Multiplicative.toAdd (1 : Multiplicative (ZMod 2))).val = 0 := by decide
      rw [hv0, pow_zero, one_mul, inv_one, mul_one]
    · have e1 : φ (Multiplicative.ofAdd (1 : ZMod 2)) (Multiplicative.ofAdd (1 : ZMod 8))
          = Multiplicative.ofAdd (5 : ZMod 8) := by rw [hφdef]; decide
      simp only [e1, hfn_val, hfg_val]
      have hv5 : (Multiplicative.toAdd (Multiplicative.ofAdd (5 : ZMod 8))).val = 5 := by decide
      have hv1 : (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2))).val = 1 := by decide
      have hv1' : (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 8))).val = 1 := by decide
      rw [hv5, hv1, hv1']
      simp only [pow_one]
      exact hrel.symm
  set s : order16_wild_G3 →* G := SemidirectProduct.lift fn fg hcomp with hsdef
  have hs_inl : ∀ a : Multiplicative (ZMod 8), s (SemidirectProduct.inl a) = fn a := by
    intro a; rw [hsdef]; exact SemidirectProduct.lift_inl fn fg hcomp a
  have hs_inr : ∀ b : Multiplicative (ZMod 2), s (SemidirectProduct.inr b) = fg b := by
    intro b; rw [hsdef]; exact SemidirectProduct.lift_inr fn fg hcomp b
  have hz2 : z ^ 2 = 1 := by rw [← hzp]; exact pow_orderOf_eq_one z
  have hzne1 : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hzp; exact absurd hzp (by norm_num)
  have hzker : z ∈ (QuotientGroup.mk' (Subgroup.zpowers z)).ker := by
    rw [QuotientGroup.ker_mk']; exact Subgroup.mem_zpowers z
  have hπz : (QuotientGroup.mk' (Subgroup.zpowers z)) z = 1 := MonoidHom.mem_ker.mp hzker
  have hπga : (QuotientGroup.mk' (Subgroup.zpowers z)) ga
      = e.symm (SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 8))) := hga
  have hπgb : (QuotientGroup.mk' (Subgroup.zpowers z)) gb
      = e.symm (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))) := hgb
  have hπs : ∀ q : order16_wild_G3,
      (QuotientGroup.mk' (Subgroup.zpowers z)) (s q) = e.symm q := by
    have hgen : (QuotientGroup.mk' (Subgroup.zpowers z)).comp s = e.symm.toMonoidHom := by
      apply SemidirectProduct.hom_ext
      · apply MonoidHom.ext; intro a
        rw [zmod_pow_eq_ofAdd_one_pow a, map_pow, map_pow]
        simp only [MonoidHom.comp_apply, hs_inl, hfn_val, MulEquiv.coe_toMonoidHom]
        rw [show (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 8))).val = 1 from by
          decide, pow_one, hπga]
      · apply MonoidHom.ext; intro b
        rw [zmod_pow_eq_ofAdd_one_pow b, map_pow, map_pow]
        simp only [MonoidHom.comp_apply, hs_inr, hfg_val, MulEquiv.coe_toMonoidHom]
        rw [show (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2))).val = 1 from by
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
  have hzrange : ∀ q : order16_wild_G3, s q = z → q = 1 := by
    intro q hqz
    have h1 := hπs q
    rw [hqz, hπz] at h1
    have h2 : q = e 1 := by
      have := congrArg e h1.symm
      simpa using this
    rw [h2, map_one]
  exact central_ext_split_iso_prod hG (card_order16_wild_G3) hzc hzp s hs_inj hzrange

/-! ## Twisted / doubled branches: `order16_wild_G3` descendants (continued)

Beyond the split branch, `G2 = C₈ ⋊[φ₂] C₂` has 7 more cocycle-bit combinations. Here we
handle the "`b` doubles" case: `a⁸ = 1` (untouched), `b² = z` (so `b` lifts to order `4`),
and the conjugation relation holds exactly (`bab⁻¹ = a³`, not `a³z`). This produces a
genuinely new order-32 group `C₈ ⋊[φ₄] C₄`, where `φ₄` is the order-`2` automorphism
`x ↦ x³` of `C₈`, now acted on by `C₄` through its quotient `C₄ ↠ C₂`. -/

/-- Reduction homomorphism `C₄ ↠ C₂` (mod-2 cast on `ZMod 4`), used to factor the `C₄`-action
through the existing `C₂`-action `c2Action_phi3`. -/
private noncomputable def redHom42 : Multiplicative (ZMod 4) →* Multiplicative (ZMod 2) :=
  AddMonoidHom.toMultiplicative (ZMod.castHom (by norm_num) (ZMod 2)).toAddMonoidHom

/-- The `C₄`-action on `C₈` obtained by factoring `φ₂` (unit `3`) through `C₄ ↠ C₂`. -/
private noncomputable def phi4Act : Multiplicative (ZMod 4) →* MulAut C8g :=
  c2Action_phi3.comp redHom42

/-- The new order-32 group `C₈ ⋊[φ₄] C₄` (the `b`-doubled descendant of `G3`). -/
noncomputable abbrev order32_c8c4_u5 : Type :=
  SemidirectProduct C8g (Multiplicative (ZMod 4)) phi4Act

@[simp] theorem card_order32_c8c4_u5 : Nat.card order32_c8c4_u5 = 32 := by
  rw [SemidirectProduct.card]; simp

/-- The `b`-doubled branch over `order16_wild_G3`: `a⁸=1`, `b²=z`, `bab⁻¹=a^5` (exact).
`G` is isomorphic to the new order-32 group `C₈ ⋊[φ₄] C₄`. -/
theorem order32_of_c8c2u5_quotient_doubled_b_case {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 32) {z : G} (hzc : z ∈ Subgroup.center G) (hzp : orderOf z = 2)
    [hnorm : (Subgroup.zpowers z).Normal]
    (e : (G ⧸ Subgroup.zpowers z) ≃* order16_wild_G3)
    {ga gb : G}
    (hga : (QuotientGroup.mk' (Subgroup.zpowers z)) ga
      = e.symm (SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 8))))
    (hgb : (QuotientGroup.mk' (Subgroup.zpowers z)) gb
      = e.symm (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))))
    (hga8 : ga ^ 8 = 1) (hgb2 : gb ^ 2 = z) (hrel : gb * ga * gb⁻¹ = ga ^ 5) :
    Nonempty (G ≃* order32_c8c4_u5) := by
  classical
  have hz2 : z ^ 2 = 1 := by rw [← hzp]; exact pow_orderOf_eq_one z
  have hzne1 : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hzp; exact absurd hzp (by norm_num)
  have hzcentral : ∀ g : G, Commute z g := fun g => (Subgroup.mem_center_iff.mp hzc g).symm
  have hgb4 : gb ^ 4 = 1 := by
    have hh : gb ^ 4 = (gb ^ 2) ^ 2 := by rw [← pow_mul]
    rw [hh, hgb2, hz2]
  set fn : C8g →* G := zmodZPowHom 8 ga hga8 with hfndef
  set fg : Multiplicative (ZMod 4) →* G := zmodZPowHom 4 gb hgb4 with hfgdef
  have hfn_val : ∀ a : C8g, fn a = ga ^ (Multiplicative.toAdd a).val := by
    intro a
    have ha : a = Multiplicative.ofAdd (((Multiplicative.toAdd a).val : ZMod 8)) := by
      rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
    have hcast : ((((Multiplicative.toAdd a).val : ℕ) : ℤ) : ZMod 8)
        = ((Multiplicative.toAdd a).val : ZMod 8) := by push_cast; ring
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
  have hcomp : ∀ t : Multiplicative (ZMod 4),
      fn.comp (phi4Act t).toMonoidHom = (MulAut.conj (fg t)).toMonoidHom.comp fn := by
    intro t
    apply monoidHom_ext_ofAdd_one
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hc4cases : ∀ x : Multiplicative (ZMod 4),
        x = 1 ∨ x = Multiplicative.ofAdd (1 : ZMod 4) ∨ x = Multiplicative.ofAdd (2 : ZMod 4)
          ∨ x = Multiplicative.ofAdd (3 : ZMod 4) := by decide
    rcases hc4cases t with rfl | rfl | rfl | rfl
    · have e1 : phi4Act (1 : Multiplicative (ZMod 4)) (Multiplicative.ofAdd (1 : ZMod 8))
          = Multiplicative.ofAdd (1 : ZMod 8) := by
        change c2Action_phi3 (redHom42 1) _ = _
        rw [show redHom42 (1 : Multiplicative (ZMod 4)) = 1 from by
          apply congrArg Multiplicative.ofAdd; decide]
        decide
      simp only [e1, hfn_val, hfg_val]
      have hv0 : (Multiplicative.toAdd (1 : Multiplicative (ZMod 4))).val = 0 := by decide
      rw [hv0, pow_zero, one_mul, inv_one, mul_one]
    · have e1 : phi4Act (Multiplicative.ofAdd (1 : ZMod 4)) (Multiplicative.ofAdd (1 : ZMod 8))
          = Multiplicative.ofAdd (5 : ZMod 8) := by
        change c2Action_phi3 (redHom42 (Multiplicative.ofAdd (1 : ZMod 4))) _ = _
        rw [show redHom42 (Multiplicative.ofAdd (1 : ZMod 4)) = Multiplicative.ofAdd (1 : ZMod 2)
          from by apply congrArg Multiplicative.ofAdd; decide]
        decide
      simp only [e1, hfn_val, hfg_val]
      have hv5 : (Multiplicative.toAdd (Multiplicative.ofAdd (5 : ZMod 8))).val = 5 := by decide
      have hv1 : (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 4))).val = 1 := by decide
      have hv1' : (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 8))).val = 1 := by decide
      rw [hv5, hv1, hv1']
      simp only [pow_one]
      exact hrel.symm
    · have e1 : phi4Act (Multiplicative.ofAdd (2 : ZMod 4)) (Multiplicative.ofAdd (1 : ZMod 8))
          = Multiplicative.ofAdd (1 : ZMod 8) := by
        change c2Action_phi3 (redHom42 (Multiplicative.ofAdd (2 : ZMod 4))) _ = _
        rw [show redHom42 (Multiplicative.ofAdd (2 : ZMod 4)) = Multiplicative.ofAdd (0 : ZMod 2)
          from by apply congrArg Multiplicative.ofAdd; decide]
        decide
      simp only [e1, hfn_val, hfg_val]
      have hv1 : (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 8))).val = 1 := by decide
      have hv2 : (Multiplicative.toAdd (Multiplicative.ofAdd (2 : ZMod 4))).val = 2 := by decide
      rw [hv1, hv2, pow_one, hgb2]
      have hstep : z * ga * z⁻¹ = ga := by rw [(hzcentral ga).eq]; group
      exact hstep.symm
    · have e1 : phi4Act (Multiplicative.ofAdd (3 : ZMod 4)) (Multiplicative.ofAdd (1 : ZMod 8))
          = Multiplicative.ofAdd (5 : ZMod 8) := by
        change c2Action_phi3 (redHom42 (Multiplicative.ofAdd (3 : ZMod 4))) _ = _
        rw [show redHom42 (Multiplicative.ofAdd (3 : ZMod 4)) = Multiplicative.ofAdd (1 : ZMod 2)
          from by apply congrArg Multiplicative.ofAdd; decide]
        decide
      simp only [e1, hfn_val, hfg_val]
      have hv5 : (Multiplicative.toAdd (Multiplicative.ofAdd (5 : ZMod 8))).val = 5 := by decide
      have hv3' : (Multiplicative.toAdd (Multiplicative.ofAdd (3 : ZMod 4))).val = 3 := by decide
      have hv1' : (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 8))).val = 1 := by decide
      rw [hv5, hv3', hv1']
      simp only [pow_one]
      have hgb3 : gb ^ 3 = gb * z := by
        rw [show (3:ℕ) = 2 + 1 from rfl, pow_add, hgb2, pow_one, (hzcentral gb).eq]
      rw [hgb3]
      have hmid : z * ga * z⁻¹ = ga := by rw [(hzcentral ga).eq]; group
      have hstep : gb * z * ga * (gb * z)⁻¹ = gb * ga * gb⁻¹ := by
        calc gb * z * ga * (gb * z)⁻¹
            = gb * (z * ga * z⁻¹) * gb⁻¹ := by rw [mul_inv_rev]; group
          _ = gb * ga * gb⁻¹ := by rw [hmid]
      rw [hstep]
      exact hrel.symm
  set s : order32_c8c4_u5 →* G := SemidirectProduct.lift fn fg hcomp with hsdef
  have hs_inl : ∀ a : C8g, s (SemidirectProduct.inl a) = fn a := by
    intro a; rw [hsdef]; exact SemidirectProduct.lift_inl fn fg hcomp a
  have hs_inr : ∀ b : Multiplicative (ZMod 4), s (SemidirectProduct.inr b) = fg b := by
    intro b; rw [hsdef]; exact SemidirectProduct.lift_inr fn fg hcomp b
  have hρcompat : ∀ g : Multiplicative (ZMod 4),
      (MonoidHom.id C8g).comp (phi4Act g).toMonoidHom
        = (c2Action_phi3 (redHom42 g)).toMonoidHom.comp (MonoidHom.id C8g) := by
    intro g; rfl
  set ρ : order32_c8c4_u5 →* order16_wild_G3 :=
    SemidirectProduct.map (MonoidHom.id C8g) redHom42 hρcompat with hρdef
  have hρ_inl : ∀ a : C8g, ρ (SemidirectProduct.inl a) = SemidirectProduct.inl a := by
    intro a; rw [hρdef]; simp
  have hρ_inr : ∀ b : Multiplicative (ZMod 4),
      ρ (SemidirectProduct.inr b) = SemidirectProduct.inr (redHom42 b) := by
    intro b; rw [hρdef]; exact SemidirectProduct.map_inr _ _ _ b
  have hzker : z ∈ (QuotientGroup.mk' (Subgroup.zpowers z)).ker := by
    rw [QuotientGroup.ker_mk']; exact Subgroup.mem_zpowers z
  have hπz : (QuotientGroup.mk' (Subgroup.zpowers z)) z = 1 := MonoidHom.mem_ker.mp hzker
  have hπga : (QuotientGroup.mk' (Subgroup.zpowers z)) ga
      = e.symm (SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 8))) := hga
  have hπgb : (QuotientGroup.mk' (Subgroup.zpowers z)) gb
      = e.symm (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))) := hgb
  have hπs : ∀ q : order32_c8c4_u5,
      (QuotientGroup.mk' (Subgroup.zpowers z)) (s q) = e.symm (ρ q) := by
    have hgen : (QuotientGroup.mk' (Subgroup.zpowers z)).comp s = e.symm.toMonoidHom.comp ρ := by
      apply SemidirectProduct.hom_ext
      · apply MonoidHom.ext; intro a
        rw [zmod_pow_eq_ofAdd_one_pow a, map_pow, map_pow]
        simp only [MonoidHom.comp_apply, hs_inl, hfn_val, MulEquiv.coe_toMonoidHom, hρ_inl]
        rw [show (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 8))).val = 1 from by
          decide, pow_one, hπga]
      · apply MonoidHom.ext; intro b
        rw [zmod_pow_eq_ofAdd_one_pow b, map_pow, map_pow]
        simp only [MonoidHom.comp_apply, hs_inr, hfg_val, MulEquiv.coe_toMonoidHom, hρ_inr]
        rw [show redHom42 (Multiplicative.ofAdd (1 : ZMod 4)) = Multiplicative.ofAdd (1 : ZMod 2)
          from by apply congrArg Multiplicative.ofAdd; decide]
        rw [show (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 4))).val = 1 from by
          decide, pow_one, hπgb]
    intro q
    have := DFunLike.congr_fun hgen q
    simpa using this
  have hs_inj : Function.Injective s := by
    refine (injective_iff_map_eq_one _).mpr ?_
    intro q hq
    have hρq1 : e.symm (ρ q) = 1 := by rw [← hπs q, hq, map_one]
    have hρq : ρ q = 1 := e.symm.injective (by rw [hρq1, map_one])
    have hcomp2 : q.left = 1 ∧ redHom42 q.right = 1 := by
      rw [hρdef] at hρq
      constructor
      · have := congrArg SemidirectProduct.left hρq
        simpa using this
      · have := congrArg SemidirectProduct.right hρq
        simpa using this
    have hqleft : q.left = 1 := hcomp2.1
    have hqfg : fg q.right = 1 := by
      have hq2 : fn q.left * fg q.right = 1 := by rw [← hq, hsdef]; rfl
      rw [hqleft, map_one, one_mul] at hq2
      exact hq2
    have hc4cases : ∀ x : Multiplicative (ZMod 4),
        x = 1 ∨ x = Multiplicative.ofAdd (1 : ZMod 4) ∨ x = Multiplicative.ofAdd (2 : ZMod 4)
          ∨ x = Multiplicative.ofAdd (3 : ZMod 4) := by decide
    have hqright1 : q.right = 1 := by
      rcases hc4cases q.right with h | h | h | h
      · exact h
      · exfalso
        rw [h] at hqfg
        rw [hfg_val] at hqfg
        rw [show (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 4))).val = 1 from by
          decide, pow_one] at hqfg
        have hgb2eq1 : gb ^ 2 = 1 := by
          rw [show (2:ℕ) = 1 + 1 from rfl, pow_add, hqfg]; group
        rw [hgb2] at hgb2eq1
        exact hzne1 hgb2eq1
      · exfalso
        rw [h] at hqfg
        rw [hfg_val] at hqfg
        rw [show (Multiplicative.toAdd (Multiplicative.ofAdd (2 : ZMod 4))).val = 2 from by
          decide, hgb2] at hqfg
        exact hzne1 hqfg
      · exfalso
        rw [h] at hqfg
        rw [hfg_val] at hqfg
        rw [show (Multiplicative.toAdd (Multiplicative.ofAdd (3 : ZMod 4))).val = 3 from by
          decide] at hqfg
        have hgb3 : gb ^ 3 = gb * z := by
          rw [show (3:ℕ) = 2 + 1 from rfl, pow_add, hgb2, pow_one, (hzcentral gb).eq]
        rw [hgb3] at hqfg
        have hgbz : gb = z⁻¹ := eq_inv_of_mul_eq_one_left hqfg
        have hzinv : z⁻¹ = z := (eq_inv_of_mul_eq_one_left (by rw [← sq]; exact hz2)).symm
        rw [hzinv] at hgbz
        have hzz : gb ^ 2 = z := hgb2
        rw [hgbz] at hzz
        rw [hz2] at hzz
        exact hzne1 hzz.symm
    ext
    · exact hqleft
    · exact hqright1
  exact central_ext_full_iso hG card_order32_c8c4_u5 s hs_inj

/-! ## `z`-twisted conjugation branch: `order16_wild_G3` descendants (continued)

The "twisted conjugation" case: `a⁸ = 1`, `b² = 1` (both untouched), but the conjugation
relation picks up a `z`-defect: `bab⁻¹ = a⁵·z` (instead of exactly `a⁵`). Consistency
(`b²=1` forces conjugation-by-`b` squared to be literally the identity) reduces to
`a^(25-1) = z^(5+1) = 1`, which holds automatically since `25 ≡ 1 (mod 8)` (true for every
odd unit, not just `3`) — so this branch is always realizable, for any of `G2`/`G3`/`G4`.
Since `z ∉ ⟨a⟩` in general, `⟨a,z⟩ ≅ C₈ × C₂` is the true normal factor, and conjugation by
`b` acts on it via `(x,y) ↦ (5x, x+y)` (in additive `ZMod 8 × ZMod 2` coordinates) — this
produces a new order-32 group `(C₈ × C₂) ⋊[ψ₃] C₂`, distinct from the doubled-generator
branches (here NEITHER generator's order changes; instead the extension is genuinely
"non-split" over `order16_wild_G3` itself, in the true cocycle sense). -/

/-- The order-32 normal factor `⟨a,z⟩ ≅ C₈ × C₂` for the twisted-conjugation branch. -/
private abbrev C8C2g : Type := Multiplicative (ZMod 8) × Multiplicative (ZMod 2)

/-- The involution `(x,y) ↦ (5x, x+y)` on `C₈ × C₂` (additively), giving the twisted
conjugation action of `b` on `⟨a,z⟩` for unit `5`. -/
private noncomputable def twistAut5 : C8C2g ≃* C8C2g where
  toFun p := (Multiplicative.ofAdd (5 * Multiplicative.toAdd p.1),
      Multiplicative.ofAdd
        ((ZMod.castHom (by norm_num : (2:ℕ) ∣ 8) (ZMod 2) (Multiplicative.toAdd p.1))
          + Multiplicative.toAdd p.2))
  invFun p := (Multiplicative.ofAdd (5 * Multiplicative.toAdd p.1),
      Multiplicative.ofAdd
        ((ZMod.castHom (by norm_num : (2:ℕ) ∣ 8) (ZMod 2) (Multiplicative.toAdd p.1))
          + Multiplicative.toAdd p.2))
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

@[simp] private theorem twistAut5_sq : twistAut5 ^ 2 = 1 := by
  apply MulEquiv.ext
  intro p
  change twistAut5 (twistAut5 p) = p
  revert p; decide

private lemma c2_two_cases_tw5 (a : Multiplicative (ZMod 2)) :
    a = 1 ∨ a = Multiplicative.ofAdd 1 := by
  have := show ∀ a : Multiplicative (ZMod 2), a = 1 ∨ a = Multiplicative.ofAdd 1 from by decide
  exact this a

/-- The `C₂`-action on `C₈ × C₂` given by `twistAut5`. -/
private noncomputable def c8c2tw_phi5 : Multiplicative (ZMod 2) →* MulAut C8C2g where
  toFun g := if g = 1 then 1 else twistAut5
  map_one' := by simp
  map_mul' a b := by
    have htw2 : twistAut5 * twistAut5 = (1 : MulAut C8C2g) := by rw [← sq]; exact twistAut5_sq
    rcases c2_two_cases_tw5 a with (rfl|rfl) <;> rcases c2_two_cases_tw5 b with (rfl|rfl) <;>
      simp only [one_mul, mul_one, reduceIte,
        show (Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd (1 : ZMod 2)
          : Multiplicative (ZMod 2)) = 1 from by decide,
        show (Multiplicative.ofAdd (1 : ZMod 2) : Multiplicative (ZMod 2)) ≠ 1 from by decide,
        htw2]

/-- The new order-32 group `(C₈ × C₂) ⋊[ψ₃] C₂` (the `z`-twisted descendant of `G2`). -/
noncomputable abbrev order32_c8c2tw_u5 : Type :=
  SemidirectProduct C8C2g (Multiplicative (ZMod 2)) c8c2tw_phi5

@[simp] theorem card_order32_c8c2tw_u5 : Nat.card order32_c8c2tw_u5 = 32 := by
  rw [SemidirectProduct.card]; simp

/-- The `z`-twisted branch over `order16_wild_G3`: `a⁸=1`, `b²=1`, `bab⁻¹=a⁵·z`.
`G` is isomorphic to the new order-32 group `(C₈ × C₂) ⋊[ψ₃] C₂`. -/
theorem order32_of_c8c2u5_quotient_twisted_case {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 32) {z : G} (hzc : z ∈ Subgroup.center G) (hzp : orderOf z = 2)
    [hnorm : (Subgroup.zpowers z).Normal]
    (e : (G ⧸ Subgroup.zpowers z) ≃* order16_wild_G3)
    {ga gb : G}
    (hga : (QuotientGroup.mk' (Subgroup.zpowers z)) ga
      = e.symm (SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 8))))
    (hgb : (QuotientGroup.mk' (Subgroup.zpowers z)) gb
      = e.symm (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))))
    (hga8 : ga ^ 8 = 1) (hgb2 : gb ^ 2 = 1) (hrel : gb * ga * gb⁻¹ = ga ^ 5 * z) :
    Nonempty (G ≃* order32_c8c2tw_u5) := by
  classical
  have hz2 : z ^ 2 = 1 := by rw [← hzp]; exact pow_orderOf_eq_one z
  have hzne1 : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hzp; exact absurd hzp (by norm_num)
  have hzcomm : ∀ g : G, Commute z g := fun g => (Subgroup.mem_center_iff.mp hzc g).symm
  set fga : Multiplicative (ZMod 8) →* G := zmodZPowHom 8 ga hga8 with hfgadef
  set fz : Multiplicative (ZMod 2) →* G := zmodZPowHom 2 z hz2 with hfzdef
  set fg : Multiplicative (ZMod 2) →* G := zmodZPowHom 2 gb hgb2 with hfgdef
  have hfga_val : ∀ a : Multiplicative (ZMod 8), fga a = ga ^ (Multiplicative.toAdd a).val := by
    intro a
    have ha : a = Multiplicative.ofAdd (((Multiplicative.toAdd a).val : ZMod 8)) := by
      rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
    have hcast : ((((Multiplicative.toAdd a).val : ℕ) : ℤ) : ZMod 8)
        = ((Multiplicative.toAdd a).val : ZMod 8) := by push_cast; ring
    conv_lhs => rw [ha, ← hcast]
    rw [hfgadef, zmodZPowHom_intCast, zpow_natCast]
  have hfz_val : ∀ c : Multiplicative (ZMod 2), fz c = z ^ (Multiplicative.toAdd c).val := by
    intro c
    have hc : c = Multiplicative.ofAdd (((Multiplicative.toAdd c).val : ZMod 2)) := by
      rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
    have hcast : ((((Multiplicative.toAdd c).val : ℕ) : ℤ) : ZMod 2)
        = ((Multiplicative.toAdd c).val : ZMod 2) := by push_cast; ring
    conv_lhs => rw [hc, ← hcast]
    rw [hfzdef, zmodZPowHom_intCast, zpow_natCast]
  have hfg_val : ∀ b : Multiplicative (ZMod 2), fg b = gb ^ (Multiplicative.toAdd b).val := by
    intro b
    have hb : b = Multiplicative.ofAdd (((Multiplicative.toAdd b).val : ZMod 2)) := by
      rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
    have hcast : ((((Multiplicative.toAdd b).val : ℕ) : ℤ) : ZMod 2)
        = ((Multiplicative.toAdd b).val : ZMod 2) := by push_cast; ring
    conv_lhs => rw [hb, ← hcast]
    rw [hfgdef, zmodZPowHom_intCast, zpow_natCast]
  have hcomm' : ∀ (a : Multiplicative (ZMod 8)) (c : Multiplicative (ZMod 2)),
      Commute (fga a) (fz c) := by
    intro a c
    rw [hfga_val, hfz_val]
    exact ((hzcomm ga).pow_pow (Multiplicative.toAdd c).val (Multiplicative.toAdd a).val).symm
  set fn : C8C2g →* G := fga.noncommCoprod fz hcomm' with hfndef
  have hfn_apply : ∀ p : C8C2g, fn p = fga p.1 * fz p.2 := by
    intro p; rw [hfndef]; exact MonoidHom.noncommCoprod_apply fga fz hcomm' p
  have hc2cases : ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = Multiplicative.ofAdd (1 : ZMod 2) :=
    by decide
  have hcomp : ∀ t : Multiplicative (ZMod 2),
      fn.comp (c8c2tw_phi5 t).toMonoidHom = (MulAut.conj (fg t)).toMonoidHom.comp fn := by
    intro t
    apply monoidHom_ext_prod_ofAdd_one
    · rcases hc2cases t with rfl | rfl
      · simp
      · have e1 : c8c2tw_phi5 (Multiplicative.ofAdd (1:ZMod 2))
            (Multiplicative.ofAdd (1:ZMod 8), (1 : Multiplicative (ZMod 2)))
            = (Multiplicative.ofAdd (5:ZMod 8), Multiplicative.ofAdd (1:ZMod 2)) := by decide
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, e1,
          hfn_apply]
        have hv5 : (Multiplicative.toAdd (Multiplicative.ofAdd (5:ZMod 8))).val = 5 := by decide
        have hv1a : (Multiplicative.toAdd (Multiplicative.ofAdd (1:ZMod 8))).val = 1 := by decide
        have hv1b : (Multiplicative.toAdd (Multiplicative.ofAdd (1:ZMod 2))).val = 1 := by decide
        have hv0 : (Multiplicative.toAdd (1:Multiplicative (ZMod 2))).val = 0 := by decide
        simp only [hfga_val, hfz_val, hfg_val, hv5, hv1a, hv1b, hv0, pow_zero, pow_one,
          mul_one]
        exact hrel.symm
    · rcases hc2cases t with rfl | rfl
      · simp
      · have e1 : c8c2tw_phi5 (Multiplicative.ofAdd (1:ZMod 2))
            ((1 : Multiplicative (ZMod 8)), Multiplicative.ofAdd (1:ZMod 2))
            = ((1 : Multiplicative (ZMod 8)), Multiplicative.ofAdd (1:ZMod 2)) := by decide
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, e1,
          hfn_apply]
        have hv0 : (Multiplicative.toAdd (1:Multiplicative (ZMod 8))).val = 0 := by decide
        have hv1b : (Multiplicative.toAdd (Multiplicative.ofAdd (1:ZMod 2))).val = 1 := by decide
        simp only [hfga_val, hfz_val, hfg_val, hv0, hv1b, pow_zero, pow_one, one_mul]
        have hstep : gb * z * gb⁻¹ = z := by rw [(hzcomm gb).symm.eq]; group
        exact hstep.symm
  set s : order32_c8c2tw_u5 →* G := SemidirectProduct.lift fn fg hcomp with hsdef
  have hs_inl : ∀ a : C8C2g, s (SemidirectProduct.inl a) = fn a := by
    intro a; rw [hsdef]; exact SemidirectProduct.lift_inl fn fg hcomp a
  have hs_inr : ∀ b : Multiplicative (ZMod 2), s (SemidirectProduct.inr b) = fg b := by
    intro b; rw [hsdef]; exact SemidirectProduct.lift_inr fn fg hcomp b
  set proj1 : C8C2g →* Multiplicative (ZMod 8) := MonoidHom.fst _ _ with hproj1def
  have hρcompat : ∀ g : Multiplicative (ZMod 2),
      proj1.comp (c8c2tw_phi5 g).toMonoidHom
        = (c2Action_phi3 g).toMonoidHom.comp proj1 := by
    intro g
    apply monoidHom_ext_prod_ofAdd_one
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rcases hc2cases g with rfl | rfl <;> decide
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rcases hc2cases g with rfl | rfl <;> decide
  set ρ : order32_c8c2tw_u5 →* order16_wild_G3 :=
    SemidirectProduct.map proj1 (MonoidHom.id (Multiplicative (ZMod 2))) hρcompat with hρdef
  have hρ_inl : ∀ a : C8C2g, ρ (SemidirectProduct.inl a) = SemidirectProduct.inl (proj1 a) := by
    intro a; rw [hρdef]; exact SemidirectProduct.map_inl _ _ _ a
  have hρ_inr : ∀ b : Multiplicative (ZMod 2),
      ρ (SemidirectProduct.inr b) = SemidirectProduct.inr b := by
    intro b; rw [hρdef]; simp
  have hzker : z ∈ (QuotientGroup.mk' (Subgroup.zpowers z)).ker := by
    rw [QuotientGroup.ker_mk']; exact Subgroup.mem_zpowers z
  have hπz : (QuotientGroup.mk' (Subgroup.zpowers z)) z = 1 := MonoidHom.mem_ker.mp hzker
  have hπga : (QuotientGroup.mk' (Subgroup.zpowers z)) ga
      = e.symm (SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 8))) := hga
  have hπgb : (QuotientGroup.mk' (Subgroup.zpowers z)) gb
      = e.symm (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))) := hgb
  have hπs : ∀ q : order32_c8c2tw_u5,
      (QuotientGroup.mk' (Subgroup.zpowers z)) (s q) = e.symm (ρ q) := by
    have hgen : (QuotientGroup.mk' (Subgroup.zpowers z)).comp s = e.symm.toMonoidHom.comp ρ := by
      apply SemidirectProduct.hom_ext
      · apply monoidHom_ext_prod_ofAdd_one
        · simp only [MonoidHom.comp_apply, hs_inl, hfn_apply, MulEquiv.coe_toMonoidHom, hρ_inl]
          have hv1 : (Multiplicative.toAdd (Multiplicative.ofAdd (1:ZMod 8))).val = 1 := by decide
          have hv0 : (Multiplicative.toAdd (1:Multiplicative (ZMod 2))).val = 0 := by decide
          have hproj : proj1 (Multiplicative.ofAdd (1:ZMod 8), (1:Multiplicative (ZMod 2)))
              = Multiplicative.ofAdd (1:ZMod 8) := rfl
          simp only [hfga_val, hfz_val, hv1, hv0, pow_one, pow_zero, mul_one, hproj]
          exact hπga
        · simp only [MonoidHom.comp_apply, hs_inl, hfn_apply, MulEquiv.coe_toMonoidHom, hρ_inl]
          have hv0 : (Multiplicative.toAdd (1:Multiplicative (ZMod 8))).val = 0 := by decide
          have hv1 : (Multiplicative.toAdd (Multiplicative.ofAdd (1:ZMod 2))).val = 1 := by decide
          have hproj : proj1 ((1:Multiplicative (ZMod 8)), Multiplicative.ofAdd (1:ZMod 2))
              = (1:Multiplicative (ZMod 8)) := rfl
          simp only [hfga_val, hfz_val, hv0, hv1, pow_zero, pow_one, one_mul, hproj, map_one]
          exact hπz
      · apply MonoidHom.ext; intro b
        rw [zmod_pow_eq_ofAdd_one_pow b, map_pow, map_pow]
        simp only [MonoidHom.comp_apply, hs_inr, hfg_val, MulEquiv.coe_toMonoidHom, hρ_inr]
        rw [show (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2))).val = 1 from by
          decide, pow_one, hπgb]
    intro q
    have := DFunLike.congr_fun hgen q
    simpa using this
  have hs_inj : Function.Injective s := by
    refine (injective_iff_map_eq_one _).mpr ?_
    intro q hq
    have hρq1 : e.symm (ρ q) = 1 := by rw [← hπs q, hq, map_one]
    have hρq : ρ q = 1 := e.symm.injective (by rw [hρq1, map_one])
    have hcomp2 : proj1 q.left = 1 ∧ q.right = 1 := by
      rw [hρdef] at hρq
      constructor
      · have := congrArg SemidirectProduct.left hρq
        simpa using this
      · have := congrArg SemidirectProduct.right hρq
        simpa using this
    have hqright : q.right = 1 := hcomp2.2
    have hqfn : fn q.left = 1 := by
      have hq2 : fn q.left * fg q.right = 1 := by rw [← hq, hsdef]; rfl
      rw [hqright, map_one, mul_one] at hq2
      exact hq2
    have hqleft1 : q.left.1 = 1 := hcomp2.1
    have hqleft2 : q.left = (1, q.left.2) := by
      ext
      · exact hqleft1
      · rfl
    rw [hqleft2, hfn_apply] at hqfn
    simp only [hfga_val, hfz_val] at hqfn
    have hv0 : (Multiplicative.toAdd (1 : Multiplicative (ZMod 8))).val = 0 := by decide
    rw [hv0, pow_zero, one_mul] at hqfn
    have hc2cases2 : ∀ y : Multiplicative (ZMod 2), z ^ (Multiplicative.toAdd y).val = 1 →
        y = 1 := by
      intro y hy
      rcases hc2cases y with rfl | rfl
      · rfl
      · exfalso
        rw [show (Multiplicative.toAdd (Multiplicative.ofAdd (1:ZMod 2))).val = 1 from by
          decide, pow_one] at hy
        exact hzne1 hy
    have hqleft2' : q.left.2 = 1 := hc2cases2 q.left.2 hqfn
    have hqleft : q.left = 1 := by
      rw [hqleft2, hqleft2']; rfl
    exact SemidirectProduct.ext hqleft hqright
  exact central_ext_full_iso hG card_order32_c8c2tw_u5 s hs_inj

end Smallgroups.UsefulTheorems
