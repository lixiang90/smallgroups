/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order16_Wild
import Smallgroups.UsefulTheorems.PGroupGeneration
import Smallgroups.UsefulTheorems.Order32.GenericTools

/-! ## Descendants of `order16_wild_G4` (`C₈ ⋊ C₂` via unit `7`, dihedral `D₁₆`)

`order16_wild_G4 = C₈ ⋊[φ₄] C₂` where `φ₄` sends the generator `b` of `C₂` to the
automorphism `x ↦ x⁻¹` of `C₈` (`bab⁻¹ = a⁻¹`, i.e. `a⁷`). Same shape as `G2`/`G3`; only
the trivial-cocycle branch is recorded. -/

namespace Smallgroups.UsefulTheorems

/-- The trivial-cocycle branch over `order16_wild_G4`: both relator bits `a⁸, b²` vanish
and the conjugation defect vanishes, so `G` splits as `order16_wild_G4 × C₂`. -/
theorem order32_of_c8c2d16_quotient_trivial_case {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 32) {z : G} (hzc : z ∈ Subgroup.center G) (hzp : orderOf z = 2)
    [hnorm : (Subgroup.zpowers z).Normal]
    (e : (G ⧸ Subgroup.zpowers z) ≃* order16_wild_G4)
    {ga gb : G}
    (hga : (QuotientGroup.mk' (Subgroup.zpowers z)) ga
      = e.symm (SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 8))))
    (hgb : (QuotientGroup.mk' (Subgroup.zpowers z)) gb
      = e.symm (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))))
    (hga8 : ga ^ 8 = 1) (hgb2 : gb ^ 2 = 1) (hrel : gb * ga * gb⁻¹ = ga ^ 7) :
    Nonempty (G ≃* order16_wild_G4 × Multiplicative (ZMod 2)) := by
  classical
  set φ := c2Action_phi4 with hφdef
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
          = Multiplicative.ofAdd (7 : ZMod 8) := by rw [hφdef]; decide
      simp only [e1, hfn_val, hfg_val]
      have hv7 : (Multiplicative.toAdd (Multiplicative.ofAdd (7 : ZMod 8))).val = 7 := by decide
      have hv1 : (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2))).val = 1 := by decide
      have hv1' : (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 8))).val = 1 := by decide
      rw [hv7, hv1, hv1']
      simp only [pow_one]
      exact hrel.symm
  set s : order16_wild_G4 →* G := SemidirectProduct.lift fn fg hcomp with hsdef
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
  have hπs : ∀ q : order16_wild_G4,
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
  have hzrange : ∀ q : order16_wild_G4, s q = z → q = 1 := by
    intro q hqz
    have h1 := hπs q
    rw [hqz, hπz] at h1
    have h2 : q = e 1 := by
      have := congrArg e h1.symm
      simpa using this
    rw [h2, map_one]
  exact central_ext_split_iso_prod hG (card_order16_wild_G4) hzc hzp s hs_inj hzrange

/-! ## Twisted / doubled branches: `order16_wild_G4` descendants (continued)

Beyond the split branch, `G2 = C₈ ⋊[φ₂] C₂` has 7 more cocycle-bit combinations. Here we
handle the "`b` doubles" case: `a⁸ = 1` (untouched), `b² = z` (so `b` lifts to order `4`),
and the conjugation relation holds exactly (`bab⁻¹ = a³`, not `a³z`). This produces a
genuinely new order-32 group `C₈ ⋊[φ₄] C₄`, where `φ₄` is the order-`2` automorphism
`x ↦ x³` of `C₈`, now acted on by `C₄` through its quotient `C₄ ↠ C₂`. -/

/-- Reduction homomorphism `C₄ ↠ C₂` (mod-2 cast on `ZMod 4`), used to factor the `C₄`-action
through the existing `C₂`-action `c2Action_phi4`. -/
private noncomputable def redHom42 : Multiplicative (ZMod 4) →* Multiplicative (ZMod 2) :=
  AddMonoidHom.toMultiplicative (ZMod.castHom (by norm_num) (ZMod 2)).toAddMonoidHom

/-- The `C₄`-action on `C₈` obtained by factoring `φ₂` (unit `3`) through `C₄ ↠ C₂`. -/
private noncomputable def phi4Act : Multiplicative (ZMod 4) →* MulAut C8g :=
  c2Action_phi4.comp redHom42

/-- The new order-32 group `C₈ ⋊[φ₄] C₄` (the `b`-doubled descendant of `G4`). -/
noncomputable abbrev order32_c8c4_u7 : Type :=
  SemidirectProduct C8g (Multiplicative (ZMod 4)) phi4Act

@[simp] theorem card_order32_c8c4_u7 : Nat.card order32_c8c4_u7 = 32 := by
  rw [SemidirectProduct.card]; simp

/-- The `b`-doubled branch over `order16_wild_G4`: `a⁸=1`, `b²=z`, `bab⁻¹=a^7` (exact).
`G` is isomorphic to the new order-32 group `C₈ ⋊[φ₄] C₄`. -/
theorem order32_of_c8c2d16_quotient_doubled_b_case {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 32) {z : G} (hzc : z ∈ Subgroup.center G) (hzp : orderOf z = 2)
    [hnorm : (Subgroup.zpowers z).Normal]
    (e : (G ⧸ Subgroup.zpowers z) ≃* order16_wild_G4)
    {ga gb : G}
    (hga : (QuotientGroup.mk' (Subgroup.zpowers z)) ga
      = e.symm (SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 8))))
    (hgb : (QuotientGroup.mk' (Subgroup.zpowers z)) gb
      = e.symm (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))))
    (hga8 : ga ^ 8 = 1) (hgb2 : gb ^ 2 = z) (hrel : gb * ga * gb⁻¹ = ga ^ 7) :
    Nonempty (G ≃* order32_c8c4_u7) := by
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
        change c2Action_phi4 (redHom42 1) _ = _
        rw [show redHom42 (1 : Multiplicative (ZMod 4)) = 1 from by
          apply congrArg Multiplicative.ofAdd; decide]
        decide
      simp only [e1, hfn_val, hfg_val]
      have hv0 : (Multiplicative.toAdd (1 : Multiplicative (ZMod 4))).val = 0 := by decide
      rw [hv0, pow_zero, one_mul, inv_one, mul_one]
    · have e1 : phi4Act (Multiplicative.ofAdd (1 : ZMod 4)) (Multiplicative.ofAdd (1 : ZMod 8))
          = Multiplicative.ofAdd (7 : ZMod 8) := by
        change c2Action_phi4 (redHom42 (Multiplicative.ofAdd (1 : ZMod 4))) _ = _
        rw [show redHom42 (Multiplicative.ofAdd (1 : ZMod 4)) = Multiplicative.ofAdd (1 : ZMod 2)
          from by apply congrArg Multiplicative.ofAdd; decide]
        decide
      simp only [e1, hfn_val, hfg_val]
      have hv7 : (Multiplicative.toAdd (Multiplicative.ofAdd (7 : ZMod 8))).val = 7 := by decide
      have hv1 : (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 4))).val = 1 := by decide
      have hv1' : (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 8))).val = 1 := by decide
      rw [hv7, hv1, hv1']
      simp only [pow_one]
      exact hrel.symm
    · have e1 : phi4Act (Multiplicative.ofAdd (2 : ZMod 4)) (Multiplicative.ofAdd (1 : ZMod 8))
          = Multiplicative.ofAdd (1 : ZMod 8) := by
        change c2Action_phi4 (redHom42 (Multiplicative.ofAdd (2 : ZMod 4))) _ = _
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
          = Multiplicative.ofAdd (7 : ZMod 8) := by
        change c2Action_phi4 (redHom42 (Multiplicative.ofAdd (3 : ZMod 4))) _ = _
        rw [show redHom42 (Multiplicative.ofAdd (3 : ZMod 4)) = Multiplicative.ofAdd (1 : ZMod 2)
          from by apply congrArg Multiplicative.ofAdd; decide]
        decide
      simp only [e1, hfn_val, hfg_val]
      have hv7 : (Multiplicative.toAdd (Multiplicative.ofAdd (7 : ZMod 8))).val = 7 := by decide
      have hv3' : (Multiplicative.toAdd (Multiplicative.ofAdd (3 : ZMod 4))).val = 3 := by decide
      have hv1' : (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 8))).val = 1 := by decide
      rw [hv7, hv3', hv1']
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
  set s : order32_c8c4_u7 →* G := SemidirectProduct.lift fn fg hcomp with hsdef
  have hs_inl : ∀ a : C8g, s (SemidirectProduct.inl a) = fn a := by
    intro a; rw [hsdef]; exact SemidirectProduct.lift_inl fn fg hcomp a
  have hs_inr : ∀ b : Multiplicative (ZMod 4), s (SemidirectProduct.inr b) = fg b := by
    intro b; rw [hsdef]; exact SemidirectProduct.lift_inr fn fg hcomp b
  have hρcompat : ∀ g : Multiplicative (ZMod 4),
      (MonoidHom.id C8g).comp (phi4Act g).toMonoidHom
        = (c2Action_phi4 (redHom42 g)).toMonoidHom.comp (MonoidHom.id C8g) := by
    intro g; rfl
  set ρ : order32_c8c4_u7 →* order16_wild_G4 :=
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
  have hπs : ∀ q : order32_c8c4_u7,
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
  exact central_ext_full_iso hG card_order32_c8c4_u7 s hs_inj

/-! ## Further twisted / doubled branches: `order16_wild_G4` (continued)

The "`a` doubles" case: `a⁸ = z` (so `a` lifts to order `16`), `b² = 1` (untouched), and
the conjugation relation holds exactly (`bab⁻¹ = a⁷`). Since conjugation-by-`b` squared
must equal the identity automorphism exactly (`b² = 1`, not absorbed by centrality),
consistency requires the unit `7` to satisfy `7² ≡ 1 (mod 16)` — which it does
(`49 = 48 + 1`), unlike units `3` and `5` (so this branch is realizable for `G4` but NOT
for `G2`/`G3`). This produces a new order-32 group `C₁₆ ⋊[φ₇] C₂`. -/

/-- The unit `7` in `(ZMod 16)ˣ`. -/
def zmod16_unit_7 : (ZMod 16)ˣ :=
  ZMod.unitOfCoprime 7 (by norm_num)

@[simp] theorem zmod16_unit_7_sq : zmod16_unit_7 ^ 2 = 1 := by
  unfold zmod16_unit_7; decide

/-- The `C₂`-action on `C₁₆` by the order-`2` unit `7`. -/
noncomputable def c16c2_phi7 : Multiplicative (ZMod 2) →* MulAut (Multiplicative (ZMod 16)) :=
  c2ActionAut 16 zmod16_unit_7 zmod16_unit_7_sq

/-- The new order-32 group `C₁₆ ⋊[φ₇] C₂` (the `a`-doubled descendant of `G4`). -/
noncomputable abbrev order32_c16c2_u7 : Type :=
  SemidirectProduct (Multiplicative (ZMod 16)) (Multiplicative (ZMod 2)) c16c2_phi7

@[simp] theorem card_order32_c16c2_u7 : Nat.card order32_c16c2_u7 = 32 := by
  rw [SemidirectProduct.card]; simp

/-- Reduction homomorphism `C₁₆ ↠ C₈` (mod-8 cast on `ZMod 16`), used to collapse the
doubled normal factor back down to `order16_wild_G4`'s own `C₈`. -/
private noncomputable def redHom16to8 : Multiplicative (ZMod 16) →* Multiplicative (ZMod 8) :=
  AddMonoidHom.toMultiplicative (ZMod.castHom (by norm_num) (ZMod 8)).toAddMonoidHom

/-- The `a`-doubled branch over `order16_wild_G4`: `a⁸=z`, `b²=1`, `bab⁻¹=a⁷` (exact).
`G` is isomorphic to the new order-32 group `C₁₆ ⋊[φ₇] C₂`. -/
theorem order32_of_c8c2d16_quotient_doubled_a_case {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 32) {z : G} (_hzc : z ∈ Subgroup.center G) (hzp : orderOf z = 2)
    [hnorm : (Subgroup.zpowers z).Normal]
    (e : (G ⧸ Subgroup.zpowers z) ≃* order16_wild_G4)
    {ga gb : G}
    (hga : (QuotientGroup.mk' (Subgroup.zpowers z)) ga
      = e.symm (SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 8))))
    (hgb : (QuotientGroup.mk' (Subgroup.zpowers z)) gb
      = e.symm (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))))
    (hga8 : ga ^ 8 = z) (hgb2 : gb ^ 2 = 1) (hrel : gb * ga * gb⁻¹ = ga ^ 7) :
    Nonempty (G ≃* order32_c16c2_u7) := by
  classical
  have hz2 : z ^ 2 = 1 := by rw [← hzp]; exact pow_orderOf_eq_one z
  have hzne1 : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hzp; exact absurd hzp (by norm_num)
  have hga16 : ga ^ 16 = 1 := by
    have hh : ga ^ 16 = (ga ^ 8) ^ 2 := by rw [← pow_mul]
    rw [hh, hga8, hz2]
  set fn : Multiplicative (ZMod 16) →* G := zmodZPowHom 16 ga hga16 with hfndef
  set fg : Multiplicative (ZMod 2) →* G := zmodZPowHom 2 gb hgb2 with hfgdef
  have hfn_val : ∀ a : Multiplicative (ZMod 16), fn a = ga ^ (Multiplicative.toAdd a).val := by
    intro a
    have ha : a = Multiplicative.ofAdd (((Multiplicative.toAdd a).val : ZMod 16)) := by
      rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
    have hcast : ((((Multiplicative.toAdd a).val : ℕ) : ℤ) : ZMod 16)
        = ((Multiplicative.toAdd a).val : ZMod 16) := by push_cast; ring
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
  have hc2cases : ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = Multiplicative.ofAdd (1 : ZMod 2) :=
    by decide
  have hcomp : ∀ t : Multiplicative (ZMod 2),
      fn.comp (c16c2_phi7 t).toMonoidHom = (MulAut.conj (fg t)).toMonoidHom.comp fn := by
    intro t
    apply monoidHom_ext_ofAdd_one
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rcases hc2cases t with rfl | rfl
    · have e1 : c16c2_phi7 (1 : Multiplicative (ZMod 2)) (Multiplicative.ofAdd (1 : ZMod 16))
          = Multiplicative.ofAdd (1 : ZMod 16) := by decide
      simp only [e1, hfn_val, hfg_val]
      have hv0 : (Multiplicative.toAdd (1 : Multiplicative (ZMod 2))).val = 0 := by decide
      rw [hv0, pow_zero, one_mul, inv_one, mul_one]
    · have e1 : c16c2_phi7 (Multiplicative.ofAdd (1 : ZMod 2)) (Multiplicative.ofAdd (1 : ZMod 16))
          = Multiplicative.ofAdd (7 : ZMod 16) := by decide
      simp only [e1, hfn_val, hfg_val]
      have hv7 : (Multiplicative.toAdd (Multiplicative.ofAdd (7 : ZMod 16))).val = 7 := by decide
      have hv1 : (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2))).val = 1 := by decide
      have hv1' : (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 16))).val = 1 := by decide
      rw [hv7, hv1, hv1']
      simp only [pow_one]
      exact hrel.symm
  set s : order32_c16c2_u7 →* G := SemidirectProduct.lift fn fg hcomp with hsdef
  have hs_inl : ∀ a : Multiplicative (ZMod 16), s (SemidirectProduct.inl a) = fn a := by
    intro a; rw [hsdef]; exact SemidirectProduct.lift_inl fn fg hcomp a
  have hs_inr : ∀ b : Multiplicative (ZMod 2), s (SemidirectProduct.inr b) = fg b := by
    intro b; rw [hsdef]; exact SemidirectProduct.lift_inr fn fg hcomp b
  have hρcompat : ∀ g : Multiplicative (ZMod 2),
      redHom16to8.comp (c16c2_phi7 g).toMonoidHom
        = (c2Action_phi4 g).toMonoidHom.comp redHom16to8 := by
    intro g
    apply monoidHom_ext_ofAdd_one
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rcases hc2cases g with rfl | rfl
    · decide
    · have e1 : c16c2_phi7 (Multiplicative.ofAdd (1 : ZMod 2)) (Multiplicative.ofAdd (1 : ZMod 16))
          = Multiplicative.ofAdd (7 : ZMod 16) := by decide
      rw [e1]
      have e2 : redHom16to8 (Multiplicative.ofAdd (7 : ZMod 16))
          = Multiplicative.ofAdd (7 : ZMod 8) := by
        apply congrArg Multiplicative.ofAdd; decide
      have e3 : redHom16to8 (Multiplicative.ofAdd (1 : ZMod 16))
          = Multiplicative.ofAdd (1 : ZMod 8) := by
        apply congrArg Multiplicative.ofAdd; decide
      rw [e2, e3]
      have e4 : c2Action_phi4 (Multiplicative.ofAdd (1 : ZMod 2))
            (Multiplicative.ofAdd (1 : ZMod 8))
          = Multiplicative.ofAdd (7 : ZMod 8) := by decide
      exact e4.symm
  set ρ : order32_c16c2_u7 →* order16_wild_G4 :=
    SemidirectProduct.map redHom16to8 (MonoidHom.id (Multiplicative (ZMod 2))) hρcompat with hρdef
  have hρ_inl : ∀ a : Multiplicative (ZMod 16),
      ρ (SemidirectProduct.inl a) = SemidirectProduct.inl (redHom16to8 a) := by
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
  have hπs : ∀ q : order32_c16c2_u7,
      (QuotientGroup.mk' (Subgroup.zpowers z)) (s q) = e.symm (ρ q) := by
    have hgen : (QuotientGroup.mk' (Subgroup.zpowers z)).comp s = e.symm.toMonoidHom.comp ρ := by
      apply SemidirectProduct.hom_ext
      · apply MonoidHom.ext; intro a
        rw [zmod_pow_eq_ofAdd_one_pow a, map_pow, map_pow]
        simp only [MonoidHom.comp_apply, hs_inl, hfn_val, MulEquiv.coe_toMonoidHom, hρ_inl]
        rw [show redHom16to8 (Multiplicative.ofAdd (1 : ZMod 16))
            = Multiplicative.ofAdd (1 : ZMod 8)
          from by apply congrArg Multiplicative.ofAdd; decide]
        rw [show (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 16))).val = 1 from by
          decide, pow_one, hπga]
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
    have hcomp2 : redHom16to8 q.left = 1 ∧ q.right = 1 := by
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
    have hc16cases : ∀ x : Multiplicative (ZMod 16), redHom16to8 x = 1 →
        x = 1 ∨ x = Multiplicative.ofAdd (8 : ZMod 16) := by decide
    have hqleft : q.left = 1 := by
      rcases hc16cases q.left hcomp2.1 with h | h
      · exact h
      · exfalso
        rw [h] at hqfn
        rw [hfn_val] at hqfn
        rw [show (Multiplicative.toAdd (Multiplicative.ofAdd (8 : ZMod 16))).val = 8 from by
          decide] at hqfn
        rw [hga8] at hqfn
        exact hzne1 hqfn
    ext
    · exact hqleft
    · exact hqright
  exact central_ext_full_iso hG card_order32_c16c2_u7 s hs_inj

/-! ## `z`-twisted conjugation branch: `order16_wild_G4` descendants (continued)

The "twisted conjugation" case: `a⁸ = 1`, `b² = 1` (both untouched), but the conjugation
relation picks up a `z`-defect: `bab⁻¹ = a³·z` (instead of exactly `a⁷`). Consistency
(`b²=1` forces conjugation-by-`b` squared to be literally the identity) reduces to
`a^(49-1) = z^(7+1) = 1`, which holds automatically since `49 ≡ 1 (mod 8)` (true for every
odd unit, not just `3`) — so this branch is always realizable, for any of `G2`/`G3`/`G4`.
Since `z ∉ ⟨a⟩` in general, `⟨a,z⟩ ≅ C₈ × C₂` is the true normal factor, and conjugation by
`b` acts on it via `(x,y) ↦ (7x, x+y)` (in additive `ZMod 8 × ZMod 2` coordinates) — this
produces a new order-32 group `(C₈ × C₂) ⋊[ψ₇] C₂`, distinct from the doubled-generator
branches (here NEITHER generator's order changes; instead the extension is genuinely
"non-split" over `order16_wild_G4` itself, in the true cocycle sense). -/

/-- The order-32 normal factor `⟨a,z⟩ ≅ C₈ × C₂` for the twisted-conjugation branch. -/
private abbrev C8C2g : Type := Multiplicative (ZMod 8) × Multiplicative (ZMod 2)

/-- The involution `(x,y) ↦ (7x, x+y)` on `C₈ × C₂` (additively), giving the twisted
conjugation action of `b` on `⟨a,z⟩` for unit `7`. -/
private noncomputable def twistAut7 : C8C2g ≃* C8C2g where
  toFun p := (Multiplicative.ofAdd (7 * Multiplicative.toAdd p.1),
      Multiplicative.ofAdd
        ((ZMod.castHom (by norm_num : (2:ℕ) ∣ 8) (ZMod 2) (Multiplicative.toAdd p.1))
          + Multiplicative.toAdd p.2))
  invFun p := (Multiplicative.ofAdd (7 * Multiplicative.toAdd p.1),
      Multiplicative.ofAdd
        ((ZMod.castHom (by norm_num : (2:ℕ) ∣ 8) (ZMod 2) (Multiplicative.toAdd p.1))
          + Multiplicative.toAdd p.2))
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

@[simp] private theorem twistAut7_sq : twistAut7 ^ 2 = 1 := by
  apply MulEquiv.ext
  intro p
  change twistAut7 (twistAut7 p) = p
  revert p; decide

private lemma c2_two_cases_tw7 (a : Multiplicative (ZMod 2)) :
    a = 1 ∨ a = Multiplicative.ofAdd 1 := by
  have := show ∀ a : Multiplicative (ZMod 2), a = 1 ∨ a = Multiplicative.ofAdd 1 from by decide
  exact this a

/-- The `C₂`-action on `C₈ × C₂` given by `twistAut7`. Not `private`: `Distinctness.lean`
needs to name it to show `order32_c8c2tw_u3 ≃* order32_c8c2tw_u7`. -/
noncomputable def c8c2tw_phi7 : Multiplicative (ZMod 2) →* MulAut C8C2g where
  toFun g := if g = 1 then 1 else twistAut7
  map_one' := by simp
  map_mul' a b := by
    have htw2 : twistAut7 * twistAut7 = (1 : MulAut C8C2g) := by rw [← sq]; exact twistAut7_sq
    rcases c2_two_cases_tw7 a with (rfl|rfl) <;> rcases c2_two_cases_tw7 b with (rfl|rfl) <;>
      simp only [one_mul, mul_one, reduceIte,
        show (Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd (1 : ZMod 2)
          : Multiplicative (ZMod 2)) = 1 from by decide,
        show (Multiplicative.ofAdd (1 : ZMod 2) : Multiplicative (ZMod 2)) ≠ 1 from by decide,
        htw2]

/-- The new order-32 group `(C₈ × C₂) ⋊[ψ₇] C₂` (the `z`-twisted descendant of `G2`). -/
noncomputable abbrev order32_c8c2tw_u7 : Type :=
  SemidirectProduct C8C2g (Multiplicative (ZMod 2)) c8c2tw_phi7

@[simp] theorem card_order32_c8c2tw_u7 : Nat.card order32_c8c2tw_u7 = 32 := by
  rw [SemidirectProduct.card]; simp

/-- The `z`-twisted branch over `order16_wild_G4`: `a⁸=1`, `b²=1`, `bab⁻¹=a⁷·z`.
`G` is isomorphic to the new order-32 group `(C₈ × C₂) ⋊[ψ₇] C₂`. -/
theorem order32_of_c8c2d16_quotient_twisted_case {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 32) {z : G} (hzc : z ∈ Subgroup.center G) (hzp : orderOf z = 2)
    [hnorm : (Subgroup.zpowers z).Normal]
    (e : (G ⧸ Subgroup.zpowers z) ≃* order16_wild_G4)
    {ga gb : G}
    (hga : (QuotientGroup.mk' (Subgroup.zpowers z)) ga
      = e.symm (SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 8))))
    (hgb : (QuotientGroup.mk' (Subgroup.zpowers z)) gb
      = e.symm (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))))
    (hga8 : ga ^ 8 = 1) (hgb2 : gb ^ 2 = 1) (hrel : gb * ga * gb⁻¹ = ga ^ 7 * z) :
    Nonempty (G ≃* order32_c8c2tw_u7) := by
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
      fn.comp (c8c2tw_phi7 t).toMonoidHom = (MulAut.conj (fg t)).toMonoidHom.comp fn := by
    intro t
    apply monoidHom_ext_prod_ofAdd_one
    · rcases hc2cases t with rfl | rfl
      · simp
      · have e1 : c8c2tw_phi7 (Multiplicative.ofAdd (1:ZMod 2))
            (Multiplicative.ofAdd (1:ZMod 8), (1 : Multiplicative (ZMod 2)))
            = (Multiplicative.ofAdd (7:ZMod 8), Multiplicative.ofAdd (1:ZMod 2)) := by decide
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, e1,
          hfn_apply]
        have hv7 : (Multiplicative.toAdd (Multiplicative.ofAdd (7:ZMod 8))).val = 7 := by decide
        have hv1a : (Multiplicative.toAdd (Multiplicative.ofAdd (1:ZMod 8))).val = 1 := by decide
        have hv1b : (Multiplicative.toAdd (Multiplicative.ofAdd (1:ZMod 2))).val = 1 := by decide
        have hv0 : (Multiplicative.toAdd (1:Multiplicative (ZMod 2))).val = 0 := by decide
        simp only [hfga_val, hfz_val, hfg_val, hv7, hv1a, hv1b, hv0, pow_zero, pow_one,
          mul_one]
        exact hrel.symm
    · rcases hc2cases t with rfl | rfl
      · simp
      · have e1 : c8c2tw_phi7 (Multiplicative.ofAdd (1:ZMod 2))
            ((1 : Multiplicative (ZMod 8)), Multiplicative.ofAdd (1:ZMod 2))
            = ((1 : Multiplicative (ZMod 8)), Multiplicative.ofAdd (1:ZMod 2)) := by decide
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, e1,
          hfn_apply]
        have hv0 : (Multiplicative.toAdd (1:Multiplicative (ZMod 8))).val = 0 := by decide
        have hv1b : (Multiplicative.toAdd (Multiplicative.ofAdd (1:ZMod 2))).val = 1 := by decide
        simp only [hfga_val, hfz_val, hfg_val, hv0, hv1b, pow_zero, pow_one, one_mul]
        have hstep : gb * z * gb⁻¹ = z := by rw [(hzcomm gb).symm.eq]; group
        exact hstep.symm
  set s : order32_c8c2tw_u7 →* G := SemidirectProduct.lift fn fg hcomp with hsdef
  have hs_inl : ∀ a : C8C2g, s (SemidirectProduct.inl a) = fn a := by
    intro a; rw [hsdef]; exact SemidirectProduct.lift_inl fn fg hcomp a
  have hs_inr : ∀ b : Multiplicative (ZMod 2), s (SemidirectProduct.inr b) = fg b := by
    intro b; rw [hsdef]; exact SemidirectProduct.lift_inr fn fg hcomp b
  set proj1 : C8C2g →* Multiplicative (ZMod 8) := MonoidHom.fst _ _ with hproj1def
  have hρcompat : ∀ g : Multiplicative (ZMod 2),
      proj1.comp (c8c2tw_phi7 g).toMonoidHom
        = (c2Action_phi4 g).toMonoidHom.comp proj1 := by
    intro g
    apply monoidHom_ext_prod_ofAdd_one
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rcases hc2cases g with rfl | rfl <;> decide
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rcases hc2cases g with rfl | rfl <;> decide
  set ρ : order32_c8c2tw_u7 →* order16_wild_G4 :=
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
  have hπs : ∀ q : order32_c8c2tw_u7,
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
  exact central_ext_full_iso hG card_order32_c8c2tw_u7 s hs_inj

/-- The unit `7` in `(ZMod 16)ˣ`. -/
def zmod16_unit_15 : (ZMod 16)ˣ :=
  ZMod.unitOfCoprime 15 (by norm_num)

@[simp] theorem zmod16_unit_15_sq : zmod16_unit_15 ^ 2 = 1 := by
  unfold zmod16_unit_15; decide

/-- The `C₂`-action on `C₁₆` by the order-`2` unit `7`. -/
noncomputable def c16c2_phi15 : Multiplicative (ZMod 2) →* MulAut (Multiplicative (ZMod 16)) :=
  c2ActionAut 16 zmod16_unit_15 zmod16_unit_15_sq

/-- The new order-32 group `C₁₆ ⋊[φ₇] C₂` (the `a`-doubled descendant of `G4`). -/
noncomputable abbrev order32_c16c2_u15 : Type :=
  SemidirectProduct (Multiplicative (ZMod 16)) (Multiplicative (ZMod 2)) c16c2_phi15

@[simp] theorem card_order32_c16c2_u15 : Nat.card order32_c16c2_u15 = 32 := by
  rw [SemidirectProduct.card]; simp


/-- The `a`-doubled branch over `order16_wild_G4`: `a⁸=z`, `b²=1`, `bab⁻¹=a¹⁵` (exact).
`G` is isomorphic to the new order-32 group `C₁₆ ⋊[φ₁₅] C₂` (the dihedral
group `D₃₂`, since `15 ≡ -1 (mod 16)`). -/
theorem order32_of_c8c2d16_quotient_doubled_a2_case {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 32) {z : G} (_hzc : z ∈ Subgroup.center G) (hzp : orderOf z = 2)
    [hnorm : (Subgroup.zpowers z).Normal]
    (e : (G ⧸ Subgroup.zpowers z) ≃* order16_wild_G4)
    {ga gb : G}
    (hga : (QuotientGroup.mk' (Subgroup.zpowers z)) ga
      = e.symm (SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 8))))
    (hgb : (QuotientGroup.mk' (Subgroup.zpowers z)) gb
      = e.symm (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))))
    (hga8 : ga ^ 8 = z) (hgb2 : gb ^ 2 = 1) (hrel : gb * ga * gb⁻¹ = ga ^ 15) :
    Nonempty (G ≃* order32_c16c2_u15) := by
  classical
  have hz2 : z ^ 2 = 1 := by rw [← hzp]; exact pow_orderOf_eq_one z
  have hzne1 : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hzp; exact absurd hzp (by norm_num)
  have hga16 : ga ^ 16 = 1 := by
    have hh : ga ^ 16 = (ga ^ 8) ^ 2 := by rw [← pow_mul]
    rw [hh, hga8, hz2]
  set fn : Multiplicative (ZMod 16) →* G := zmodZPowHom 16 ga hga16 with hfndef
  set fg : Multiplicative (ZMod 2) →* G := zmodZPowHom 2 gb hgb2 with hfgdef
  have hfn_val : ∀ a : Multiplicative (ZMod 16), fn a = ga ^ (Multiplicative.toAdd a).val := by
    intro a
    have ha : a = Multiplicative.ofAdd (((Multiplicative.toAdd a).val : ZMod 16)) := by
      rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
    have hcast : ((((Multiplicative.toAdd a).val : ℕ) : ℤ) : ZMod 16)
        = ((Multiplicative.toAdd a).val : ZMod 16) := by push_cast; ring
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
  have hc2cases : ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = Multiplicative.ofAdd (1 : ZMod 2) :=
    by decide
  have hcomp : ∀ t : Multiplicative (ZMod 2),
      fn.comp (c16c2_phi15 t).toMonoidHom = (MulAut.conj (fg t)).toMonoidHom.comp fn := by
    intro t
    apply monoidHom_ext_ofAdd_one
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rcases hc2cases t with rfl | rfl
    · have e1 : c16c2_phi15 (1 : Multiplicative (ZMod 2)) (Multiplicative.ofAdd (1 : ZMod 16))
          = Multiplicative.ofAdd (1 : ZMod 16) := by decide
      simp only [e1, hfn_val, hfg_val]
      have hv0 : (Multiplicative.toAdd (1 : Multiplicative (ZMod 2))).val = 0 := by decide
      rw [hv0, pow_zero, one_mul, inv_one, mul_one]
    · have e1 : c16c2_phi15 (Multiplicative.ofAdd (1 : ZMod 2)) (Multiplicative.ofAdd (1 : ZMod 16))
          = Multiplicative.ofAdd (15 : ZMod 16) := by decide
      simp only [e1, hfn_val, hfg_val]
      have hv15 : (Multiplicative.toAdd (Multiplicative.ofAdd (15 : ZMod 16))).val = 15 := by decide
      have hv1 : (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2))).val = 1 := by decide
      have hv1' : (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 16))).val = 1 := by decide
      rw [hv15, hv1, hv1']
      simp only [pow_one]
      exact hrel.symm
  set s : order32_c16c2_u15 →* G := SemidirectProduct.lift fn fg hcomp with hsdef
  have hs_inl : ∀ a : Multiplicative (ZMod 16), s (SemidirectProduct.inl a) = fn a := by
    intro a; rw [hsdef]; exact SemidirectProduct.lift_inl fn fg hcomp a
  have hs_inr : ∀ b : Multiplicative (ZMod 2), s (SemidirectProduct.inr b) = fg b := by
    intro b; rw [hsdef]; exact SemidirectProduct.lift_inr fn fg hcomp b
  have hρcompat : ∀ g : Multiplicative (ZMod 2),
      redHom16to8.comp (c16c2_phi15 g).toMonoidHom
        = (c2Action_phi4 g).toMonoidHom.comp redHom16to8 := by
    intro g
    apply monoidHom_ext_ofAdd_one
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rcases hc2cases g with rfl | rfl
    · decide
    · have e1 : c16c2_phi15 (Multiplicative.ofAdd (1 : ZMod 2)) (Multiplicative.ofAdd (1 : ZMod 16))
          = Multiplicative.ofAdd (15 : ZMod 16) := by decide
      rw [e1]
      have e2 : redHom16to8 (Multiplicative.ofAdd (15 : ZMod 16))
          = Multiplicative.ofAdd (7 : ZMod 8) := by
        apply congrArg Multiplicative.ofAdd; decide
      have e3 : redHom16to8 (Multiplicative.ofAdd (1 : ZMod 16))
          = Multiplicative.ofAdd (1 : ZMod 8) := by
        apply congrArg Multiplicative.ofAdd; decide
      rw [e2, e3]
      have e4 : c2Action_phi4 (Multiplicative.ofAdd (1 : ZMod 2))
            (Multiplicative.ofAdd (1 : ZMod 8))
          = Multiplicative.ofAdd (7 : ZMod 8) := by decide
      exact e4.symm
  set ρ : order32_c16c2_u15 →* order16_wild_G4 :=
    SemidirectProduct.map redHom16to8 (MonoidHom.id (Multiplicative (ZMod 2))) hρcompat with hρdef
  have hρ_inl : ∀ a : Multiplicative (ZMod 16),
      ρ (SemidirectProduct.inl a) = SemidirectProduct.inl (redHom16to8 a) := by
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
  have hπs : ∀ q : order32_c16c2_u15,
      (QuotientGroup.mk' (Subgroup.zpowers z)) (s q) = e.symm (ρ q) := by
    have hgen : (QuotientGroup.mk' (Subgroup.zpowers z)).comp s = e.symm.toMonoidHom.comp ρ := by
      apply SemidirectProduct.hom_ext
      · apply MonoidHom.ext; intro a
        rw [zmod_pow_eq_ofAdd_one_pow a, map_pow, map_pow]
        simp only [MonoidHom.comp_apply, hs_inl, hfn_val, MulEquiv.coe_toMonoidHom, hρ_inl]
        rw [show redHom16to8 (Multiplicative.ofAdd (1 : ZMod 16))
            = Multiplicative.ofAdd (1 : ZMod 8)
          from by apply congrArg Multiplicative.ofAdd; decide]
        rw [show (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 16))).val = 1 from by
          decide, pow_one, hπga]
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
    have hcomp2 : redHom16to8 q.left = 1 ∧ q.right = 1 := by
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
    have hc16cases : ∀ x : Multiplicative (ZMod 16), redHom16to8 x = 1 →
        x = 1 ∨ x = Multiplicative.ofAdd (8 : ZMod 16) := by decide
    have hqleft : q.left = 1 := by
      rcases hc16cases q.left hcomp2.1 with h | h
      · exact h
      · exfalso
        rw [h] at hqfn
        rw [hfn_val] at hqfn
        rw [show (Multiplicative.toAdd (Multiplicative.ofAdd (8 : ZMod 16))).val = 8 from by
          decide] at hqfn
        rw [hga8] at hqfn
        exact hzne1 hqfn
    ext
    · exact hqleft
    · exact hqright
  exact central_ext_full_iso hG card_order32_c16c2_u15 s hs_inj

end Smallgroups.UsefulTheorems
