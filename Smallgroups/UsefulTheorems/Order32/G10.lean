/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order16_Wild
import Smallgroups.UsefulTheorems.PGroupGeneration
import Smallgroups.UsefulTheorems.Order32.GenericTools

/-! ## Descendants of `order16_wild_G10` (`K₈ ⋊ C₂` via `ψ₆`, `Q₈ ⋊ C₂`)

`order16_wild_G10 = K₈ ⋊[ψ₆] C₂` where `ψ₆ : (x,y) ↦ (x⁻¹·ι(y), y)`, i.e. `bxb⁻¹ = x⁻¹`,
`byb⁻¹ = x²y`. Only the trivial-cocycle branch is recorded. Since we check `hcomp` only at
the two literal generator points `xK8, yK8` (not a general `(a,b)`), no power-induction is
needed at all here — both relations are used exactly once, at the generator. -/

namespace Smallgroups.UsefulTheorems

/-- The trivial-cocycle branch over `order16_wild_G10`: all relator bits vanish and the
conjugation defects vanish, so `G` splits as `order16_wild_G10 × C₂`. -/
theorem order32_of_k8c2_psi6_quotient_trivial_case {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 32) {z : G} (hzc : z ∈ Subgroup.center G) (hzp : orderOf z = 2)
    [hnorm : (Subgroup.zpowers z).Normal]
    (e : (G ⧸ Subgroup.zpowers z) ≃* order16_wild_G10)
    {ga gb gc : G}
    (hga : (QuotientGroup.mk' (Subgroup.zpowers z)) ga
      = e.symm (SemidirectProduct.inl (xK8 : K8g)))
    (hgb : (QuotientGroup.mk' (Subgroup.zpowers z)) gb
      = e.symm (SemidirectProduct.inl (yK8 : K8g)))
    (hgc : (QuotientGroup.mk' (Subgroup.zpowers z)) gc
      = e.symm (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))))
    (hga4 : ga ^ 4 = 1) (hgb2 : gb ^ 2 = 1) (hgc2 : gc ^ 2 = 1) (hcommab : Commute ga gb)
    (hrelgca : gc * ga * gc⁻¹ = ga⁻¹) (hrelgcb : gc * gb * gc⁻¹ = ga ^ 2 * gb) :
    Nonempty (G ≃* order16_wild_G10 × Multiplicative (ZMod 2)) := by
  classical
  set φ := c2Action_psi6 with hφdef
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
    have hxK8val : φ (Multiplicative.ofAdd (1 : ZMod 2)) (xK8 : K8g) = xK8⁻¹ := by
      rw [hφdef]; decide
    have hyK8val : φ (Multiplicative.ofAdd (1 : ZMod 2)) (yK8 : K8g) = xK8 ^ 2 * yK8 := by
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
        rw [hxK8val, map_inv, hfnxK8, hfgc, hrelgca]
      · change fn (φ (Multiplicative.ofAdd (1 : ZMod 2)) (yK8 : K8g))
            = fg (Multiplicative.ofAdd (1 : ZMod 2)) * fn (yK8 : K8g)
              * (fg (Multiplicative.ofAdd (1 : ZMod 2)))⁻¹
        rw [hyK8val, map_mul, map_pow, hfnxK8, hfnyK8, hfgc, hrelgcb]
  set s : order16_wild_G10 →* G := SemidirectProduct.lift fn fg hcomp with hsdef
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
  have hπs : ∀ q : order16_wild_G10,
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
  have hzrange : ∀ q : order16_wild_G10, s q = z → q = 1 := by
    intro q hqz
    have h1 := hπs q
    rw [hqz, hπz] at h1
    have h2 : q = e 1 := by
      have := congrArg e h1.symm
      simpa using this
    rw [h2, map_one]
  exact central_ext_split_iso_prod hG (card_order16_wild_G10) hzc hzp s hs_inj hzrange

/-! ## `c`-doubled branch: `order16_wild_G10` descendants (continued)

The "`c` doubles" case: `x⁴=1`, `y²=1` (both untouched), `c²=z`, and both conjugation
relations hold exactly. Same recipe as `G8`/`G9`'s `c`-doubled branches: the `C₂`-action
`ψ₆` factors through the reduction `C₄ ↠ C₂`, giving a new order-32 group
`K₈ ⋊[ψ₆∘red] C₄`. As in the trivial branch, checking `hcomp` only at the two literal
generator points `xK8, yK8` means each relation is used exactly once per case, with no
power-induction needed. -/

/-- Reduction homomorphism `C₄ ↠ C₂`, used to factor the `C₂`-action `ψ₆` through
`c`'s doubled order. -/
private noncomputable def redHom42g10 : Multiplicative (ZMod 4) →* Multiplicative (ZMod 2) :=
  AddMonoidHom.toMultiplicative (ZMod.castHom (by norm_num) (ZMod 2)).toAddMonoidHom

/-- The `C₄`-action on `K₈` obtained by factoring `ψ₆` through `C₄ ↠ C₂`. -/
private noncomputable def psi6Act4 : Multiplicative (ZMod 4) →* MulAut K8g :=
  c2Action_psi6.comp redHom42g10

/-- The new order-32 group `K₈ ⋊[ψ₆∘red] C₄` (the `c`-doubled descendant of `G10`). -/
noncomputable abbrev order32_k8c4_psi6 : Type :=
  SemidirectProduct K8g (Multiplicative (ZMod 4)) psi6Act4

@[simp] theorem card_order32_k8c4_psi6 : Nat.card order32_k8c4_psi6 = 32 := by
  rw [SemidirectProduct.card]; simp

/-- The `c`-doubled branch over `order16_wild_G10`: `x⁴=1`, `y²=1`, `c²=z`, and both
conjugation relations hold exactly. `G` is isomorphic to `K₈ ⋊[ψ₆∘red] C₄`. -/
theorem order32_of_k8c2_psi6_quotient_doubled_c_case {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 32) {z : G} (hzc : z ∈ Subgroup.center G) (hzp : orderOf z = 2)
    [hnorm : (Subgroup.zpowers z).Normal]
    (e : (G ⧸ Subgroup.zpowers z) ≃* order16_wild_G10)
    {ga gb gc : G}
    (hga : (QuotientGroup.mk' (Subgroup.zpowers z)) ga
      = e.symm (SemidirectProduct.inl (xK8 : K8g)))
    (hgb : (QuotientGroup.mk' (Subgroup.zpowers z)) gb
      = e.symm (SemidirectProduct.inl (yK8 : K8g)))
    (hgc : (QuotientGroup.mk' (Subgroup.zpowers z)) gc
      = e.symm (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))))
    (hga4 : ga ^ 4 = 1) (hgb2 : gb ^ 2 = 1) (hgc2 : gc ^ 2 = z) (hcommab : Commute ga gb)
    (hrelgca : gc * ga * gc⁻¹ = ga⁻¹) (hrelgcb : gc * gb * gc⁻¹ = ga ^ 2 * gb) :
    Nonempty (G ≃* order32_k8c4_psi6) := by
  classical
  have hz2 : z ^ 2 = 1 := by rw [← hzp]; exact pow_orderOf_eq_one z
  have hzne1 : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hzp; exact absurd hzp (by norm_num)
  have hzcentral : ∀ g : G, Commute z g := fun g => (Subgroup.mem_center_iff.mp hzc g).symm
  have hgc4 : gc ^ 4 = 1 := by
    have hh : gc ^ 4 = (gc ^ 2) ^ 2 := by rw [← pow_mul]
    rw [hh, hgc2, hz2]
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
  set fg : Multiplicative (ZMod 4) →* G := zmodZPowHom 4 gc hgc4 with hfgdef
  have hfg_val : ∀ t : Multiplicative (ZMod 4), fg t = gc ^ (Multiplicative.toAdd t).val := by
    intro t
    have ht : t = Multiplicative.ofAdd (((Multiplicative.toAdd t).val : ZMod 4)) := by
      rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
    have hcast : ((((Multiplicative.toAdd t).val : ℕ) : ℤ) : ZMod 4)
        = ((Multiplicative.toAdd t).val : ZMod 4) := by push_cast; ring
    conv_lhs => rw [ht, ← hcast]
    rw [hfgdef, zmodZPowHom_intCast, zpow_natCast]
  have hc4cases : ∀ x : Multiplicative (ZMod 4),
      x = 1 ∨ x = Multiplicative.ofAdd (1 : ZMod 4) ∨ x = Multiplicative.ofAdd (2 : ZMod 4)
        ∨ x = Multiplicative.ofAdd (3 : ZMod 4) := by decide
  have hcomp : ∀ t : Multiplicative (ZMod 4),
      fn.comp (psi6Act4 t).toMonoidHom = (MulAut.conj (fg t)).toMonoidHom.comp fn := by
    intro t
    rcases hc4cases t with rfl | rfl | rfl | rfl
    · apply monoidHom_ext_prod_ofAdd_one
      · change fn (psi6Act4 (1 : Multiplicative (ZMod 4)) (xK8 : K8g))
            = fg 1 * fn (xK8 : K8g) * (fg 1)⁻¹
        rw [show psi6Act4 (1 : Multiplicative (ZMod 4)) (xK8 : K8g) = xK8 from by
          change c2Action_psi6 (redHom42g10 1) (xK8 : K8g) = xK8
          rw [show redHom42g10 (1 : Multiplicative (ZMod 4)) = 1 from by
            apply congrArg Multiplicative.ofAdd; decide]
          decide]
        rw [fg.map_one, one_mul, inv_one, mul_one]
      · change fn (psi6Act4 (1 : Multiplicative (ZMod 4)) (yK8 : K8g))
            = fg 1 * fn (yK8 : K8g) * (fg 1)⁻¹
        rw [show psi6Act4 (1 : Multiplicative (ZMod 4)) (yK8 : K8g) = yK8 from by
          change c2Action_psi6 (redHom42g10 1) (yK8 : K8g) = yK8
          rw [show redHom42g10 (1 : Multiplicative (ZMod 4)) = 1 from by
            apply congrArg Multiplicative.ofAdd; decide]
          decide]
        rw [fg.map_one, one_mul, inv_one, mul_one]
    · apply monoidHom_ext_prod_ofAdd_one
      · change fn (psi6Act4 (Multiplicative.ofAdd (1 : ZMod 4)) (xK8 : K8g))
            = fg (Multiplicative.ofAdd (1 : ZMod 4)) * fn (xK8 : K8g)
              * (fg (Multiplicative.ofAdd (1 : ZMod 4)))⁻¹
        rw [show psi6Act4 (Multiplicative.ofAdd (1 : ZMod 4)) (xK8 : K8g) = xK8⁻¹ from by
          change c2Action_psi6 (redHom42g10 (Multiplicative.ofAdd (1 : ZMod 4))) (xK8 : K8g)
            = xK8⁻¹
          rw [show redHom42g10 (Multiplicative.ofAdd (1 : ZMod 4))
              = Multiplicative.ofAdd (1 : ZMod 2)
            from by apply congrArg Multiplicative.ofAdd; decide]
          decide]
        have hfgc1 : fg (Multiplicative.ofAdd (1 : ZMod 4)) = gc := by
          rw [hfg_val, show (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 4))).val = 1
            from by decide, pow_one]
        rw [map_inv, hfnxK8, hfgc1, hrelgca]
      · change fn (psi6Act4 (Multiplicative.ofAdd (1 : ZMod 4)) (yK8 : K8g))
            = fg (Multiplicative.ofAdd (1 : ZMod 4)) * fn (yK8 : K8g)
              * (fg (Multiplicative.ofAdd (1 : ZMod 4)))⁻¹
        rw [show psi6Act4 (Multiplicative.ofAdd (1 : ZMod 4)) (yK8 : K8g) = xK8 ^ 2 * yK8 from by
          change c2Action_psi6 (redHom42g10 (Multiplicative.ofAdd (1 : ZMod 4))) (yK8 : K8g)
            = xK8 ^ 2 * yK8
          rw [show redHom42g10 (Multiplicative.ofAdd (1 : ZMod 4))
              = Multiplicative.ofAdd (1 : ZMod 2)
            from by apply congrArg Multiplicative.ofAdd; decide]
          decide]
        have hfgc1 : fg (Multiplicative.ofAdd (1 : ZMod 4)) = gc := by
          rw [hfg_val, show (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 4))).val = 1
            from by decide, pow_one]
        rw [map_mul, map_pow, hfnxK8, hfnyK8, hfgc1, hrelgcb]
    · apply monoidHom_ext_prod_ofAdd_one
      · change fn (psi6Act4 (Multiplicative.ofAdd (2 : ZMod 4)) (xK8 : K8g))
            = fg (Multiplicative.ofAdd (2 : ZMod 4)) * fn (xK8 : K8g)
              * (fg (Multiplicative.ofAdd (2 : ZMod 4)))⁻¹
        rw [show psi6Act4 (Multiplicative.ofAdd (2 : ZMod 4)) (xK8 : K8g) = xK8 from by
          change c2Action_psi6 (redHom42g10 (Multiplicative.ofAdd (2 : ZMod 4))) (xK8 : K8g)
            = xK8
          rw [show redHom42g10 (Multiplicative.ofAdd (2 : ZMod 4))
              = Multiplicative.ofAdd (0 : ZMod 2)
            from by apply congrArg Multiplicative.ofAdd; decide]
          decide]
        have hfgc2 : fg (Multiplicative.ofAdd (2 : ZMod 4)) = z := by
          rw [hfg_val, show (Multiplicative.toAdd (Multiplicative.ofAdd (2 : ZMod 4))).val = 2
            from by decide, hgc2]
        rw [hfgc2]
        have hstep : z * fn (xK8 : K8g) * z⁻¹ = fn (xK8 : K8g) := by
          rw [(hzcentral (fn (xK8 : K8g))).eq]; group
        exact hstep.symm
      · change fn (psi6Act4 (Multiplicative.ofAdd (2 : ZMod 4)) (yK8 : K8g))
            = fg (Multiplicative.ofAdd (2 : ZMod 4)) * fn (yK8 : K8g)
              * (fg (Multiplicative.ofAdd (2 : ZMod 4)))⁻¹
        rw [show psi6Act4 (Multiplicative.ofAdd (2 : ZMod 4)) (yK8 : K8g) = yK8 from by
          change c2Action_psi6 (redHom42g10 (Multiplicative.ofAdd (2 : ZMod 4))) (yK8 : K8g)
            = yK8
          rw [show redHom42g10 (Multiplicative.ofAdd (2 : ZMod 4))
              = Multiplicative.ofAdd (0 : ZMod 2)
            from by apply congrArg Multiplicative.ofAdd; decide]
          decide]
        have hfgc2 : fg (Multiplicative.ofAdd (2 : ZMod 4)) = z := by
          rw [hfg_val, show (Multiplicative.toAdd (Multiplicative.ofAdd (2 : ZMod 4))).val = 2
            from by decide, hgc2]
        rw [hfgc2]
        have hstep : z * fn (yK8 : K8g) * z⁻¹ = fn (yK8 : K8g) := by
          rw [(hzcentral (fn (yK8 : K8g))).eq]; group
        exact hstep.symm
    · apply monoidHom_ext_prod_ofAdd_one
      · change fn (psi6Act4 (Multiplicative.ofAdd (3 : ZMod 4)) (xK8 : K8g))
            = fg (Multiplicative.ofAdd (3 : ZMod 4)) * fn (xK8 : K8g)
              * (fg (Multiplicative.ofAdd (3 : ZMod 4)))⁻¹
        rw [show psi6Act4 (Multiplicative.ofAdd (3 : ZMod 4)) (xK8 : K8g) = xK8⁻¹ from by
          change c2Action_psi6 (redHom42g10 (Multiplicative.ofAdd (3 : ZMod 4))) (xK8 : K8g)
            = xK8⁻¹
          rw [show redHom42g10 (Multiplicative.ofAdd (3 : ZMod 4))
              = Multiplicative.ofAdd (1 : ZMod 2)
            from by apply congrArg Multiplicative.ofAdd; decide]
          decide]
        have hfgc3 : fg (Multiplicative.ofAdd (3 : ZMod 4)) = gc * z := by
          rw [hfg_val, show (Multiplicative.toAdd (Multiplicative.ofAdd (3 : ZMod 4))).val = 3
            from by decide, show (3 : ℕ) = 2 + 1 from rfl, pow_add, hgc2, pow_one,
            (hzcentral gc).eq]
        rw [hfgc3, map_inv, hfnxK8]
        have hstep : gc * z * ga * (gc * z)⁻¹ = ga⁻¹ := by
          rw [mul_inv_rev]
          have hmid : z * ga * z⁻¹ = ga := by rw [(hzcentral ga).eq]; group
          calc gc * z * ga * (z⁻¹ * gc⁻¹)
              = gc * (z * ga * z⁻¹) * gc⁻¹ := by group
            _ = gc * ga * gc⁻¹ := by rw [hmid]
            _ = ga⁻¹ := hrelgca
        exact hstep.symm
      · change fn (psi6Act4 (Multiplicative.ofAdd (3 : ZMod 4)) (yK8 : K8g))
            = fg (Multiplicative.ofAdd (3 : ZMod 4)) * fn (yK8 : K8g)
              * (fg (Multiplicative.ofAdd (3 : ZMod 4)))⁻¹
        rw [show psi6Act4 (Multiplicative.ofAdd (3 : ZMod 4)) (yK8 : K8g) = xK8 ^ 2 * yK8 from by
          change c2Action_psi6 (redHom42g10 (Multiplicative.ofAdd (3 : ZMod 4))) (yK8 : K8g)
            = xK8 ^ 2 * yK8
          rw [show redHom42g10 (Multiplicative.ofAdd (3 : ZMod 4))
              = Multiplicative.ofAdd (1 : ZMod 2)
            from by apply congrArg Multiplicative.ofAdd; decide]
          decide]
        have hfgc3 : fg (Multiplicative.ofAdd (3 : ZMod 4)) = gc * z := by
          rw [hfg_val, show (Multiplicative.toAdd (Multiplicative.ofAdd (3 : ZMod 4))).val = 3
            from by decide, show (3 : ℕ) = 2 + 1 from rfl, pow_add, hgc2, pow_one,
            (hzcentral gc).eq]
        rw [map_mul, map_pow, hfnxK8, hfnyK8, hfgc3]
        have hstep : gc * z * gb * (gc * z)⁻¹ = ga ^ 2 * gb := by
          rw [mul_inv_rev]
          have hmid : z * gb * z⁻¹ = gb := by rw [(hzcentral gb).eq]; group
          calc gc * z * gb * (z⁻¹ * gc⁻¹)
              = gc * (z * gb * z⁻¹) * gc⁻¹ := by group
            _ = gc * gb * gc⁻¹ := by rw [hmid]
            _ = ga ^ 2 * gb := hrelgcb
        exact hstep.symm
  set s : order32_k8c4_psi6 →* G := SemidirectProduct.lift fn fg hcomp with hsdef
  have hs_inl : ∀ p : K8g, s (SemidirectProduct.inl p) = fn p := by
    intro p; rw [hsdef]; exact SemidirectProduct.lift_inl fn fg hcomp p
  have hs_inr : ∀ t : Multiplicative (ZMod 4), s (SemidirectProduct.inr t) = fg t := by
    intro t; rw [hsdef]; exact SemidirectProduct.lift_inr fn fg hcomp t
  have hρcompat : ∀ t : Multiplicative (ZMod 4),
      (MonoidHom.id K8g).comp (psi6Act4 t).toMonoidHom
        = (c2Action_psi6 (redHom42g10 t)).toMonoidHom.comp (MonoidHom.id K8g) := by
    intro t; rfl
  set ρ : order32_k8c4_psi6 →* order16_wild_G10 :=
    SemidirectProduct.map (MonoidHom.id K8g) redHom42g10 hρcompat with hρdef
  have hρ_inl : ∀ p : K8g, ρ (SemidirectProduct.inl p) = SemidirectProduct.inl p := by
    intro p; rw [hρdef]; simp
  have hρ_inr : ∀ t : Multiplicative (ZMod 4),
      ρ (SemidirectProduct.inr t) = SemidirectProduct.inr (redHom42g10 t) := by
    intro t; rw [hρdef]; exact SemidirectProduct.map_inr _ _ _ t
  have hzker : z ∈ (QuotientGroup.mk' (Subgroup.zpowers z)).ker := by
    rw [QuotientGroup.ker_mk']; exact Subgroup.mem_zpowers z
  have hπz : (QuotientGroup.mk' (Subgroup.zpowers z)) z = 1 := MonoidHom.mem_ker.mp hzker
  have hπga : (QuotientGroup.mk' (Subgroup.zpowers z)) ga
      = e.symm (SemidirectProduct.inl (xK8 : K8g)) := hga
  have hπgb : (QuotientGroup.mk' (Subgroup.zpowers z)) gb
      = e.symm (SemidirectProduct.inl (yK8 : K8g)) := hgb
  have hπgc : (QuotientGroup.mk' (Subgroup.zpowers z)) gc
      = e.symm (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))) := hgc
  have hπs : ∀ q : order32_k8c4_psi6,
      (QuotientGroup.mk' (Subgroup.zpowers z)) (s q) = e.symm (ρ q) := by
    have hgen : (QuotientGroup.mk' (Subgroup.zpowers z)).comp s = e.symm.toMonoidHom.comp ρ := by
      apply SemidirectProduct.hom_ext
      · apply monoidHom_ext_prod_ofAdd_one
        · change (QuotientGroup.mk' (Subgroup.zpowers z)) (s (SemidirectProduct.inl (xK8 : K8g)))
              = e.symm (ρ (SemidirectProduct.inl (xK8 : K8g)))
          rw [hs_inl, hρ_inl, hfnxK8, hπga]
        · change (QuotientGroup.mk' (Subgroup.zpowers z)) (s (SemidirectProduct.inl (yK8 : K8g)))
              = e.symm (ρ (SemidirectProduct.inl (yK8 : K8g)))
          rw [hs_inl, hρ_inl, hfnyK8, hπgb]
      · apply MonoidHom.ext; intro t
        rw [zmod_pow_eq_ofAdd_one_pow t, map_pow, map_pow]
        simp only [MonoidHom.comp_apply, hs_inr, hfg_val, MulEquiv.coe_toMonoidHom, hρ_inr]
        rw [show (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 4))).val = 1 from by
          decide, pow_one]
        rw [show redHom42g10 (Multiplicative.ofAdd (1 : ZMod 4))
            = Multiplicative.ofAdd (1 : ZMod 2)
          from by apply congrArg Multiplicative.ofAdd; decide]
        rw [hπgc]
    intro q
    have := DFunLike.congr_fun hgen q
    simpa using this
  have hs_inj : Function.Injective s := by
    refine (injective_iff_map_eq_one _).mpr ?_
    intro q hq
    have hρq1 : e.symm (ρ q) = 1 := by rw [← hπs q, hq, map_one]
    have hρq : ρ q = 1 := e.symm.injective (by rw [hρq1, map_one])
    have hcomp2 : q.left = 1 ∧ redHom42g10 q.right = 1 := by
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
    have hqright1 : q.right = 1 := by
      rcases hc4cases q.right with h | h | h | h
      · exact h
      · exfalso
        rw [h, hfg_val] at hqfg
        rw [show (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 4))).val = 1 from by
          decide, pow_one] at hqfg
        have hgc2eq1 : gc ^ 2 = 1 := by
          rw [show (2 : ℕ) = 1 + 1 from rfl, pow_add, hqfg]; group
        rw [hgc2] at hgc2eq1
        exact hzne1 hgc2eq1
      · exfalso
        rw [h, hfg_val] at hqfg
        rw [show (Multiplicative.toAdd (Multiplicative.ofAdd (2 : ZMod 4))).val = 2 from by
          decide, hgc2] at hqfg
        exact hzne1 hqfg
      · exfalso
        rw [h, hfg_val] at hqfg
        rw [show (Multiplicative.toAdd (Multiplicative.ofAdd (3 : ZMod 4))).val = 3 from by
          decide] at hqfg
        have hgc3 : gc ^ 3 = gc * z := by
          rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, hgc2, pow_one, (hzcentral gc).eq]
        rw [hgc3] at hqfg
        have hgcz : gc = z⁻¹ := eq_inv_of_mul_eq_one_left hqfg
        have hzinv : z⁻¹ = z := (eq_inv_of_mul_eq_one_left (by rw [← sq]; exact hz2)).symm
        rw [hzinv] at hgcz
        have hzz : gc ^ 2 = z := hgc2
        rw [hgcz] at hzz
        rw [hz2] at hzz
        exact hzne1 hzz.symm
    exact SemidirectProduct.ext hqleft hqright1
  exact central_ext_full_iso hG card_order32_k8c4_psi6 s hs_inj

/-! ## `y`-doubled branch: `order16_wild_G10` descendants (continued)

The "`y` doubles" case: `x⁴ = 1` (untouched), `y² = z` (so `y` lifts to order `4`),
`c² = 1` (untouched), and both conjugation relations hold exactly (`cxc⁻¹ = x⁻¹`,
`cyc⁻¹ = x²y`). Unlike the (blocked) `x`-doubled branch, this direction is fine: the
shift term `ι(y) = x²` in `ψ₆` is a FUNCTION OF `y`, landing in the (unchanged) `x`
factor — doubling `y` only requires precomposing `ι` with the (always-valid,
"decreasing") mod-`2` projection `C₄ ↠ C₂`, i.e. `ι' := ι ∘ π` where `π = k8Proj` and
`ι = k8Emb` (both already defined in `Order16_Wild.lean`). The true normal factor
becomes `⟨x,y⟩ ≅ C₄ × C₄`, giving a new order-32 group `(C₄ × C₄) ⋊[ψ₆'] C₂`. -/

/-- The order-16 normal factor `⟨x,y⟩ ≅ C₄ × C₄` for the `y`-doubled branch. -/
private abbrev C4C4gK8yG10 : Type := Multiplicative (ZMod 4) × Multiplicative (ZMod 4)

/-- The shift `ι' := k8Emb ∘ k8Proj : C₄ → C₄`, i.e. `y ↦ x²` factored through the
mod-`2` projection of the (now doubled) `y`. -/
private noncomputable def k8EmbProjBig : Multiplicative (ZMod 4) →* Multiplicative (ZMod 4) :=
  k8Emb.comp k8Proj

/-- `ψ₆` lifted to `C₄ × C₄`: `(p,q) ↦ (p⁻¹·ι'(q), q)`. -/
private noncomputable def psi6BigY : C4C4gK8yG10 ≃* C4C4gK8yG10 where
  toFun p := (p.1⁻¹ * k8EmbProjBig p.2, p.2)
  invFun p := (p.1⁻¹ * k8EmbProjBig p.2, p.2)
  left_inv p := by revert p; decide
  right_inv p := by revert p; decide
  map_mul' p q := by revert p q; decide

@[simp] private theorem psi6BigY_sq : psi6BigY ^ 2 = 1 := by
  apply MulEquiv.ext
  intro p
  change psi6BigY (psi6BigY p) = p
  revert p; decide

private lemma c2_two_cases_y6 (a : Multiplicative (ZMod 2)) :
    a = 1 ∨ a = Multiplicative.ofAdd 1 := by
  have := show ∀ a : Multiplicative (ZMod 2), a = 1 ∨ a = Multiplicative.ofAdd 1 from by decide
  exact this a

@[simp] private lemma c2_mul_self_y6 : (Multiplicative.ofAdd (1 : ZMod 2)
    * Multiplicative.ofAdd (1 : ZMod 2) : Multiplicative (ZMod 2)) = 1 := by decide

set_option linter.flexible false in
/-- The `C₂`-action on `C₄ × C₄` given by `psi6BigY`. -/
private noncomputable def c4c4K8yG10_psi6 : Multiplicative (ZMod 2) →* MulAut C4C4gK8yG10 where
  toFun g := if g = 1 then 1 else psi6BigY
  map_one' := by simp
  map_mul' a b := by
    rcases c2_two_cases_y6 a with (rfl|rfl) <;> rcases c2_two_cases_y6 b with (rfl|rfl) <;>
      simp; try rw [← sq, psi6BigY_sq]

/-- The new order-32 group `(C₄ × C₄) ⋊[ψ₆'] C₂` (the `y`-doubled descendant of `G10`). -/
noncomputable abbrev order32_k8ydbl_psi6 : Type :=
  SemidirectProduct C4C4gK8yG10 (Multiplicative (ZMod 2)) c4c4K8yG10_psi6

@[simp] theorem card_order32_k8ydbl_psi6 : Nat.card order32_k8ydbl_psi6 = 32 := by
  rw [SemidirectProduct.card]; simp

/-- Reduction homomorphism `C₄ ↠ C₂` (mod-2 cast), used to collapse the doubled `y`
factor back down to `C₂`. -/
private noncomputable def redHom42g10y : Multiplicative (ZMod 4) →* Multiplicative (ZMod 2) :=
  AddMonoidHom.toMultiplicative (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)).toAddMonoidHom

/-- The combined reduction `C₄ × C₄ ↠ K₈` (identity on the first factor, mod-2 on the
second). -/
private noncomputable def redHomK8yG10 : C4C4gK8yG10 →* K8g :=
  (MonoidHom.id (Multiplicative (ZMod 4))).prodMap redHom42g10y

/-- The `y`-doubled branch over `order16_wild_G10`: `x⁴=1`, `y²=z`, `c²=1`, and both
conjugation relations hold exactly. `G` is isomorphic to `(C₄ × C₄) ⋊[ψ₆'] C₂`. -/
theorem order32_of_k8c2_psi6_quotient_doubled_y_case {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 32) {z : G} (_hzc : z ∈ Subgroup.center G) (hzp : orderOf z = 2)
    [hnorm : (Subgroup.zpowers z).Normal]
    (e : (G ⧸ Subgroup.zpowers z) ≃* order16_wild_G10)
    {ga gb gc : G}
    (hga : (QuotientGroup.mk' (Subgroup.zpowers z)) ga
      = e.symm (SemidirectProduct.inl (xK8 : K8g)))
    (hgb : (QuotientGroup.mk' (Subgroup.zpowers z)) gb
      = e.symm (SemidirectProduct.inl (yK8 : K8g)))
    (hgc : (QuotientGroup.mk' (Subgroup.zpowers z)) gc
      = e.symm (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))))
    (hga4 : ga ^ 4 = 1) (hgb2 : gb ^ 2 = z) (hgc2 : gc ^ 2 = 1) (hcommab : Commute ga gb)
    (hrelgca : gc * ga * gc⁻¹ = ga⁻¹) (hrelgcb : gc * gb * gc⁻¹ = ga ^ 2 * gb) :
    Nonempty (G ≃* order32_k8ydbl_psi6) := by
  classical
  have hz2 : z ^ 2 = 1 := by rw [← hzp]; exact pow_orderOf_eq_one z
  have hzne1 : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hzp; exact absurd hzp (by norm_num)
  have hgb4 : gb ^ 4 = 1 := by
    have hh : gb ^ 4 = (gb ^ 2) ^ 2 := by rw [← pow_mul]
    rw [hh, hgb2, hz2]
  set fga : Multiplicative (ZMod 4) →* G := zmodZPowHom 4 ga hga4 with hfgadef
  set fgb : Multiplicative (ZMod 4) →* G := zmodZPowHom 4 gb hgb4 with hfgbdef
  have hfga_val : ∀ a : Multiplicative (ZMod 4), fga a = ga ^ (Multiplicative.toAdd a).val := by
    intro a
    have ha : a = Multiplicative.ofAdd (((Multiplicative.toAdd a).val : ZMod 4)) := by
      rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
    have hcast : ((((Multiplicative.toAdd a).val : ℕ) : ℤ) : ZMod 4)
        = ((Multiplicative.toAdd a).val : ZMod 4) := by push_cast; ring
    conv_lhs => rw [ha, ← hcast]
    rw [hfgadef, zmodZPowHom_intCast, zpow_natCast]
  have hfgb_val : ∀ b : Multiplicative (ZMod 4), fgb b = gb ^ (Multiplicative.toAdd b).val := by
    intro b
    have hb : b = Multiplicative.ofAdd (((Multiplicative.toAdd b).val : ZMod 4)) := by
      rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
    have hcast : ((((Multiplicative.toAdd b).val : ℕ) : ℤ) : ZMod 4)
        = ((Multiplicative.toAdd b).val : ZMod 4) := by push_cast; ring
    conv_lhs => rw [hb, ← hcast]
    rw [hfgbdef, zmodZPowHom_intCast, zpow_natCast]
  have hcomm' : ∀ (a : Multiplicative (ZMod 4)) (b : Multiplicative (ZMod 4)),
      Commute (fga a) (fgb b) := by
    intro a b; rw [hfga_val, hfgb_val]; exact hcommab.pow_pow _ _
  set fn : C4C4gK8yG10 →* G := fga.noncommCoprod fgb hcomm' with hfndef
  have hfn_apply : ∀ p : C4C4gK8yG10, fn p = fga p.1 * fgb p.2 := by
    intro p; rw [hfndef]; exact MonoidHom.noncommCoprod_apply fga fgb hcomm' p
  set fg : Multiplicative (ZMod 2) →* G := zmodZPowHom 2 gc hgc2 with hfgdef
  have hfgag : fga (Multiplicative.ofAdd (1 : ZMod 4)) = ga := by
    rw [hfgadef]
    have h := zmodZPowHom_intCast 4 ga hga4 1
    simp only [Int.cast_one, zpow_one] at h
    exact h
  have hfgbg : fgb (Multiplicative.ofAdd (1 : ZMod 4)) = gb := by
    rw [hfgbdef]
    have h := zmodZPowHom_intCast 4 gb hgb4 1
    simp only [Int.cast_one, zpow_one] at h
    exact h
  have hfgc : fg (Multiplicative.ofAdd (1 : ZMod 2)) = gc := by
    rw [hfgdef]
    have h := zmodZPowHom_intCast 2 gc hgc2 1
    simp only [Int.cast_one, zpow_one] at h
    exact h
  have hfngen1 : fn (Multiplicative.ofAdd (1 : ZMod 4), (1 : Multiplicative (ZMod 4))) = ga := by
    rw [hfn_apply]
    change fga (Multiplicative.ofAdd (1 : ZMod 4)) * fgb 1 = ga
    rw [fgb.map_one, mul_one, hfgag]
  have hfngen2 : fn ((1 : Multiplicative (ZMod 4)), Multiplicative.ofAdd (1 : ZMod 4)) = gb := by
    rw [hfn_apply]
    change fga 1 * fgb (Multiplicative.ofAdd (1 : ZMod 4)) = gb
    rw [fga.map_one, one_mul, hfgbg]
  have hga2eq : fn (Multiplicative.ofAdd (2 : ZMod 4), (1 : Multiplicative (ZMod 4))) = ga ^ 2 := by
    rw [hfn_apply]
    change fga (Multiplicative.ofAdd (2 : ZMod 4)) * fgb 1 = ga ^ 2
    rw [fgb.map_one, mul_one, hfga_val,
      show (Multiplicative.toAdd (Multiplicative.ofAdd (2 : ZMod 4))).val = 2 from by decide]
  have hc2cases : ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = Multiplicative.ofAdd (1 : ZMod 2) :=
    by decide
  have hphi1 : ∀ p : C4C4gK8yG10, c4c4K8yG10_psi6 (1 : Multiplicative (ZMod 2)) p = p := by decide
  have hgenact1 : c4c4K8yG10_psi6 (Multiplicative.ofAdd (1 : ZMod 2))
      (Multiplicative.ofAdd (1 : ZMod 4), (1 : Multiplicative (ZMod 4)))
      = (Multiplicative.ofAdd (1 : ZMod 4), (1 : Multiplicative (ZMod 4)))⁻¹ := by decide
  have hgenact2 : c4c4K8yG10_psi6 (Multiplicative.ofAdd (1 : ZMod 2))
      ((1 : Multiplicative (ZMod 4)), Multiplicative.ofAdd (1 : ZMod 4))
      = (Multiplicative.ofAdd (2 : ZMod 4), (1 : Multiplicative (ZMod 4)))
        * ((1 : Multiplicative (ZMod 4)), Multiplicative.ofAdd (1 : ZMod 4)) := by decide
  have hcomp : ∀ t : Multiplicative (ZMod 2),
      fn.comp (c4c4K8yG10_psi6 t).toMonoidHom = (MulAut.conj (fg t)).toMonoidHom.comp fn := by
    intro t
    rcases hc2cases t with rfl | rfl
    · apply monoidHom_ext_prod_ofAdd_one
      · change fn (c4c4K8yG10_psi6 (1 : Multiplicative (ZMod 2))
            (Multiplicative.ofAdd (1 : ZMod 4), (1 : Multiplicative (ZMod 4))))
            = fg 1 * fn (Multiplicative.ofAdd (1 : ZMod 4), (1 : Multiplicative (ZMod 4)))
              * (fg 1)⁻¹
        rw [hphi1, fg.map_one, one_mul, inv_one, mul_one]
      · change fn (c4c4K8yG10_psi6 (1 : Multiplicative (ZMod 2))
            ((1 : Multiplicative (ZMod 4)), Multiplicative.ofAdd (1 : ZMod 4)))
            = fg 1 * fn ((1 : Multiplicative (ZMod 4)), Multiplicative.ofAdd (1 : ZMod 4))
              * (fg 1)⁻¹
        rw [hphi1, fg.map_one, one_mul, inv_one, mul_one]
    · apply monoidHom_ext_prod_ofAdd_one
      · change fn (c4c4K8yG10_psi6 (Multiplicative.ofAdd (1 : ZMod 2))
            (Multiplicative.ofAdd (1 : ZMod 4), (1 : Multiplicative (ZMod 4))))
            = fg (Multiplicative.ofAdd (1 : ZMod 2))
              * fn (Multiplicative.ofAdd (1 : ZMod 4), (1 : Multiplicative (ZMod 4)))
              * (fg (Multiplicative.ofAdd (1 : ZMod 2)))⁻¹
        rw [hgenact1, map_inv, hfngen1, hfgc, hrelgca]
      · change fn (c4c4K8yG10_psi6 (Multiplicative.ofAdd (1 : ZMod 2))
            ((1 : Multiplicative (ZMod 4)), Multiplicative.ofAdd (1 : ZMod 4)))
            = fg (Multiplicative.ofAdd (1 : ZMod 2))
              * fn ((1 : Multiplicative (ZMod 4)), Multiplicative.ofAdd (1 : ZMod 4))
              * (fg (Multiplicative.ofAdd (1 : ZMod 2)))⁻¹
        rw [hgenact2, map_mul, hga2eq, hfngen2, hfgc, hrelgcb]
  set s : order32_k8ydbl_psi6 →* G := SemidirectProduct.lift fn fg hcomp with hsdef
  have hs_inl : ∀ p : C4C4gK8yG10, s (SemidirectProduct.inl p) = fn p := by
    intro p; rw [hsdef]; exact SemidirectProduct.lift_inl fn fg hcomp p
  have hs_inr : ∀ t : Multiplicative (ZMod 2), s (SemidirectProduct.inr t) = fg t := by
    intro t; rw [hsdef]; exact SemidirectProduct.lift_inr fn fg hcomp t
  have hρcompat : ∀ t : Multiplicative (ZMod 2),
      redHomK8yG10.comp (c4c4K8yG10_psi6 t).toMonoidHom
        = (c2Action_psi6 t).toMonoidHom.comp redHomK8yG10 := by
    intro t
    apply monoidHom_ext_prod_ofAdd_one
    · rcases hc2cases t with rfl | rfl
      · decide
      · decide
    · rcases hc2cases t with rfl | rfl
      · decide
      · decide
  set ρ : order32_k8ydbl_psi6 →* order16_wild_G10 :=
    SemidirectProduct.map redHomK8yG10 (MonoidHom.id (Multiplicative (ZMod 2))) hρcompat with hρdef
  have hρ_inl : ∀ p : C4C4gK8yG10,
      ρ (SemidirectProduct.inl p) = SemidirectProduct.inl (redHomK8yG10 p) := by
    intro p; rw [hρdef]; exact SemidirectProduct.map_inl _ _ _ p
  have hρ_inr : ∀ t : Multiplicative (ZMod 2),
      ρ (SemidirectProduct.inr t) = SemidirectProduct.inr t := by
    intro t; rw [hρdef]; simp
  have hzker : z ∈ (QuotientGroup.mk' (Subgroup.zpowers z)).ker := by
    rw [QuotientGroup.ker_mk']; exact Subgroup.mem_zpowers z
  have hπz : (QuotientGroup.mk' (Subgroup.zpowers z)) z = 1 := MonoidHom.mem_ker.mp hzker
  have hπga : (QuotientGroup.mk' (Subgroup.zpowers z)) ga
      = e.symm (SemidirectProduct.inl (xK8 : K8g)) := hga
  have hπgb : (QuotientGroup.mk' (Subgroup.zpowers z)) gb
      = e.symm (SemidirectProduct.inl (yK8 : K8g)) := hgb
  have hπgc : (QuotientGroup.mk' (Subgroup.zpowers z)) gc
      = e.symm (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))) := hgc
  have hredgen1 : redHomK8yG10 (Multiplicative.ofAdd (1 : ZMod 4), (1 : Multiplicative (ZMod 4)))
      = (xK8 : K8g) := by decide
  have hredgen2 : redHomK8yG10 ((1 : Multiplicative (ZMod 4)), Multiplicative.ofAdd (1 : ZMod 4))
      = (yK8 : K8g) := by decide
  have hπs : ∀ q : order32_k8ydbl_psi6,
      (QuotientGroup.mk' (Subgroup.zpowers z)) (s q) = e.symm (ρ q) := by
    have hgen : (QuotientGroup.mk' (Subgroup.zpowers z)).comp s = e.symm.toMonoidHom.comp ρ := by
      apply SemidirectProduct.hom_ext
      · apply monoidHom_ext_prod_ofAdd_one
        · change (QuotientGroup.mk' (Subgroup.zpowers z)) (s (SemidirectProduct.inl
              (Multiplicative.ofAdd (1 : ZMod 4), (1 : Multiplicative (ZMod 4)))))
              = e.symm (ρ (SemidirectProduct.inl
              (Multiplicative.ofAdd (1 : ZMod 4), (1 : Multiplicative (ZMod 4)))))
          rw [hs_inl, hρ_inl, hredgen1, hfngen1, hπga]
        · change (QuotientGroup.mk' (Subgroup.zpowers z)) (s (SemidirectProduct.inl
              ((1 : Multiplicative (ZMod 4)), Multiplicative.ofAdd (1 : ZMod 4))))
              = e.symm (ρ (SemidirectProduct.inl
              ((1 : Multiplicative (ZMod 4)), Multiplicative.ofAdd (1 : ZMod 4))))
          rw [hs_inl, hρ_inl, hredgen2, hfngen2, hπgb]
      · apply MonoidHom.ext; intro t
        rw [zmod_pow_eq_ofAdd_one_pow t, map_pow, map_pow]
        simp only [MonoidHom.comp_apply, hs_inr, hfgdef, MulEquiv.coe_toMonoidHom, hρ_inr]
        have hb : (zmodZPowHom 2 gc hgc2) (Multiplicative.ofAdd (1 : ZMod 2)) = gc := by
          rw [← hfgdef]; exact hfgc
        rw [hb, hπgc]
    intro q
    have := DFunLike.congr_fun hgen q
    simpa using this
  have hs_inj : Function.Injective s := by
    refine (injective_iff_map_eq_one _).mpr ?_
    intro q hq
    have hρq1 : e.symm (ρ q) = 1 := by rw [← hπs q, hq, map_one]
    have hρq : ρ q = 1 := e.symm.injective (by rw [hρq1, map_one])
    have hcomp2 : redHomK8yG10 q.left = 1 ∧ q.right = 1 := by
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
    have hc4cases2 : ∀ x : Multiplicative (ZMod 4), redHom42g10y x = 1 →
        x = 1 ∨ x = Multiplicative.ofAdd (2 : ZMod 4) := by decide
    have hleft1 : q.left.1 = 1 := by
      have := congrArg Prod.fst hcomp2.1
      simpa [redHomK8yG10] using this
    have hleft2cases : redHom42g10y q.left.2 = 1 := by
      have := congrArg Prod.snd hcomp2.1
      simpa [redHomK8yG10] using this
    have hqleft2 : q.left.2 = 1 := by
      rcases hc4cases2 q.left.2 hleft2cases with h | h
      · exact h
      · exfalso
        rw [hfn_apply, h, hleft1] at hqfn
        rw [fga.map_one, one_mul, hfgb_val, show
          (Multiplicative.toAdd (Multiplicative.ofAdd (2 : ZMod 4))).val = 2 from by decide] at hqfn
        rw [hgb2] at hqfn
        exact hzne1 hqfn
    have hqleft : q.left = 1 := by
      apply Prod.ext hleft1 hqleft2
    exact SemidirectProduct.ext hqleft hqright
  exact central_ext_full_iso hG card_order32_k8ydbl_psi6 s hs_inj

end Smallgroups.UsefulTheorems
