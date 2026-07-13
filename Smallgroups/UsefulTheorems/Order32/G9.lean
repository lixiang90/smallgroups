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

/-! ## `c`-doubled branch: `order16_wild_G9` descendants (continued)

The "`c` doubles" case: `x⁴=1`, `y²=1` (both untouched), `c²=z`, and both conjugation
relations hold exactly. Same recipe as `G8`'s `c`-doubled branch: the `C₂`-action `ψ₅`
factors through the reduction `C₄ ↠ C₂`, giving a new order-32 group
`K₈ ⋊[ψ₅∘red] C₄`. -/

/-- Reduction homomorphism `C₄ ↠ C₂`, used to factor the `C₂`-action `ψ₅` through
`c`'s doubled order. -/
private noncomputable def redHom42g9 : Multiplicative (ZMod 4) →* Multiplicative (ZMod 2) :=
  AddMonoidHom.toMultiplicative (ZMod.castHom (by norm_num) (ZMod 2)).toAddMonoidHom

/-- The `C₄`-action on `K₈` obtained by factoring `ψ₅` through `C₄ ↠ C₂`. -/
private noncomputable def psi5Act4 : Multiplicative (ZMod 4) →* MulAut K8g :=
  c2Action_psi5.comp redHom42g9

/-- The new order-32 group `K₈ ⋊[ψ₅∘red] C₄` (the `c`-doubled descendant of `G9`). -/
noncomputable abbrev order32_k8c4_psi5 : Type :=
  SemidirectProduct K8g (Multiplicative (ZMod 4)) psi5Act4

@[simp] theorem card_order32_k8c4_psi5 : Nat.card order32_k8c4_psi5 = 32 := by
  rw [SemidirectProduct.card]; simp

/-- The `c`-doubled branch over `order16_wild_G9`: `x⁴=1`, `y²=1`, `c²=z`, and both
conjugation relations hold exactly. `G` is isomorphic to `K₈ ⋊[ψ₅∘red] C₄`. -/
theorem order32_of_k8c2_psi5_quotient_doubled_c_case {G : Type*} [Group G] [Finite G]
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
    (hga4 : ga ^ 4 = 1) (hgb2 : gb ^ 2 = 1) (hgc2 : gc ^ 2 = z) (hcommab : Commute ga gb)
    (hrelgca : gc * ga * gc⁻¹ = ga * gb) (hcommgcb : Commute gc gb) :
    Nonempty (G ≃* order32_k8c4_psi5) := by
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
      fn.comp (psi5Act4 t).toMonoidHom = (MulAut.conj (fg t)).toMonoidHom.comp fn := by
    intro t
    rcases hc4cases t with rfl | rfl | rfl | rfl
    · apply monoidHom_ext_prod_ofAdd_one
      · change fn (psi5Act4 (1 : Multiplicative (ZMod 4)) (xK8 : K8g))
            = fg 1 * fn (xK8 : K8g) * (fg 1)⁻¹
        rw [show psi5Act4 (1 : Multiplicative (ZMod 4)) (xK8 : K8g) = xK8 from by
          change c2Action_psi5 (redHom42g9 1) (xK8 : K8g) = xK8
          rw [show redHom42g9 (1 : Multiplicative (ZMod 4)) = 1 from by
            apply congrArg Multiplicative.ofAdd; decide]
          decide]
        rw [fg.map_one, one_mul, inv_one, mul_one]
      · change fn (psi5Act4 (1 : Multiplicative (ZMod 4)) (yK8 : K8g))
            = fg 1 * fn (yK8 : K8g) * (fg 1)⁻¹
        rw [show psi5Act4 (1 : Multiplicative (ZMod 4)) (yK8 : K8g) = yK8 from by
          change c2Action_psi5 (redHom42g9 1) (yK8 : K8g) = yK8
          rw [show redHom42g9 (1 : Multiplicative (ZMod 4)) = 1 from by
            apply congrArg Multiplicative.ofAdd; decide]
          decide]
        rw [fg.map_one, one_mul, inv_one, mul_one]
    · apply monoidHom_ext_prod_ofAdd_one
      · change fn (psi5Act4 (Multiplicative.ofAdd (1 : ZMod 4)) (xK8 : K8g))
            = fg (Multiplicative.ofAdd (1 : ZMod 4)) * fn (xK8 : K8g)
              * (fg (Multiplicative.ofAdd (1 : ZMod 4)))⁻¹
        rw [show psi5Act4 (Multiplicative.ofAdd (1 : ZMod 4)) (xK8 : K8g) = xK8 * yK8 from by
          change c2Action_psi5 (redHom42g9 (Multiplicative.ofAdd (1 : ZMod 4))) (xK8 : K8g)
            = xK8 * yK8
          rw [show redHom42g9 (Multiplicative.ofAdd (1 : ZMod 4)) 
                   = Multiplicative.ofAdd (1 : ZMod 2)
            from by apply congrArg Multiplicative.ofAdd; decide]
          decide]
        have hfgc1 : fg (Multiplicative.ofAdd (1 : ZMod 4)) = gc := by
          rw [hfg_val, show (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 4))).val = 1
            from by decide, pow_one]
        rw [map_mul, hfnxK8, hfnyK8, hfgc1, hrelgca]
      · change fn (psi5Act4 (Multiplicative.ofAdd (1 : ZMod 4)) (yK8 : K8g))
            = fg (Multiplicative.ofAdd (1 : ZMod 4)) * fn (yK8 : K8g)
              * (fg (Multiplicative.ofAdd (1 : ZMod 4)))⁻¹
        rw [show psi5Act4 (Multiplicative.ofAdd (1 : ZMod 4)) (yK8 : K8g) = yK8 from by
          change c2Action_psi5 (redHom42g9 (Multiplicative.ofAdd (1 : ZMod 4))) (yK8 : K8g) = yK8
          rw [show redHom42g9 (Multiplicative.ofAdd (1 : ZMod 4)) 
                   = Multiplicative.ofAdd (1 : ZMod 2)
            from by apply congrArg Multiplicative.ofAdd; decide]
          decide]
        have hfgc1 : fg (Multiplicative.ofAdd (1 : ZMod 4)) = gc := by
          rw [hfg_val, show (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 4))).val = 1
            from by decide, pow_one]
        rw [hfnyK8, hfgc1, hcommgcb, mul_inv_cancel_right]
    · apply monoidHom_ext_prod_ofAdd_one
      · change fn (psi5Act4 (Multiplicative.ofAdd (2 : ZMod 4)) (xK8 : K8g))
            = fg (Multiplicative.ofAdd (2 : ZMod 4)) * fn (xK8 : K8g)
              * (fg (Multiplicative.ofAdd (2 : ZMod 4)))⁻¹
        rw [show psi5Act4 (Multiplicative.ofAdd (2 : ZMod 4)) (xK8 : K8g) = xK8 from by
          change c2Action_psi5 (redHom42g9 (Multiplicative.ofAdd (2 : ZMod 4))) (xK8 : K8g) = xK8
          rw [show redHom42g9 (Multiplicative.ofAdd (2 : ZMod 4)) 
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
      · change fn (psi5Act4 (Multiplicative.ofAdd (2 : ZMod 4)) (yK8 : K8g))
            = fg (Multiplicative.ofAdd (2 : ZMod 4)) * fn (yK8 : K8g)
              * (fg (Multiplicative.ofAdd (2 : ZMod 4)))⁻¹
        rw [show psi5Act4 (Multiplicative.ofAdd (2 : ZMod 4)) (yK8 : K8g) = yK8 from by
          change c2Action_psi5 (redHom42g9 (Multiplicative.ofAdd (2 : ZMod 4))) (yK8 : K8g) = yK8
          rw [show redHom42g9 (Multiplicative.ofAdd (2 : ZMod 4)) 
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
      · change fn (psi5Act4 (Multiplicative.ofAdd (3 : ZMod 4)) (xK8 : K8g))
            = fg (Multiplicative.ofAdd (3 : ZMod 4)) * fn (xK8 : K8g)
              * (fg (Multiplicative.ofAdd (3 : ZMod 4)))⁻¹
        rw [show psi5Act4 (Multiplicative.ofAdd (3 : ZMod 4)) (xK8 : K8g) = xK8 * yK8 from by
          change c2Action_psi5 (redHom42g9 (Multiplicative.ofAdd (3 : ZMod 4))) (xK8 : K8g)
            = xK8 * yK8
          rw [show redHom42g9 (Multiplicative.ofAdd (3 : ZMod 4)) 
                   = Multiplicative.ofAdd (1 : ZMod 2)
            from by apply congrArg Multiplicative.ofAdd; decide]
          decide]
        have hfgc3 : fg (Multiplicative.ofAdd (3 : ZMod 4)) = gc * z := by
          rw [hfg_val, show (Multiplicative.toAdd (Multiplicative.ofAdd (3 : ZMod 4))).val = 3
            from by decide, show (3 : ℕ) = 2 + 1 from rfl, pow_add, hgc2, pow_one,
            (hzcentral gc).eq]
        rw [hfgc3, map_mul, hfnxK8, hfnyK8]
        have hstep : gc * z * ga * (gc * z)⁻¹ = ga * gb := by
          rw [mul_inv_rev]
          have hmid : z * ga * z⁻¹ = ga := by
            rw [(hzcentral ga).eq]; group
          calc gc * z * ga * (z⁻¹ * gc⁻¹)
              = gc * (z * ga * z⁻¹) * gc⁻¹ := by group
            _ = gc * ga * gc⁻¹ := by rw [hmid]
            _ = ga * gb := hrelgca
        exact hstep.symm
      · change fn (psi5Act4 (Multiplicative.ofAdd (3 : ZMod 4)) (yK8 : K8g))
            = fg (Multiplicative.ofAdd (3 : ZMod 4)) * fn (yK8 : K8g)
              * (fg (Multiplicative.ofAdd (3 : ZMod 4)))⁻¹
        rw [show psi5Act4 (Multiplicative.ofAdd (3 : ZMod 4)) (yK8 : K8g) = yK8 from by
          change c2Action_psi5 (redHom42g9 (Multiplicative.ofAdd (3 : ZMod 4))) (yK8 : K8g) = yK8
          rw [show redHom42g9 (Multiplicative.ofAdd (3 : ZMod 4)) 
                   = Multiplicative.ofAdd (1 : ZMod 2)
            from by apply congrArg Multiplicative.ofAdd; decide]
          decide]
        have hfgc3 : fg (Multiplicative.ofAdd (3 : ZMod 4)) = gc * z := by
          rw [hfg_val, show (Multiplicative.toAdd (Multiplicative.ofAdd (3 : ZMod 4))).val = 3
            from by decide, show (3 : ℕ) = 2 + 1 from rfl, pow_add, hgc2, pow_one,
            (hzcentral gc).eq]
        rw [hfgc3, hfnyK8]
        have hstep : gc * z * gb * (gc * z)⁻¹ = gb := by
          rw [mul_inv_rev]
          have hmid : z * gb * z⁻¹ = gb := by
            rw [(hzcentral gb).eq]; group
          calc gc * z * gb * (z⁻¹ * gc⁻¹)
              = gc * (z * gb * z⁻¹) * gc⁻¹ := by group
            _ = gc * gb * gc⁻¹ := by rw [hmid]
            _ = gb := by rw [hcommgcb, mul_inv_cancel_right]
        exact hstep.symm
  set s : order32_k8c4_psi5 →* G := SemidirectProduct.lift fn fg hcomp with hsdef
  have hs_inl : ∀ p : K8g, s (SemidirectProduct.inl p) = fn p := by
    intro p; rw [hsdef]; exact SemidirectProduct.lift_inl fn fg hcomp p
  have hs_inr : ∀ t : Multiplicative (ZMod 4), s (SemidirectProduct.inr t) = fg t := by
    intro t; rw [hsdef]; exact SemidirectProduct.lift_inr fn fg hcomp t
  have hρcompat : ∀ t : Multiplicative (ZMod 4),
      (MonoidHom.id K8g).comp (psi5Act4 t).toMonoidHom
        = (c2Action_psi5 (redHom42g9 t)).toMonoidHom.comp (MonoidHom.id K8g) := by
    intro t; rfl
  set ρ : order32_k8c4_psi5 →* order16_wild_G9 :=
    SemidirectProduct.map (MonoidHom.id K8g) redHom42g9 hρcompat with hρdef
  have hρ_inl : ∀ p : K8g, ρ (SemidirectProduct.inl p) = SemidirectProduct.inl p := by
    intro p; rw [hρdef]; simp
  have hρ_inr : ∀ t : Multiplicative (ZMod 4),
      ρ (SemidirectProduct.inr t) = SemidirectProduct.inr (redHom42g9 t) := by
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
  have hπs : ∀ q : order32_k8c4_psi5,
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
        rw [show redHom42g9 (Multiplicative.ofAdd (1 : ZMod 4)) = Multiplicative.ofAdd (1 : ZMod 2)
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
    have hcomp2 : q.left = 1 ∧ redHom42g9 q.right = 1 := by
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
  exact central_ext_full_iso hG card_order32_k8c4_psi5 s hs_inj

/-! ## `x`-doubled branch: `order16_wild_G9` descendants (continued)

The "`x` doubles" case: `x⁴ = z` (so `x` lifts to order `8`), `y² = 1` and `c² = 1`
(both untouched), and both conjugation relations hold exactly (`cxc⁻¹ = xy`, `cyc⁻¹ = y`).
Same shape as `G8`'s `x`-doubled branch: the true normal factor becomes `⟨x,y⟩ ≅ C₈ × C₂`,
with `c` acting via `ψ₅` lifted to `C₈ × C₂`: `(p,q) ↦ (p, π(p)·q)` where `π : C₈ → C₂` is
the natural (mod-`2`) projection. This produces a new order-32 group
`(C₈ × C₂) ⋊[ψ₅'] C₂`. -/

/-- The order-16 normal factor `⟨x,y⟩ ≅ C₈ × C₂` for the `x`-doubled branch. -/
private abbrev C8C2gK8y : Type := Multiplicative (ZMod 8) × Multiplicative (ZMod 2)

/-- The natural projection `Multiplicative (ZMod 8) → Multiplicative (ZMod 2)`. -/
private noncomputable def k8ProjBigY : Multiplicative (ZMod 8) →* Multiplicative (ZMod 2) :=
  AddMonoidHom.toMultiplicative (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 8) (ZMod 2)).toAddMonoidHom

/-- `ψ₅` lifted to `C₈ × C₂`: `(p,q) ↦ (p, π(p)·q)`. -/
private noncomputable def psi5Big : C8C2gK8y ≃* C8C2gK8y where
  toFun p := (p.1, k8ProjBigY p.1 * p.2)
  invFun p := (p.1, (k8ProjBigY p.1)⁻¹ * p.2)
  left_inv p := by
    rcases p with ⟨x, y⟩; dsimp
    calc
      (x, (k8ProjBigY x)⁻¹ * (k8ProjBigY x * y)) = (x, ((k8ProjBigY x)⁻¹ * k8ProjBigY x) * y) := by
        group
      _ = (x, 1 * y) := by simp
      _ = (x, y) := by simp
  right_inv p := by
    rcases p with ⟨x, y⟩; dsimp
    calc
      (x, k8ProjBigY x * ((k8ProjBigY x)⁻¹ * y)) = (x, (k8ProjBigY x * (k8ProjBigY x)⁻¹) * y) := by
        group
      _ = (x, 1 * y) := by simp
      _ = (x, y) := by simp
  map_mul' p q := by
    rcases p with ⟨x₁, y₁⟩; rcases q with ⟨x₂, y₂⟩
    apply Prod.ext
    · rfl
    · simp [k8ProjBigY.map_mul, mul_assoc, mul_left_comm, mul_comm]

@[simp] private theorem psi5Big_sq : psi5Big ^ 2 = 1 := by
  apply MulEquiv.ext
  intro p
  rcases p with ⟨x, y⟩
  have hsq : (k8ProjBigY x) ^ 2 = 1 := by
    have hcard : Fintype.card (Multiplicative (ZMod 2)) = 2 := by simp
    have h := pow_card_eq_one (x := k8ProjBigY x)
    rwa [hcard] at h
  calc
    (psi5Big ^ 2) (x, y) = psi5Big (psi5Big (x, y)) := rfl
    _ = psi5Big (x, k8ProjBigY x * y) := rfl
    _ = (x, k8ProjBigY x * (k8ProjBigY x * y)) := rfl
    _ = (x, (k8ProjBigY x * k8ProjBigY x) * y) := by group
    _ = (x, (k8ProjBigY x ^ 2) * y) := by rw [sq]
    _ = (x, 1 * y) := by rw [hsq]
    _ = (x, y) := by simp

private lemma c2_two_cases_x5 (a : Multiplicative (ZMod 2)) :
    a = 1 ∨ a = Multiplicative.ofAdd 1 := by
  have := show ∀ a : Multiplicative (ZMod 2), a = 1 ∨ a = Multiplicative.ofAdd 1 from by decide
  exact this a

@[simp] private lemma c2_mul_self_x5 : (Multiplicative.ofAdd (1 : ZMod 2)
    * Multiplicative.ofAdd (1 : ZMod 2) : Multiplicative (ZMod 2)) = 1 := by decide

set_option linter.flexible false in
/-- The `C₂`-action on `C₈ × C₂` given by `psi5Big`. Not `private`: `Distinctness.lean`
needs to name it to show `order32_c8c2tw_u5 ≃* order32_k8xdbl_psi5`. -/
noncomputable def c8c2K8y_psi5 : Multiplicative (ZMod 2) →* MulAut C8C2gK8y where
  toFun g := if g = 1 then 1 else psi5Big
  map_one' := by simp
  map_mul' a b := by
    rcases c2_two_cases_x5 a with (rfl|rfl) <;> rcases c2_two_cases_x5 b with (rfl|rfl) <;>
      simp; try rw [← sq, psi5Big_sq]

/-- The new order-32 group `(C₈ × C₂) ⋊[ψ₅'] C₂` (the `x`-doubled descendant of `G9`). -/
noncomputable abbrev order32_k8xdbl_psi5 : Type :=
  SemidirectProduct C8C2gK8y (Multiplicative (ZMod 2)) c8c2K8y_psi5

@[simp] theorem card_order32_k8xdbl_psi5 : Nat.card order32_k8xdbl_psi5 = 32 := by
  rw [SemidirectProduct.card]; simp

/-- Reduction homomorphism `C₈ ↠ C₄` (mod-4 cast), used to collapse the doubled normal
factor `C₈ × C₂` back down to `K₈ = C₄ × C₂`. -/
private noncomputable def redHom84g9x : Multiplicative (ZMod 8) →* Multiplicative (ZMod 4) :=
  AddMonoidHom.toMultiplicative (ZMod.castHom (by norm_num : (4 : ℕ) ∣ 8) (ZMod 4)).toAddMonoidHom

/-- The combined reduction `C₈ × C₂ ↠ K₈`. -/
private noncomputable def redHomK8y : C8C2gK8y →* K8g :=
  redHom84g9x.prodMap (MonoidHom.id (Multiplicative (ZMod 2)))

/-- The `x`-doubled branch over `order16_wild_G9`: `x⁴=z`, `y²=1`, `c²=1`, and both
conjugation relations hold exactly. `G` is isomorphic to `(C₈ × C₂) ⋊[ψ₅'] C₂`. -/
theorem order32_of_k8c2_psi5_quotient_doubled_x_case {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 32) {z : G} (_hzc : z ∈ Subgroup.center G) (hzp : orderOf z = 2)
    [hnorm : (Subgroup.zpowers z).Normal]
    (e : (G ⧸ Subgroup.zpowers z) ≃* order16_wild_G9)
    {ga gb gc : G}
    (hga : (QuotientGroup.mk' (Subgroup.zpowers z)) ga
      = e.symm (SemidirectProduct.inl (xK8 : K8g)))
    (hgb : (QuotientGroup.mk' (Subgroup.zpowers z)) gb
      = e.symm (SemidirectProduct.inl (yK8 : K8g)))
    (hgc : (QuotientGroup.mk' (Subgroup.zpowers z)) gc
      = e.symm (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))))
    (hga4 : ga ^ 4 = z) (hgb2 : gb ^ 2 = 1) (hgc2 : gc ^ 2 = 1) (hcommab : Commute ga gb)
    (hrelgca : gc * ga * gc⁻¹ = ga * gb) (hcommgcb : Commute gc gb) :
    Nonempty (G ≃* order32_k8xdbl_psi5) := by
  classical
  have hz2 : z ^ 2 = 1 := by rw [← hzp]; exact pow_orderOf_eq_one z
  have hzne1 : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hzp; exact absurd hzp (by norm_num)
  have hga8 : ga ^ 8 = 1 := by
    have hh : ga ^ 8 = (ga ^ 4) ^ 2 := by rw [← pow_mul]
    rw [hh, hga4, hz2]
  set fga : Multiplicative (ZMod 8) →* G := zmodZPowHom 8 ga hga8 with hfgadef
  set fgb : Multiplicative (ZMod 2) →* G := zmodZPowHom 2 gb hgb2 with hfgbdef
  have hfga_val : ∀ a : Multiplicative (ZMod 8), fga a = ga ^ (Multiplicative.toAdd a).val := by
    intro a
    have ha : a = Multiplicative.ofAdd (((Multiplicative.toAdd a).val : ZMod 8)) := by
      rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
    have hcast : ((((Multiplicative.toAdd a).val : ℕ) : ℤ) : ZMod 8)
        = ((Multiplicative.toAdd a).val : ZMod 8) := by push_cast; ring
    conv_lhs => rw [ha, ← hcast]
    rw [hfgadef, zmodZPowHom_intCast, zpow_natCast]
  have hfgb_val : ∀ b : Multiplicative (ZMod 2), fgb b = gb ^ (Multiplicative.toAdd b).val := by
    intro b
    have hb : b = Multiplicative.ofAdd (((Multiplicative.toAdd b).val : ZMod 2)) := by
      rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
    have hcast : ((((Multiplicative.toAdd b).val : ℕ) : ℤ) : ZMod 2)
        = ((Multiplicative.toAdd b).val : ZMod 2) := by push_cast; ring
    conv_lhs => rw [hb, ← hcast]
    rw [hfgbdef, zmodZPowHom_intCast, zpow_natCast]
  have hcomm' : ∀ (a : Multiplicative (ZMod 8)) (b : Multiplicative (ZMod 2)),
      Commute (fga a) (fgb b) := by
    intro a b; rw [hfga_val, hfgb_val]; exact hcommab.pow_pow _ _
  set fn : C8C2gK8y →* G := fga.noncommCoprod fgb hcomm' with hfndef
  have hfn_apply : ∀ p : C8C2gK8y, fn p = fga p.1 * fgb p.2 := by
    intro p; rw [hfndef]; exact MonoidHom.noncommCoprod_apply fga fgb hcomm' p
  set fg : Multiplicative (ZMod 2) →* G := zmodZPowHom 2 gc hgc2 with hfgdef
  have hfgag : fga (Multiplicative.ofAdd (1 : ZMod 8)) = ga := by
    rw [hfgadef]
    have h := zmodZPowHom_intCast 8 ga hga8 1
    simp only [Int.cast_one, zpow_one] at h
    exact h
  have hfgbg : fgb (Multiplicative.ofAdd (1 : ZMod 2)) = gb := by
    rw [hfgbdef]
    have h := zmodZPowHom_intCast 2 gb hgb2 1
    simp only [Int.cast_one, zpow_one] at h
    exact h
  have hfgc : fg (Multiplicative.ofAdd (1 : ZMod 2)) = gc := by
    rw [hfgdef]
    have h := zmodZPowHom_intCast 2 gc hgc2 1
    simp only [Int.cast_one, zpow_one] at h
    exact h
  have hfngen1 : fn (Multiplicative.ofAdd (1 : ZMod 8), (1 : Multiplicative (ZMod 2))) = ga := by
    rw [hfn_apply]
    change fga (Multiplicative.ofAdd (1 : ZMod 8)) * fgb 1 = ga
    rw [fgb.map_one, mul_one, hfgag]
  have hfngen2 : fn ((1 : Multiplicative (ZMod 8)), Multiplicative.ofAdd (1 : ZMod 2)) = gb := by
    rw [hfn_apply]
    change fga 1 * fgb (Multiplicative.ofAdd (1 : ZMod 2)) = gb
    rw [fga.map_one, one_mul, hfgbg]
  have hc2cases : ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = Multiplicative.ofAdd (1 : ZMod 2) :=
    by decide
  have hphi1 : ∀ p : C8C2gK8y, c8c2K8y_psi5 (1 : Multiplicative (ZMod 2)) p = p := by decide
  have hgenact1 : c8c2K8y_psi5 (Multiplicative.ofAdd (1 : ZMod 2))
      (Multiplicative.ofAdd (1 : ZMod 8), (1 : Multiplicative (ZMod 2)))
      = (Multiplicative.ofAdd (1 : ZMod 8), Multiplicative.ofAdd (1 : ZMod 2)) := by decide
  have hgenact2 : c8c2K8y_psi5 (Multiplicative.ofAdd (1 : ZMod 2))
      ((1 : Multiplicative (ZMod 8)), Multiplicative.ofAdd (1 : ZMod 2))
      = ((1 : Multiplicative (ZMod 8)), Multiplicative.ofAdd (1 : ZMod 2)) := by decide
  have hprodgen : (Multiplicative.ofAdd (1 : ZMod 8), Multiplicative.ofAdd (1 : ZMod 2))
      = (Multiplicative.ofAdd (1 : ZMod 8), (1 : Multiplicative (ZMod 2)))
        * ((1 : Multiplicative (ZMod 8)), Multiplicative.ofAdd (1 : ZMod 2)) := by
    simp [Prod.mk_mul_mk]
  have hcomp : ∀ t : Multiplicative (ZMod 2),
      fn.comp (c8c2K8y_psi5 t).toMonoidHom = (MulAut.conj (fg t)).toMonoidHom.comp fn := by
    intro t
    rcases hc2cases t with rfl | rfl
    · apply monoidHom_ext_prod_ofAdd_one
      · change fn (c8c2K8y_psi5 (1 : Multiplicative (ZMod 2))
            (Multiplicative.ofAdd (1 : ZMod 8), (1 : Multiplicative (ZMod 2))))
            = fg 1 * fn (Multiplicative.ofAdd (1 : ZMod 8), (1 : Multiplicative (ZMod 2)))
              * (fg 1)⁻¹
        rw [hphi1, fg.map_one, one_mul, inv_one, mul_one]
      · change fn (c8c2K8y_psi5 (1 : Multiplicative (ZMod 2))
            ((1 : Multiplicative (ZMod 8)), Multiplicative.ofAdd (1 : ZMod 2)))
            = fg 1 * fn ((1 : Multiplicative (ZMod 8)), Multiplicative.ofAdd (1 : ZMod 2))
              * (fg 1)⁻¹
        rw [hphi1, fg.map_one, one_mul, inv_one, mul_one]
    · apply monoidHom_ext_prod_ofAdd_one
      · change fn (c8c2K8y_psi5 (Multiplicative.ofAdd (1 : ZMod 2))
            (Multiplicative.ofAdd (1 : ZMod 8), (1 : Multiplicative (ZMod 2))))
            = fg (Multiplicative.ofAdd (1 : ZMod 2))
              * fn (Multiplicative.ofAdd (1 : ZMod 8), (1 : Multiplicative (ZMod 2)))
              * (fg (Multiplicative.ofAdd (1 : ZMod 2)))⁻¹
        rw [hgenact1, hprodgen, map_mul, hfngen1, hfngen2, hfgc, hrelgca]
      · change fn (c8c2K8y_psi5 (Multiplicative.ofAdd (1 : ZMod 2))
            ((1 : Multiplicative (ZMod 8)), Multiplicative.ofAdd (1 : ZMod 2)))
            = fg (Multiplicative.ofAdd (1 : ZMod 2))
              * fn ((1 : Multiplicative (ZMod 8)), Multiplicative.ofAdd (1 : ZMod 2))
              * (fg (Multiplicative.ofAdd (1 : ZMod 2)))⁻¹
        rw [hgenact2, hfngen2, hfgc, hcommgcb, mul_inv_cancel_right]
  set s : order32_k8xdbl_psi5 →* G := SemidirectProduct.lift fn fg hcomp with hsdef
  have hs_inl : ∀ p : C8C2gK8y, s (SemidirectProduct.inl p) = fn p := by
    intro p; rw [hsdef]; exact SemidirectProduct.lift_inl fn fg hcomp p
  have hs_inr : ∀ t : Multiplicative (ZMod 2), s (SemidirectProduct.inr t) = fg t := by
    intro t; rw [hsdef]; exact SemidirectProduct.lift_inr fn fg hcomp t
  have hρcompat : ∀ t : Multiplicative (ZMod 2),
      redHomK8y.comp (c8c2K8y_psi5 t).toMonoidHom
        = (c2Action_psi5 t).toMonoidHom.comp redHomK8y := by
    intro t
    apply monoidHom_ext_prod_ofAdd_one
    · rcases hc2cases t with rfl | rfl
      · decide
      · decide
    · rcases hc2cases t with rfl | rfl
      · decide
      · decide
  set ρ : order32_k8xdbl_psi5 →* order16_wild_G9 :=
    SemidirectProduct.map redHomK8y (MonoidHom.id (Multiplicative (ZMod 2))) hρcompat with hρdef
  have hρ_inl : ∀ p : C8C2gK8y,
      ρ (SemidirectProduct.inl p) = SemidirectProduct.inl (redHomK8y p) := by
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
  have hredgen1 : redHomK8y (Multiplicative.ofAdd (1 : ZMod 8), (1 : Multiplicative (ZMod 2)))
      = (xK8 : K8g) := by decide
  have hredgen2 : redHomK8y ((1 : Multiplicative (ZMod 8)), Multiplicative.ofAdd (1 : ZMod 2))
      = (yK8 : K8g) := by decide
  have hπs : ∀ q : order32_k8xdbl_psi5,
      (QuotientGroup.mk' (Subgroup.zpowers z)) (s q) = e.symm (ρ q) := by
    have hgen : (QuotientGroup.mk' (Subgroup.zpowers z)).comp s = e.symm.toMonoidHom.comp ρ := by
      apply SemidirectProduct.hom_ext
      · apply monoidHom_ext_prod_ofAdd_one
        · change (QuotientGroup.mk' (Subgroup.zpowers z)) (s (SemidirectProduct.inl
              (Multiplicative.ofAdd (1 : ZMod 8), (1 : Multiplicative (ZMod 2)))))
              = e.symm (ρ (SemidirectProduct.inl
              (Multiplicative.ofAdd (1 : ZMod 8), (1 : Multiplicative (ZMod 2)))))
          rw [hs_inl, hρ_inl, hredgen1, hfngen1, hπga]
        · change (QuotientGroup.mk' (Subgroup.zpowers z)) (s (SemidirectProduct.inl
              ((1 : Multiplicative (ZMod 8)), Multiplicative.ofAdd (1 : ZMod 2))))
              = e.symm (ρ (SemidirectProduct.inl
              ((1 : Multiplicative (ZMod 8)), Multiplicative.ofAdd (1 : ZMod 2))))
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
    have hcomp2 : redHomK8y q.left = 1 ∧ q.right = 1 := by
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
    have hc8cases4 : ∀ x : Multiplicative (ZMod 8), redHom84g9x x = 1 →
        x = 1 ∨ x = Multiplicative.ofAdd (4 : ZMod 8) := by decide
    have hleft2 : q.left.2 = 1 := by
      have := congrArg Prod.snd hcomp2.1
      simpa [redHomK8y] using this
    have hleft1cases : redHom84g9x q.left.1 = 1 := by
      have := congrArg Prod.fst hcomp2.1
      simpa [redHomK8y] using this
    have hqleft1 : q.left.1 = 1 := by
      rcases hc8cases4 q.left.1 hleft1cases with h | h
      · exact h
      · exfalso
        rw [hfn_apply, h, hleft2] at hqfn
        rw [hfga_val, show (Multiplicative.toAdd (Multiplicative.ofAdd (4 : ZMod 8))).val = 4
          from by decide, fgb.map_one, mul_one] at hqfn
        rw [hga4] at hqfn
        exact hzne1 hqfn
    have hqleft : q.left = 1 := by
      apply Prod.ext hqleft1 hleft2
    exact SemidirectProduct.ext hqleft hqright
  exact central_ext_full_iso hG card_order32_k8xdbl_psi5 s hs_inj

end Smallgroups.UsefulTheorems
