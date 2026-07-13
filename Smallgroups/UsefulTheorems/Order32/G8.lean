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

/-! ## `c`-doubled branch: `order16_wild_G8` descendants (continued)

The "`c` doubles" case: `x⁴=1`, `y²=1` (both untouched), `c²=z` (so `c` lifts to order
`4`), and both conjugation relations hold exactly. Since `z` is central, doubling the
ACTING generator `c` never adds a numerical obstruction (the same phenomenon as the
`C₈⋊C₂` family's `b`-doubled branches): the `C₂`-action `ψ₃` factors through the
reduction `C₄ ↠ C₂`, giving a new order-32 group `K₈ ⋊[ψ₃∘red] C₄`. -/

/-- Reduction homomorphism `C₄ ↠ C₂`, used to factor the `C₂`-action `ψ₃` through
`c`'s doubled order. -/
private noncomputable def redHom42g8 : Multiplicative (ZMod 4) →* Multiplicative (ZMod 2) :=
  AddMonoidHom.toMultiplicative (ZMod.castHom (by norm_num) (ZMod 2)).toAddMonoidHom

/-- The `C₄`-action on `K₈` obtained by factoring `ψ₃` through `C₄ ↠ C₂`. -/
private noncomputable def psi3Act4 : Multiplicative (ZMod 4) →* MulAut K8g :=
  c2Action_psi3.comp redHom42g8

/-- The new order-32 group `K₈ ⋊[ψ₃∘red] C₄` (the `c`-doubled descendant of `G8`). -/
noncomputable abbrev order32_k8c4_psi3 : Type :=
  SemidirectProduct K8g (Multiplicative (ZMod 4)) psi3Act4

@[simp] theorem card_order32_k8c4_psi3 : Nat.card order32_k8c4_psi3 = 32 := by
  rw [SemidirectProduct.card]; simp

/-- The `c`-doubled branch over `order16_wild_G8`: `x⁴=1`, `y²=1`, `c²=z`, and both
conjugation relations hold exactly. `G` is isomorphic to `K₈ ⋊[ψ₃∘red] C₄`. -/
theorem order32_of_k8c2_d8xc2_quotient_doubled_c_case {G : Type*} [Group G] [Finite G]
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
    (hga4 : ga ^ 4 = 1) (hgb2 : gb ^ 2 = 1) (hgc2 : gc ^ 2 = z) (hcommab : Commute ga gb)
    (hrelgca : gc * ga * gc⁻¹ = ga⁻¹) (hcommgcb : Commute gc gb) :
    Nonempty (G ≃* order32_k8c4_psi3) := by
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
  have hfn_apply : ∀ p : K8g, fn p = fg1 p.1 * fg2 p.2 := by
    intro p; rw [hfndef]; exact MonoidHom.noncommCoprod_apply fg1 fg2 hcomm' p
  set fg : Multiplicative (ZMod 4) →* G := zmodZPowHom 4 gc hgc4 with hfgdef
  have hfg_val : ∀ t : Multiplicative (ZMod 4), fg t = gc ^ (Multiplicative.toAdd t).val := by
    intro t
    have ht : t = Multiplicative.ofAdd (((Multiplicative.toAdd t).val : ZMod 4)) := by
      rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
    have hcast : ((((Multiplicative.toAdd t).val : ℕ) : ℤ) : ZMod 4)
        = ((Multiplicative.toAdd t).val : ZMod 4) := by push_cast; ring
    conv_lhs => rw [ht, ← hcast]
    rw [hfgdef, zmodZPowHom_intCast, zpow_natCast]
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
  have hc4cases : ∀ x : Multiplicative (ZMod 4),
      x = 1 ∨ x = Multiplicative.ofAdd (1 : ZMod 4) ∨ x = Multiplicative.ofAdd (2 : ZMod 4)
        ∨ x = Multiplicative.ofAdd (3 : ZMod 4) := by decide
  have hcomp : ∀ t : Multiplicative (ZMod 4),
      fn.comp (psi3Act4 t).toMonoidHom = (MulAut.conj (fg t)).toMonoidHom.comp fn := by
    intro t
    apply MonoidHom.ext
    rintro ⟨a, b⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    revert a b
    rcases hc4cases t with rfl | rfl | rfl | rfl
    · have e1 : ∀ p : K8g, psi3Act4 (1 : Multiplicative (ZMod 4)) p = p := by
        intro p
        change c2Action_psi3 (redHom42g8 1) p = p
        rw [show redHom42g8 (1 : Multiplicative (ZMod 4)) = 1 from by
          apply congrArg Multiplicative.ofAdd; decide]
        revert p; decide
      rintro a b
      rw [e1, hfn_apply, fg.map_one, one_mul, inv_one, mul_one]
    · have e1 : ∀ p : K8g, psi3Act4 (Multiplicative.ofAdd (1 : ZMod 4)) p = (p.1⁻¹, p.2) := by
        intro p
        change c2Action_psi3 (redHom42g8 (Multiplicative.ofAdd (1 : ZMod 4))) p = (p.1⁻¹, p.2)
        rw [show redHom42g8 (Multiplicative.ofAdd (1 : ZMod 4)) = Multiplicative.ofAdd (1 : ZMod 2)
          from by apply congrArg Multiplicative.ofAdd; decide]
        revert p; decide
      rintro a b
      rw [e1, hfn_apply, hfn_apply, map_inv]
      have hfgc1 : fg (Multiplicative.ofAdd (1 : ZMod 4)) = gc := by
        rw [hfg_val, show (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 4))).val = 1
          from by decide, pow_one]
      rw [hfgc1]
      rw [show gc * (fg1 a * fg2 b) * gc⁻¹ = (gc * fg1 a * gc⁻¹) * (gc * fg2 b * gc⁻¹) from by
        group]
      rw [hconjga a, hconjgb b]
    · have e1 : ∀ p : K8g, psi3Act4 (Multiplicative.ofAdd (2 : ZMod 4)) p = p := by
        intro p
        change c2Action_psi3 (redHom42g8 (Multiplicative.ofAdd (2 : ZMod 4))) p = p
        rw [show redHom42g8 (Multiplicative.ofAdd (2 : ZMod 4)) = Multiplicative.ofAdd (0 : ZMod 2)
          from by apply congrArg Multiplicative.ofAdd; decide]
        revert p; decide
      rintro a b
      rw [e1, hfn_apply]
      have hfgc2 : fg (Multiplicative.ofAdd (2 : ZMod 4)) = z := by
        rw [hfg_val, show (Multiplicative.toAdd (Multiplicative.ofAdd (2 : ZMod 4))).val = 2
          from by decide, hgc2]
      rw [hfgc2]
      have hstep : z * (fg1 a * fg2 b) * z⁻¹ = fg1 a * fg2 b := by
        rw [(hzcentral (fg1 a * fg2 b)).eq]; group
      exact hstep.symm
    · have e1 : ∀ p : K8g, psi3Act4 (Multiplicative.ofAdd (3 : ZMod 4)) p = (p.1⁻¹, p.2) := by
        intro p
        change c2Action_psi3 (redHom42g8 (Multiplicative.ofAdd (3 : ZMod 4))) p = (p.1⁻¹, p.2)
        rw [show redHom42g8 (Multiplicative.ofAdd (3 : ZMod 4)) = Multiplicative.ofAdd (1 : ZMod 2)
          from by apply congrArg Multiplicative.ofAdd; decide]
        revert p; decide
      rintro a b
      rw [e1, hfn_apply, hfn_apply, map_inv]
      have hfgc3 : fg (Multiplicative.ofAdd (3 : ZMod 4)) = gc * z := by
        rw [hfg_val, show (Multiplicative.toAdd (Multiplicative.ofAdd (3 : ZMod 4))).val = 3
          from by decide, show (3 : ℕ) = 2 + 1 from rfl, pow_add, hgc2, pow_one,
          (hzcentral gc).eq]
      rw [hfgc3]
      have hstep : gc * z * (fg1 a * fg2 b) * (gc * z)⁻¹
          = (gc * fg1 a * gc⁻¹) * (gc * fg2 b * gc⁻¹) := by
        rw [mul_inv_rev]
        have hmid : z * (fg1 a * fg2 b) * z⁻¹ = fg1 a * fg2 b := by
          rw [(hzcentral (fg1 a * fg2 b)).eq]; group
        calc gc * z * (fg1 a * fg2 b) * (z⁻¹ * gc⁻¹)
            = gc * (z * (fg1 a * fg2 b) * z⁻¹) * gc⁻¹ := by group
          _ = gc * (fg1 a * fg2 b) * gc⁻¹ := by rw [hmid]
          _ = (gc * fg1 a * gc⁻¹) * (gc * fg2 b * gc⁻¹) := by group
      rw [hstep, hconjga a, hconjgb b]
  set s : order32_k8c4_psi3 →* G := SemidirectProduct.lift fn fg hcomp with hsdef
  have hs_inl : ∀ p : K8g, s (SemidirectProduct.inl p) = fn p := by
    intro p; rw [hsdef]; exact SemidirectProduct.lift_inl fn fg hcomp p
  have hs_inr : ∀ t : Multiplicative (ZMod 4), s (SemidirectProduct.inr t) = fg t := by
    intro t; rw [hsdef]; exact SemidirectProduct.lift_inr fn fg hcomp t
  have hρcompat : ∀ t : Multiplicative (ZMod 4),
      (MonoidHom.id K8g).comp (psi3Act4 t).toMonoidHom
        = (c2Action_psi3 (redHom42g8 t)).toMonoidHom.comp (MonoidHom.id K8g) := by
    intro t; rfl
  set ρ : order32_k8c4_psi3 →* order16_wild_G8 :=
    SemidirectProduct.map (MonoidHom.id K8g) redHom42g8 hρcompat with hρdef
  have hρ_inl : ∀ p : K8g, ρ (SemidirectProduct.inl p) = SemidirectProduct.inl p := by
    intro p; rw [hρdef]; simp
  have hρ_inr : ∀ t : Multiplicative (ZMod 4),
      ρ (SemidirectProduct.inr t) = SemidirectProduct.inr (redHom42g8 t) := by
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
  have hπs : ∀ q : order32_k8c4_psi3,
      (QuotientGroup.mk' (Subgroup.zpowers z)) (s q) = e.symm (ρ q) := by
    have hgen : (QuotientGroup.mk' (Subgroup.zpowers z)).comp s = e.symm.toMonoidHom.comp ρ := by
      apply SemidirectProduct.hom_ext
      · apply monoidHom_ext_prod_ofAdd_one
        · change (QuotientGroup.mk' (Subgroup.zpowers z)) (s (SemidirectProduct.inl (xK8 : K8g)))
              = e.symm (ρ (SemidirectProduct.inl (xK8 : K8g)))
          rw [hs_inl, hρ_inl]
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
              = e.symm (ρ (SemidirectProduct.inl (yK8 : K8g)))
          rw [hs_inl, hρ_inl]
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
        simp only [MonoidHom.comp_apply, hs_inr, hfg_val, MulEquiv.coe_toMonoidHom, hρ_inr]
        rw [show (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 4))).val = 1 from by
          decide, pow_one]
        rw [show redHom42g8 (Multiplicative.ofAdd (1 : ZMod 4)) = Multiplicative.ofAdd (1 : ZMod 2)
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
    have hcomp2 : q.left = 1 ∧ redHom42g8 q.right = 1 := by
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
  exact central_ext_full_iso hG card_order32_k8c4_psi3 s hs_inj

/-! ## `x`-doubled branch: `order16_wild_G8` descendants (continued)

The "`x` doubles" case: `x⁴ = z` (so `x` lifts to order `8`), `y² = 1` and `c² = 1`
(both untouched), and both conjugation relations hold exactly (`cxc⁻¹ = x⁻¹`,
`cyc⁻¹ = y`). Since the ACTING generator `c` is not doubled, this is a normal-side
doubling (same shape as `G4`'s `a`-doubled branch): the true normal factor becomes
`⟨x,y⟩ ≅ C₈ × C₂` (still a direct product, since `x,y` commute exactly), with `c` acting
by inverting the `C₈` factor and fixing the `C₂` factor — `ψ₃` lifted to `C₈ × C₂`. This
produces a new order-32 group `(C₈ × C₂) ⋊[ψ₃'] C₂`. -/

/-- The order-16 normal factor `⟨x,y⟩ ≅ C₈ × C₂` for the `x`-doubled branch. -/
private abbrev C8C2gK8x : Type := Multiplicative (ZMod 8) × Multiplicative (ZMod 2)

/-- `ψ₃` lifted to `C₈ × C₂`: `(p,q) ↦ (p⁻¹,q)`. -/
private noncomputable def psi3Big : C8C2gK8x ≃* C8C2gK8x where
  toFun p := (p.1⁻¹, p.2)
  invFun p := (p.1⁻¹, p.2)
  left_inv p := by rcases p with ⟨x, y⟩; simp
  right_inv p := by rcases p with ⟨x, y⟩; simp
  map_mul' p q := by
    rcases p with ⟨x₁, y₁⟩
    rcases q with ⟨x₂, y₂⟩
    simp [mul_inv_rev, mul_comm]

@[simp] private theorem psi3Big_sq : psi3Big ^ 2 = 1 := by
  apply MulEquiv.ext
  intro p
  rcases p with ⟨x, y⟩
  calc
    (psi3Big ^ 2) (x, y) = psi3Big (psi3Big (x, y)) := rfl
    _ = psi3Big (x⁻¹, y) := rfl
    _ = ((x⁻¹)⁻¹, y) := rfl
    _ = (x, y) := by simp

private lemma c2_two_cases_x3 (a : Multiplicative (ZMod 2)) :
    a = 1 ∨ a = Multiplicative.ofAdd 1 := by
  have := show ∀ a : Multiplicative (ZMod 2), a = 1 ∨ a = Multiplicative.ofAdd 1 from by decide
  exact this a

@[simp] private lemma c2_mul_self_x3 : (Multiplicative.ofAdd (1 : ZMod 2)
    * Multiplicative.ofAdd (1 : ZMod 2) : Multiplicative (ZMod 2)) = 1 := by decide

set_option linter.flexible false in
/-- The `C₂`-action on `C₈ × C₂` given by `psi3Big`. -/
private noncomputable def c8c2K8x_psi3 : Multiplicative (ZMod 2) →* MulAut C8C2gK8x where
  toFun g := if g = 1 then 1 else psi3Big
  map_one' := by simp
  map_mul' a b := by
    rcases c2_two_cases_x3 a with (rfl|rfl) <;> rcases c2_two_cases_x3 b with (rfl|rfl) <;>
      simp; try rw [← sq, psi3Big_sq]

/-- The new order-32 group `(C₈ × C₂) ⋊[ψ₃'] C₂` (the `x`-doubled descendant of `G8`). -/
noncomputable abbrev order32_k8xdbl_psi3 : Type :=
  SemidirectProduct C8C2gK8x (Multiplicative (ZMod 2)) c8c2K8x_psi3

@[simp] theorem card_order32_k8xdbl_psi3 : Nat.card order32_k8xdbl_psi3 = 32 := by
  rw [SemidirectProduct.card]; simp

/-- Reduction homomorphism `C₈ ↠ C₄` (mod-4 cast on `ZMod 8`), used to collapse the
doubled normal factor `C₈ × C₂` back down to `K₈ = C₄ × C₂`. -/
private noncomputable def redHom84g8x : Multiplicative (ZMod 8) →* Multiplicative (ZMod 4) :=
  AddMonoidHom.toMultiplicative (ZMod.castHom (by norm_num : (4 : ℕ) ∣ 8) (ZMod 4)).toAddMonoidHom

/-- The combined reduction `C₈ × C₂ ↠ K₈` (mod-4 on the first factor, identity on the
second). -/
private noncomputable def redHomK8x : C8C2gK8x →* K8g :=
  redHom84g8x.prodMap (MonoidHom.id (Multiplicative (ZMod 2)))

/-- The `x`-doubled branch over `order16_wild_G8`: `x⁴=z`, `y²=1`, `c²=1`, and both
conjugation relations hold exactly. `G` is isomorphic to `(C₈ × C₂) ⋊[ψ₃'] C₂`. -/
theorem order32_of_k8c2_d8xc2_quotient_doubled_x_case {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 32) {z : G} (_hzc : z ∈ Subgroup.center G) (hzp : orderOf z = 2)
    [hnorm : (Subgroup.zpowers z).Normal]
    (e : (G ⧸ Subgroup.zpowers z) ≃* order16_wild_G8)
    {ga gb gc : G}
    (hga : (QuotientGroup.mk' (Subgroup.zpowers z)) ga
      = e.symm (SemidirectProduct.inl (xK8 : K8g)))
    (hgb : (QuotientGroup.mk' (Subgroup.zpowers z)) gb
      = e.symm (SemidirectProduct.inl (yK8 : K8g)))
    (hgc : (QuotientGroup.mk' (Subgroup.zpowers z)) gc
      = e.symm (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))))
    (hga4 : ga ^ 4 = z) (hgb2 : gb ^ 2 = 1) (hgc2 : gc ^ 2 = 1) (hcommab : Commute ga gb)
    (hrelgca : gc * ga * gc⁻¹ = ga⁻¹) (hcommgcb : Commute gc gb) :
    Nonempty (G ≃* order32_k8xdbl_psi3) := by
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
  set fn : C8C2gK8x →* G := fga.noncommCoprod fgb hcomm' with hfndef
  have hfn_apply : ∀ p : C8C2gK8x, fn p = fga p.1 * fgb p.2 := by
    intro p; rw [hfndef]; exact MonoidHom.noncommCoprod_apply fga fgb hcomm' p
  set fg : Multiplicative (ZMod 2) →* G := zmodZPowHom 2 gc hgc2 with hfgdef
  have hconjpow : ∀ k : ℕ, gc * ga ^ k * gc⁻¹ = (gc * ga * gc⁻¹) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
      have hstep : gc * ga ^ (n + 1) * gc⁻¹ = (gc * ga ^ n * gc⁻¹) * (gc * ga * gc⁻¹) := by
        rw [pow_succ]; group
      rw [hstep, ih, ← pow_succ]
  have hconjga : ∀ a : Multiplicative (ZMod 8), gc * fga a * gc⁻¹ = (fga a)⁻¹ := by
    intro a
    rw [hfga_val, hconjpow, hrelgca, inv_pow]
  have hconjgb : ∀ b : Multiplicative (ZMod 2), gc * fgb b * gc⁻¹ = fgb b := by
    intro b
    rw [hfgb_val]
    have hcommpow : gc * gb ^ (Multiplicative.toAdd b).val
        = gb ^ (Multiplicative.toAdd b).val * gc := hcommgcb.pow_right _
    rw [hcommpow, mul_inv_cancel_right]
  have hc2cases : ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = Multiplicative.ofAdd (1 : ZMod 2) :=
    by decide
  have hphi1 : ∀ p : C8C2gK8x, c8c2K8x_psi3 (1 : Multiplicative (ZMod 2)) p = p := by decide
  have hpsi : ∀ p : C8C2gK8x, c8c2K8x_psi3 (Multiplicative.ofAdd (1 : ZMod 2)) p
      = (p.1⁻¹, p.2) := by decide
  have hcomp : ∀ t : Multiplicative (ZMod 2),
      fn.comp (c8c2K8x_psi3 t).toMonoidHom = (MulAut.conj (fg t)).toMonoidHom.comp fn := by
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
      have hfna : fn (a⁻¹, b) = (fga a)⁻¹ * fgb b := by
        rw [hfndef, MonoidHom.noncommCoprod_apply, map_inv]
      have hfnab : fn (a, b) = fga a * fgb b := by rw [hfndef, MonoidHom.noncommCoprod_apply]
      rw [hfgc, hfna, hfnab]
      rw [show gc * (fga a * fgb b) * gc⁻¹ = (gc * fga a * gc⁻¹) * (gc * fgb b * gc⁻¹) from by
        group]
      rw [hconjga a, hconjgb b]
  set s : order32_k8xdbl_psi3 →* G := SemidirectProduct.lift fn fg hcomp with hsdef
  have hs_inl : ∀ p : C8C2gK8x, s (SemidirectProduct.inl p) = fn p := by
    intro p; rw [hsdef]; exact SemidirectProduct.lift_inl fn fg hcomp p
  have hs_inr : ∀ t : Multiplicative (ZMod 2), s (SemidirectProduct.inr t) = fg t := by
    intro t; rw [hsdef]; exact SemidirectProduct.lift_inr fn fg hcomp t
  have hρcompat : ∀ t : Multiplicative (ZMod 2),
      redHomK8x.comp (c8c2K8x_psi3 t).toMonoidHom
        = (c2Action_psi3 t).toMonoidHom.comp redHomK8x := by
    intro t
    apply monoidHom_ext_prod_ofAdd_one
    · rcases hc2cases t with rfl | rfl
      · decide
      · decide
    · rcases hc2cases t with rfl | rfl
      · decide
      · decide
  set ρ : order32_k8xdbl_psi3 →* order16_wild_G8 :=
    SemidirectProduct.map redHomK8x (MonoidHom.id (Multiplicative (ZMod 2))) hρcompat with hρdef
  have hρ_inl : ∀ p : C8C2gK8x,
      ρ (SemidirectProduct.inl p) = SemidirectProduct.inl (redHomK8x p) := by
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
  have hredgen1 : redHomK8x (Multiplicative.ofAdd (1 : ZMod 8), (1 : Multiplicative (ZMod 2)))
      = (xK8 : K8g) := by decide
  have hredgen2 : redHomK8x ((1 : Multiplicative (ZMod 8)), Multiplicative.ofAdd (1 : ZMod 2))
      = (yK8 : K8g) := by decide
  have hπs : ∀ q : order32_k8xdbl_psi3,
      (QuotientGroup.mk' (Subgroup.zpowers z)) (s q) = e.symm (ρ q) := by
    have hgen : (QuotientGroup.mk' (Subgroup.zpowers z)).comp s = e.symm.toMonoidHom.comp ρ := by
      apply SemidirectProduct.hom_ext
      · apply monoidHom_ext_prod_ofAdd_one
        · change (QuotientGroup.mk' (Subgroup.zpowers z)) (s (SemidirectProduct.inl
              (Multiplicative.ofAdd (1 : ZMod 8), (1 : Multiplicative (ZMod 2)))))
              = e.symm (ρ (SemidirectProduct.inl
              (Multiplicative.ofAdd (1 : ZMod 8), (1 : Multiplicative (ZMod 2)))))
          rw [hs_inl, hρ_inl, hredgen1]
          change (QuotientGroup.mk' (Subgroup.zpowers z))
              (fga (Multiplicative.ofAdd (1 : ZMod 8)) * fgb 1) = _
          rw [fgb.map_one, mul_one]
          have hfgag : fga (Multiplicative.ofAdd (1 : ZMod 8)) = ga := by
            rw [hfgadef]
            have h := zmodZPowHom_intCast 8 ga hga8 1
            simp only [Int.cast_one, zpow_one] at h
            exact h
          rw [hfgag, hπga]
        · change (QuotientGroup.mk' (Subgroup.zpowers z)) (s (SemidirectProduct.inl
              ((1 : Multiplicative (ZMod 8)), Multiplicative.ofAdd (1 : ZMod 2))))
              = e.symm (ρ (SemidirectProduct.inl
              ((1 : Multiplicative (ZMod 8)), Multiplicative.ofAdd (1 : ZMod 2))))
          rw [hs_inl, hρ_inl, hredgen2]
          change (QuotientGroup.mk' (Subgroup.zpowers z))
              (fga 1 * fgb (Multiplicative.ofAdd (1 : ZMod 2))) = _
          rw [fga.map_one, one_mul]
          have hfgbg : fgb (Multiplicative.ofAdd (1 : ZMod 2)) = gb := by
            rw [hfgbdef]
            have h := zmodZPowHom_intCast 2 gb hgb2 1
            simp only [Int.cast_one, zpow_one] at h
            exact h
          rw [hfgbg, hπgb]
      · apply MonoidHom.ext; intro t
        rw [zmod_pow_eq_ofAdd_one_pow t, map_pow, map_pow]
        simp only [MonoidHom.comp_apply, hs_inr, hfgdef, MulEquiv.coe_toMonoidHom, hρ_inr]
        have hb : (zmodZPowHom 2 gc hgc2) (Multiplicative.ofAdd (1 : ZMod 2)) = gc := by
          have h := zmodZPowHom_intCast 2 gc hgc2 1
          simp only [Int.cast_one, zpow_one] at h
          exact h
        rw [hb, hπgc]
    intro q
    have := DFunLike.congr_fun hgen q
    simpa using this
  have hs_inj : Function.Injective s := by
    refine (injective_iff_map_eq_one _).mpr ?_
    intro q hq
    have hρq1 : e.symm (ρ q) = 1 := by rw [← hπs q, hq, map_one]
    have hρq : ρ q = 1 := e.symm.injective (by rw [hρq1, map_one])
    have hcomp2 : redHomK8x q.left = 1 ∧ q.right = 1 := by
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
    have hc8cases4 : ∀ x : Multiplicative (ZMod 8), redHom84g8x x = 1 →
        x = 1 ∨ x = Multiplicative.ofAdd (4 : ZMod 8) := by decide
    have hleft2 : q.left.2 = 1 := by
      have := congrArg Prod.snd hcomp2.1
      simpa [redHomK8x] using this
    have hleft1cases : redHom84g8x q.left.1 = 1 := by
      have := congrArg Prod.fst hcomp2.1
      simpa [redHomK8x] using this
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
  exact central_ext_full_iso hG card_order32_k8xdbl_psi3 s hs_inj

/-! ## `y`-doubled branch: `order16_wild_G8` descendants (continued)

The "`y` doubles" case: `x⁴ = 1` (untouched), `y² = z` (so `y` lifts to order `4`),
`c² = 1` (untouched), and both conjugation relations hold exactly (`cxc⁻¹ = x⁻¹`,
`cyc⁻¹ = y`). Since `c` FIXES `y` exactly under `ψ₃` (no shift/embedding of `y` is ever
needed), doubling `y`'s order causes NO obstruction: the lifted action still just
inverts the `x`-factor and fixes the (now order-`4`) `y`-factor. The true normal factor
becomes `⟨x,y⟩ ≅ C₄ × C₄`, giving a new order-32 group `(C₄ × C₄) ⋊[ψ₃''] C₂`. -/

/-- The order-16 normal factor `⟨x,y⟩ ≅ C₄ × C₄` for the `y`-doubled branch. -/
private abbrev C4C4gK8y : Type := Multiplicative (ZMod 4) × Multiplicative (ZMod 4)

/-- `ψ₃` lifted to `C₄ × C₄`: `(p,q) ↦ (p⁻¹,q)`. -/
private noncomputable def psi3Small : C4C4gK8y ≃* C4C4gK8y where
  toFun p := (p.1⁻¹, p.2)
  invFun p := (p.1⁻¹, p.2)
  left_inv p := by rcases p with ⟨x, y⟩; simp
  right_inv p := by rcases p with ⟨x, y⟩; simp
  map_mul' p q := by
    rcases p with ⟨x₁, y₁⟩
    rcases q with ⟨x₂, y₂⟩
    simp [mul_inv_rev, mul_comm]

@[simp] private theorem psi3Small_sq : psi3Small ^ 2 = 1 := by
  apply MulEquiv.ext
  intro p
  rcases p with ⟨x, y⟩
  calc
    (psi3Small ^ 2) (x, y) = psi3Small (psi3Small (x, y)) := rfl
    _ = psi3Small (x⁻¹, y) := rfl
    _ = ((x⁻¹)⁻¹, y) := rfl
    _ = (x, y) := by simp

private lemma c2_two_cases_y3 (a : Multiplicative (ZMod 2)) :
    a = 1 ∨ a = Multiplicative.ofAdd 1 := by
  have := show ∀ a : Multiplicative (ZMod 2), a = 1 ∨ a = Multiplicative.ofAdd 1 from by decide
  exact this a

@[simp] private lemma c2_mul_self_y3 : (Multiplicative.ofAdd (1 : ZMod 2)
    * Multiplicative.ofAdd (1 : ZMod 2) : Multiplicative (ZMod 2)) = 1 := by decide

set_option linter.flexible false in
/-- The `C₂`-action on `C₄ × C₄` given by `psi3Small`. -/
private noncomputable def c4c4K8y_psi3 : Multiplicative (ZMod 2) →* MulAut C4C4gK8y where
  toFun g := if g = 1 then 1 else psi3Small
  map_one' := by simp
  map_mul' a b := by
    rcases c2_two_cases_y3 a with (rfl|rfl) <;> rcases c2_two_cases_y3 b with (rfl|rfl) <;>
      simp; try rw [← sq, psi3Small_sq]

/-- The new order-32 group `(C₄ × C₄) ⋊[ψ₃''] C₂` (the `y`-doubled descendant of `G8`). -/
noncomputable abbrev order32_k8ydbl_psi3 : Type :=
  SemidirectProduct C4C4gK8y (Multiplicative (ZMod 2)) c4c4K8y_psi3

@[simp] theorem card_order32_k8ydbl_psi3 : Nat.card order32_k8ydbl_psi3 = 32 := by
  rw [SemidirectProduct.card]; simp

/-- Reduction homomorphism `C₄ ↠ C₂` (mod-2 cast), used to collapse the doubled `y`
factor back down to `C₂`. -/
private noncomputable def redHom42g8y : Multiplicative (ZMod 4) →* Multiplicative (ZMod 2) :=
  AddMonoidHom.toMultiplicative (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)).toAddMonoidHom

/-- The combined reduction `C₄ × C₄ ↠ K₈` (identity on the first factor, mod-2 on the
second). -/
private noncomputable def redHomK8y3 : C4C4gK8y →* K8g :=
  (MonoidHom.id (Multiplicative (ZMod 4))).prodMap redHom42g8y

/-- The `y`-doubled branch over `order16_wild_G8`: `x⁴=1`, `y²=z`, `c²=1`, and both
conjugation relations hold exactly. `G` is isomorphic to `(C₄ × C₄) ⋊[ψ₃''] C₂`. -/
theorem order32_of_k8c2_d8xc2_quotient_doubled_y_case {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 32) {z : G} (_hzc : z ∈ Subgroup.center G) (hzp : orderOf z = 2)
    [hnorm : (Subgroup.zpowers z).Normal]
    (e : (G ⧸ Subgroup.zpowers z) ≃* order16_wild_G8)
    {ga gb gc : G}
    (hga : (QuotientGroup.mk' (Subgroup.zpowers z)) ga
      = e.symm (SemidirectProduct.inl (xK8 : K8g)))
    (hgb : (QuotientGroup.mk' (Subgroup.zpowers z)) gb
      = e.symm (SemidirectProduct.inl (yK8 : K8g)))
    (hgc : (QuotientGroup.mk' (Subgroup.zpowers z)) gc
      = e.symm (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))))
    (hga4 : ga ^ 4 = 1) (hgb2 : gb ^ 2 = z) (hgc2 : gc ^ 2 = 1) (hcommab : Commute ga gb)
    (hrelgca : gc * ga * gc⁻¹ = ga⁻¹) (hcommgcb : Commute gc gb) :
    Nonempty (G ≃* order32_k8ydbl_psi3) := by
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
  set fn : C4C4gK8y →* G := fga.noncommCoprod fgb hcomm' with hfndef
  have hfn_apply : ∀ p : C4C4gK8y, fn p = fga p.1 * fgb p.2 := by
    intro p; rw [hfndef]; exact MonoidHom.noncommCoprod_apply fga fgb hcomm' p
  set fg : Multiplicative (ZMod 2) →* G := zmodZPowHom 2 gc hgc2 with hfgdef
  have hconjpow : ∀ k : ℕ, gc * ga ^ k * gc⁻¹ = (gc * ga * gc⁻¹) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
      have hstep : gc * ga ^ (n + 1) * gc⁻¹ = (gc * ga ^ n * gc⁻¹) * (gc * ga * gc⁻¹) := by
        rw [pow_succ]; group
      rw [hstep, ih, ← pow_succ]
  have hconjga : ∀ a : Multiplicative (ZMod 4), gc * fga a * gc⁻¹ = (fga a)⁻¹ := by
    intro a
    rw [hfga_val, hconjpow, hrelgca, inv_pow]
  have hconjgb : ∀ b : Multiplicative (ZMod 4), gc * fgb b * gc⁻¹ = fgb b := by
    intro b
    rw [hfgb_val]
    have hcommpow : gc * gb ^ (Multiplicative.toAdd b).val
        = gb ^ (Multiplicative.toAdd b).val * gc := hcommgcb.pow_right _
    rw [hcommpow, mul_inv_cancel_right]
  have hc2cases : ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = Multiplicative.ofAdd (1 : ZMod 2) :=
    by decide
  have hphi1 : ∀ p : C4C4gK8y, c4c4K8y_psi3 (1 : Multiplicative (ZMod 2)) p = p := by decide
  have hpsi : ∀ p : C4C4gK8y, c4c4K8y_psi3 (Multiplicative.ofAdd (1 : ZMod 2)) p
      = (p.1⁻¹, p.2) := by decide
  have hcomp : ∀ t : Multiplicative (ZMod 2),
      fn.comp (c4c4K8y_psi3 t).toMonoidHom = (MulAut.conj (fg t)).toMonoidHom.comp fn := by
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
      have hfna : fn (a⁻¹, b) = (fga a)⁻¹ * fgb b := by
        rw [hfndef, MonoidHom.noncommCoprod_apply, map_inv]
      have hfnab : fn (a, b) = fga a * fgb b := by rw [hfndef, MonoidHom.noncommCoprod_apply]
      rw [hfgc, hfna, hfnab]
      rw [show gc * (fga a * fgb b) * gc⁻¹ = (gc * fga a * gc⁻¹) * (gc * fgb b * gc⁻¹) from by
        group]
      rw [hconjga a, hconjgb b]
  set s : order32_k8ydbl_psi3 →* G := SemidirectProduct.lift fn fg hcomp with hsdef
  have hs_inl : ∀ p : C4C4gK8y, s (SemidirectProduct.inl p) = fn p := by
    intro p; rw [hsdef]; exact SemidirectProduct.lift_inl fn fg hcomp p
  have hs_inr : ∀ t : Multiplicative (ZMod 2), s (SemidirectProduct.inr t) = fg t := by
    intro t; rw [hsdef]; exact SemidirectProduct.lift_inr fn fg hcomp t
  have hρcompat : ∀ t : Multiplicative (ZMod 2),
      redHomK8y3.comp (c4c4K8y_psi3 t).toMonoidHom
        = (c2Action_psi3 t).toMonoidHom.comp redHomK8y3 := by
    intro t
    apply monoidHom_ext_prod_ofAdd_one
    · rcases hc2cases t with rfl | rfl
      · decide
      · decide
    · rcases hc2cases t with rfl | rfl
      · decide
      · decide
  set ρ : order32_k8ydbl_psi3 →* order16_wild_G8 :=
    SemidirectProduct.map redHomK8y3 (MonoidHom.id (Multiplicative (ZMod 2))) hρcompat with hρdef
  have hρ_inl : ∀ p : C4C4gK8y,
      ρ (SemidirectProduct.inl p) = SemidirectProduct.inl (redHomK8y3 p) := by
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
  have hredgen1 : redHomK8y3 (Multiplicative.ofAdd (1 : ZMod 4), (1 : Multiplicative (ZMod 4)))
      = (xK8 : K8g) := by decide
  have hredgen2 : redHomK8y3 ((1 : Multiplicative (ZMod 4)), Multiplicative.ofAdd (1 : ZMod 4))
      = (yK8 : K8g) := by decide
  have hπs : ∀ q : order32_k8ydbl_psi3,
      (QuotientGroup.mk' (Subgroup.zpowers z)) (s q) = e.symm (ρ q) := by
    have hgen : (QuotientGroup.mk' (Subgroup.zpowers z)).comp s = e.symm.toMonoidHom.comp ρ := by
      apply SemidirectProduct.hom_ext
      · apply monoidHom_ext_prod_ofAdd_one
        · change (QuotientGroup.mk' (Subgroup.zpowers z)) (s (SemidirectProduct.inl
              (Multiplicative.ofAdd (1 : ZMod 4), (1 : Multiplicative (ZMod 4)))))
              = e.symm (ρ (SemidirectProduct.inl
              (Multiplicative.ofAdd (1 : ZMod 4), (1 : Multiplicative (ZMod 4)))))
          rw [hs_inl, hρ_inl, hredgen1]
          change (QuotientGroup.mk' (Subgroup.zpowers z))
              (fga (Multiplicative.ofAdd (1 : ZMod 4)) * fgb 1) = _
          rw [fgb.map_one, mul_one]
          have hfgag : fga (Multiplicative.ofAdd (1 : ZMod 4)) = ga := by
            rw [hfgadef]
            have h := zmodZPowHom_intCast 4 ga hga4 1
            simp only [Int.cast_one, zpow_one] at h
            exact h
          rw [hfgag, hπga]
        · change (QuotientGroup.mk' (Subgroup.zpowers z)) (s (SemidirectProduct.inl
              ((1 : Multiplicative (ZMod 4)), Multiplicative.ofAdd (1 : ZMod 4))))
              = e.symm (ρ (SemidirectProduct.inl
              ((1 : Multiplicative (ZMod 4)), Multiplicative.ofAdd (1 : ZMod 4))))
          rw [hs_inl, hρ_inl, hredgen2]
          change (QuotientGroup.mk' (Subgroup.zpowers z))
              (fga 1 * fgb (Multiplicative.ofAdd (1 : ZMod 4))) = _
          rw [fga.map_one, one_mul]
          have hfgbg : fgb (Multiplicative.ofAdd (1 : ZMod 4)) = gb := by
            rw [hfgbdef]
            have h := zmodZPowHom_intCast 4 gb hgb4 1
            simp only [Int.cast_one, zpow_one] at h
            exact h
          rw [hfgbg, hπgb]
      · apply MonoidHom.ext; intro t
        rw [zmod_pow_eq_ofAdd_one_pow t, map_pow, map_pow]
        simp only [MonoidHom.comp_apply, hs_inr, hfgdef, MulEquiv.coe_toMonoidHom, hρ_inr]
        have hb : (zmodZPowHom 2 gc hgc2) (Multiplicative.ofAdd (1 : ZMod 2)) = gc := by
          have h := zmodZPowHom_intCast 2 gc hgc2 1
          simp only [Int.cast_one, zpow_one] at h
          exact h
        rw [hb, hπgc]
    intro q
    have := DFunLike.congr_fun hgen q
    simpa using this
  have hs_inj : Function.Injective s := by
    refine (injective_iff_map_eq_one _).mpr ?_
    intro q hq
    have hρq1 : e.symm (ρ q) = 1 := by rw [← hπs q, hq, map_one]
    have hρq : ρ q = 1 := e.symm.injective (by rw [hρq1, map_one])
    have hcomp2 : redHomK8y3 q.left = 1 ∧ q.right = 1 := by
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
    have hc4cases2 : ∀ x : Multiplicative (ZMod 4), redHom42g8y x = 1 →
        x = 1 ∨ x = Multiplicative.ofAdd (2 : ZMod 4) := by decide
    have hleft1 : q.left.1 = 1 := by
      have := congrArg Prod.fst hcomp2.1
      simpa [redHomK8y3] using this
    have hleft2cases : redHom42g8y q.left.2 = 1 := by
      have := congrArg Prod.snd hcomp2.1
      simpa [redHomK8y3] using this
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
  exact central_ext_full_iso hG card_order32_k8ydbl_psi3 s hs_inj

end Smallgroups.UsefulTheorems
