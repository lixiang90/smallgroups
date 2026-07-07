/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order16_Wild
import Smallgroups.UsefulTheorems.PGroupGeneration
import Smallgroups.UsefulTheorems.Order32.Common

/-! ## Descendants of `order16_wild_G0` (`(C₂)⁴`), abelian-lift case

`order16_wild_G0 = order16_A5 ≃* order16_wild_C2pow4` (elementary abelian rank `4`), with
four independent order-`2` generators `a, b, c, d`.  With commuting lifts, the sixteen
choices of `(ga², gb², gc², gd²)` collapse to just **two** isomorphism types: `C2 × C2 × C2
× C2 × C2` (all trivial) and `C4 × C2 × C2 × C2` (any other combination — whichever
generator is nontrivial absorbs `z` and doubles to order `4`; every other nontrivial
generator merges with it via the matching-period substitution `x * anchor`). -/

namespace Smallgroups.UsefulTheorems

/-- Shared reduction: given an "anchor" `ga` with `ga ^ 2 = z` (so `orderOf ga = 4`) and
three other pairwise-commuting order-`2`-or-`z` elements `gb, gc, gd`, each separated by a
dedicated projection `ψb, ψc, ψd` (killed by `ga` and by each other), `G ≃* C4 × C2 × C2 ×
C2` — whichever of `gb, gc, gd` squares to `z` merges into a fresh order-`2` element via
`x * ga` (the projections are unaffected by this merge, since each kills `ga`). -/
private theorem quad_c2_anchor_reduce {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 32)
    {z ga gb gc gd : G} (hz2 : z ^ 2 = 1) (hzne1 : z ≠ 1)
    (hcab : Commute ga gb) (hcac : Commute ga gc) (hcad : Commute ga gd)
    (hcbc : Commute gb gc) (hcbd : Commute gb gd) (hccd : Commute gc gd)
    (hga2 : ga ^ 2 = z) (hordga2 : (2 : ℕ) ∣ orderOf ga)
    (hgb2 : gb ^ 2 = 1 ∨ gb ^ 2 = z) (hgc2 : gc ^ 2 = 1 ∨ gc ^ 2 = z)
    (hgd2 : gd ^ 2 = 1 ∨ gd ^ 2 = z)
    {K : Type*} [Group K] (ψb ψc ψd : G →* K)
    (hψbgb : orderOf (ψb gb) = 2) (hψbgc : ψb gc = 1) (hψbgd : ψb gd = 1)
    (hψbga : ψb ga = 1)
    (hψcgc : orderOf (ψc gc) = 2) (hψcgb : ψc gb = 1) (hψcgd : ψc gd = 1)
    (hψcga : ψc ga = 1)
    (hψdgd : orderOf (ψd gd) = 2) (hψdgb : ψd gb = 1) (hψdgc : ψd gc = 1)
    (hψdga : ψd ga = 1) :
    Nonempty (G ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 2)
      × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
  classical
  have hordga : orderOf ga = 4 :=
    order_double_of_pow_eq_central (by norm_num) hordga2 hga2 hzne1 hz2
  set gb' := if gb ^ 2 = z then gb * ga else gb with hgb'def
  set gc' := if gc ^ 2 = z then gc * ga else gc with hgc'def
  set gd' := if gd ^ 2 = z then gd * ga else gd with hgd'def
  have hgb'sq : gb' ^ 2 = 1 := by
    rw [hgb'def]; split_ifs with h
    · exact sym_merge_sq_one hcab.symm h hga2 hz2
    · exact hgb2.resolve_right h
  have hgc'sq : gc' ^ 2 = 1 := by
    rw [hgc'def]; split_ifs with h
    · exact sym_merge_sq_one hcac.symm h hga2 hz2
    · exact hgc2.resolve_right h
  have hgd'sq : gd' ^ 2 = 1 := by
    rw [hgd'def]; split_ifs with h
    · exact sym_merge_sq_one hcad.symm h hga2 hz2
    · exact hgd2.resolve_right h
  have hcommgb' : Commute ga gb' := by
    rw [hgb'def]; split_ifs
    · exact hcab.mul_right (Commute.refl ga)
    · exact hcab
  have hcommgc' : Commute ga gc' := by
    rw [hgc'def]; split_ifs
    · exact hcac.mul_right (Commute.refl ga)
    · exact hcac
  have hcommgd' : Commute ga gd' := by
    rw [hgd'def]; split_ifs
    · exact hcad.mul_right (Commute.refl ga)
    · exact hcad
  have hcommb'c' : Commute gb' gc' := by
    rw [hgb'def, hgc'def]; split_ifs
    · exact (hcbc.mul_right hcab.symm).mul_left (hcac.mul_right (Commute.refl ga))
    · exact hcbc.mul_left hcac
    · exact hcbc.mul_right hcab.symm
    · exact hcbc
  have hcommb'd' : Commute gb' gd' := by
    rw [hgb'def, hgd'def]; split_ifs
    · exact (hcbd.mul_right hcab.symm).mul_left (hcad.mul_right (Commute.refl ga))
    · exact hcbd.mul_left hcad
    · exact hcbd.mul_right hcab.symm
    · exact hcbd
  have hcommc'd' : Commute gc' gd' := by
    rw [hgc'def, hgd'def]; split_ifs
    · exact (hccd.mul_right hcac.symm).mul_left (hcad.mul_right (Commute.refl ga))
    · exact hccd.mul_left hcad
    · exact hccd.mul_right hcac.symm
    · exact hccd
  have hψbgb' : orderOf (ψb gb') = 2 := by
    rw [hgb'def]; split_ifs
    · rw [map_mul, hψbga, mul_one]; exact hψbgb
    · exact hψbgb
  have hψcgb' : ψc gb' = 1 := by
    rw [hgb'def]; split_ifs
    · rw [map_mul, hψcga, mul_one]; exact hψcgb
    · exact hψcgb
  have hψdgb' : ψd gb' = 1 := by
    rw [hgb'def]; split_ifs
    · rw [map_mul, hψdga, mul_one]; exact hψdgb
    · exact hψdgb
  have hψbgc' : ψb gc' = 1 := by
    rw [hgc'def]; split_ifs
    · rw [map_mul, hψbga, mul_one]; exact hψbgc
    · exact hψbgc
  have hψcgc' : orderOf (ψc gc') = 2 := by
    rw [hgc'def]; split_ifs
    · rw [map_mul, hψcga, mul_one]; exact hψcgc
    · exact hψcgc
  have hψdgc' : ψd gc' = 1 := by
    rw [hgc'def]; split_ifs
    · rw [map_mul, hψdga, mul_one]; exact hψdgc
    · exact hψdgc
  have hψbgd' : ψb gd' = 1 := by
    rw [hgd'def]; split_ifs
    · rw [map_mul, hψbga, mul_one]; exact hψbgd
    · exact hψbgd
  have hψcgd' : ψc gd' = 1 := by
    rw [hgd'def]; split_ifs
    · rw [map_mul, hψcga, mul_one]; exact hψcgd
    · exact hψcgd
  have hψdgd' : orderOf (ψd gd') = 2 := by
    rw [hgd'def]; split_ifs
    · rw [map_mul, hψdga, mul_one]; exact hψdgd
    · exact hψdgd
  have hindep : ∀ i j u v : ℕ, i < 4 → j < 2 → u < 2 → v < 2 →
      ga ^ i * gb' ^ j * gc' ^ u * gd' ^ v = 1 → i = 0 ∧ j = 0 ∧ u = 0 ∧ v = 0 := by
    intro i j u v hilt hjlt hult hvlt hijuv
    have h1 : ψb (ga ^ i * gb' ^ j * gc' ^ u * gd' ^ v) = 1 := by rw [hijuv]; exact map_one ψb
    simp only [map_mul, map_pow, hψbga, hψbgc', hψbgd', one_pow, one_mul, mul_one] at h1
    have hj0 : j = 0 := Nat.eq_zero_of_dvd_of_lt (hψbgb' ▸ orderOf_dvd_of_pow_eq_one h1) hjlt
    subst hj0
    rw [pow_zero, mul_one] at hijuv
    have h2 : ψc (ga ^ i * gc' ^ u * gd' ^ v) = 1 := by rw [hijuv]; exact map_one ψc
    simp only [map_mul, map_pow, hψcga, hψcgd', one_pow, one_mul, mul_one] at h2
    have hu0 : u = 0 := Nat.eq_zero_of_dvd_of_lt (hψcgc' ▸ orderOf_dvd_of_pow_eq_one h2) hult
    subst hu0
    rw [pow_zero, mul_one] at hijuv
    have h3 : ψd (ga ^ i * gd' ^ v) = 1 := by rw [hijuv]; exact map_one ψd
    simp only [map_mul, map_pow, hψdga, one_pow, one_mul] at h3
    have hv0 : v = 0 := Nat.eq_zero_of_dvd_of_lt (hψdgd' ▸ orderOf_dvd_of_pow_eq_one h3) hvlt
    subst hv0
    rw [pow_zero, mul_one] at hijuv
    have hdvd : orderOf ga ∣ i := orderOf_dvd_of_pow_eq_one hijuv
    rw [hordga] at hdvd
    exact ⟨Nat.eq_zero_of_dvd_of_lt hdvd hilt, rfl, rfl, rfl⟩
  exact four_commuting_gens_iso hG
    (by rw [← hordga]; exact pow_orderOf_eq_one ga) hgb'sq hgc'sq hgd'sq
    hcommgb' hcommgc' hcommgd' hcommb'c' hcommb'd' hcommc'd' hindep (by norm_num)

theorem order32_of_c2pow4_quotient_abelian_case {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 32) {z : G} (hzc : z ∈ Subgroup.center G) (hzp : orderOf z = 2)
    [hnorm : (Subgroup.zpowers z).Normal]
    (e : (G ⧸ Subgroup.zpowers z) ≃* order16_wild_C2pow4)
    {ga gb gc gd : G}
    (hga : (QuotientGroup.mk' (Subgroup.zpowers z)) ga
      = e.symm (Multiplicative.ofAdd (1 : ZMod 2), 1, 1, 1))
    (hgb : (QuotientGroup.mk' (Subgroup.zpowers z)) gb
      = e.symm (1, Multiplicative.ofAdd (1 : ZMod 2), 1, 1))
    (hgc : (QuotientGroup.mk' (Subgroup.zpowers z)) gc
      = e.symm (1, 1, Multiplicative.ofAdd (1 : ZMod 2), 1))
    (hgd : (QuotientGroup.mk' (Subgroup.zpowers z)) gd
      = e.symm (1, 1, 1, Multiplicative.ofAdd (1 : ZMod 2)))
    (hcab : Commute ga gb) (hcac : Commute ga gc) (hcad : Commute ga gd)
    (hcbc : Commute gb gc) (hcbd : Commute gb gd) (hccd : Commute gc gd) :
    Nonempty (G ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 2)
        × Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
      ∨ Nonempty (G ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)
        × Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
  classical
  have hz2 : z ^ 2 = 1 := by rw [← hzp]; exact pow_orderOf_eq_one z
  have hker : (QuotientGroup.mk' (Subgroup.zpowers z)).ker = Subgroup.zpowers z :=
    QuotientGroup.ker_mk' _
  set π := QuotientGroup.mk' (Subgroup.zpowers z) with hπdef
  have hgapow : π (ga ^ 2) = 1 := by
    rw [map_pow, hga, ← map_pow, Prod.pow_mk, Prod.pow_mk, Prod.pow_mk]; norm_num; decide
  have hgbpow : π (gb ^ 2) = 1 := by
    rw [map_pow, hgb, ← map_pow, Prod.pow_mk, Prod.pow_mk, Prod.pow_mk]; norm_num; decide
  have hgcpow : π (gc ^ 2) = 1 := by
    rw [map_pow, hgc, ← map_pow, Prod.pow_mk, Prod.pow_mk, Prod.pow_mk]; norm_num; decide
  have hgdpow : π (gd ^ 2) = 1 := by
    rw [map_pow, hgd, ← map_pow, Prod.pow_mk, Prod.pow_mk, Prod.pow_mk]; norm_num; decide
  have hgamem : ga ^ 2 ∈ Subgroup.zpowers z := by
    rw [← hker, MonoidHom.mem_ker]; exact hgapow
  have hgbmem : gb ^ 2 ∈ Subgroup.zpowers z := by
    rw [← hker, MonoidHom.mem_ker]; exact hgbpow
  have hgcmem : gc ^ 2 ∈ Subgroup.zpowers z := by
    rw [← hker, MonoidHom.mem_ker]; exact hgcpow
  have hgdmem : gd ^ 2 ∈ Subgroup.zpowers z := by
    rw [← hker, MonoidHom.mem_ker]; exact hgdpow
  have hcaseA := central_pow_cases hz2 hgamem
  have hcaseB := central_pow_cases hz2 hgbmem
  have hcaseC := central_pow_cases hz2 hgcmem
  have hcaseD := central_pow_cases hz2 hgdmem
  set ψa : G →* Multiplicative (ZMod 2) :=
    (MonoidHom.fst _ _).comp (e.toMonoidHom.comp π) with hψadef
  set ψbcd : G →* Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2) :=
    (MonoidHom.snd _ _).comp (e.toMonoidHom.comp π) with hψbcddef
  set ψb : G →* Multiplicative (ZMod 2) := (MonoidHom.fst _ _).comp ψbcd with hψbdef
  set ψcd : G →* Multiplicative (ZMod 2) × Multiplicative (ZMod 2) :=
    (MonoidHom.snd _ _).comp ψbcd with hψcddef
  set ψc : G →* Multiplicative (ZMod 2) := (MonoidHom.fst _ _).comp ψcd with hψcdef
  set ψd : G →* Multiplicative (ZMod 2) := (MonoidHom.snd _ _).comp ψcd with hψddef
  have hψaga : ψa ga = Multiplicative.ofAdd (1 : ZMod 2) := by
    change Prod.fst (e (π ga)) = _; rw [hga, e.apply_symm_apply]
  have hψagb : ψa gb = 1 := by
    change Prod.fst (e (π gb)) = _; rw [hgb, e.apply_symm_apply]
  have hψagc : ψa gc = 1 := by
    change Prod.fst (e (π gc)) = _; rw [hgc, e.apply_symm_apply]
  have hψagd : ψa gd = 1 := by
    change Prod.fst (e (π gd)) = _; rw [hgd, e.apply_symm_apply]
  have hψbga : ψb ga = 1 := by
    rw [hψbdef]; change Prod.fst (Prod.snd (e (π ga))) = _; rw [hga, e.apply_symm_apply]
  have hψbgb : ψb gb = Multiplicative.ofAdd (1 : ZMod 2) := by
    rw [hψbdef]; change Prod.fst (Prod.snd (e (π gb))) = _; rw [hgb, e.apply_symm_apply]
  have hψbgc : ψb gc = 1 := by
    rw [hψbdef]; change Prod.fst (Prod.snd (e (π gc))) = _; rw [hgc, e.apply_symm_apply]
  have hψbgd : ψb gd = 1 := by
    rw [hψbdef]; change Prod.fst (Prod.snd (e (π gd))) = _; rw [hgd, e.apply_symm_apply]
  have hψcga : ψc ga = 1 := by
    rw [hψcdef, hψcddef]
    change Prod.fst (Prod.snd (Prod.snd (e (π ga)))) = _; rw [hga, e.apply_symm_apply]
  have hψcgb : ψc gb = 1 := by
    rw [hψcdef, hψcddef]
    change Prod.fst (Prod.snd (Prod.snd (e (π gb)))) = _; rw [hgb, e.apply_symm_apply]
  have hψcgc : ψc gc = Multiplicative.ofAdd (1 : ZMod 2) := by
    rw [hψcdef, hψcddef]
    change Prod.fst (Prod.snd (Prod.snd (e (π gc)))) = _; rw [hgc, e.apply_symm_apply]
  have hψcgd : ψc gd = 1 := by
    rw [hψcdef, hψcddef]
    change Prod.fst (Prod.snd (Prod.snd (e (π gd)))) = _; rw [hgd, e.apply_symm_apply]
  have hψdga : ψd ga = 1 := by
    rw [hψddef, hψcddef]
    change Prod.snd (Prod.snd (Prod.snd (e (π ga)))) = _; rw [hga, e.apply_symm_apply]
  have hψdgb : ψd gb = 1 := by
    rw [hψddef, hψcddef]
    change Prod.snd (Prod.snd (Prod.snd (e (π gb)))) = _; rw [hgb, e.apply_symm_apply]
  have hψdgc : ψd gc = 1 := by
    rw [hψddef, hψcddef]
    change Prod.snd (Prod.snd (Prod.snd (e (π gc)))) = _; rw [hgc, e.apply_symm_apply]
  have hψdgd : ψd gd = Multiplicative.ofAdd (1 : ZMod 2) := by
    rw [hψddef, hψcddef]
    change Prod.snd (Prod.snd (Prod.snd (e (π gd)))) = _; rw [hgd, e.apply_symm_apply]
  have hz_ne_one : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hzp; exact absurd hzp (by norm_num)
  have hzmem : z ∈ π.ker := by rw [hker]; exact Subgroup.mem_zpowers z
  have hπz : π z = 1 := MonoidHom.mem_ker.mp hzmem
  have hψaz : ψa z = 1 := by
    rw [hψadef]; change Prod.fst (e (π z)) = 1; rw [hπz, map_one]; rfl
  have hψbz : ψb z = 1 := by
    rw [hψbdef]; change Prod.fst (Prod.snd (e (π z))) = 1; rw [hπz, map_one]; rfl
  have hψcz : ψc z = 1 := by
    rw [hψcdef, hψcddef]
    change Prod.fst (Prod.snd (Prod.snd (e (π z)))) = 1; rw [hπz, map_one]; rfl
  have hψdz : ψd z = 1 := by
    rw [hψddef, hψcddef]
    change Prod.snd (Prod.snd (Prod.snd (e (π z)))) = 1; rw [hπz, map_one]; rfl
  have hord2 : orderOf (Multiplicative.ofAdd (1 : ZMod 2)) = 2 := by
    rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  have hordga_2 : (2 : ℕ) ∣ orderOf ga := by
    have hhom : orderOf (ψa ga) ∣ orderOf ga := orderOf_map_dvd _ ga
    rwa [hψaga, hord2] at hhom
  have hordgb_2 : (2 : ℕ) ∣ orderOf gb := by
    have hhom : orderOf (ψb gb) ∣ orderOf gb := orderOf_map_dvd _ gb
    rwa [hψbgb, hord2] at hhom
  have hordgc_2 : (2 : ℕ) ∣ orderOf gc := by
    have hhom : orderOf (ψc gc) ∣ orderOf gc := orderOf_map_dvd _ gc
    rwa [hψcgc, hord2] at hhom
  have hordgd_2 : (2 : ℕ) ∣ orderOf gd := by
    have hhom : orderOf (ψd gd) ∣ orderOf gd := orderOf_map_dvd _ gd
    rwa [hψdgd, hord2] at hhom
  have hordψaga : orderOf (ψa ga) = 2 := by rw [hψaga, hord2]
  have hordψbgb : orderOf (ψb gb) = 2 := by rw [hψbgb, hord2]
  have hordψcgc : orderOf (ψc gc) = 2 := by rw [hψcgc, hord2]
  have hordψdgd : orderOf (ψd gd) = 2 := by rw [hψdgd, hord2]
  rcases hcaseA with hcA | hcA <;> rcases hcaseB with hcB | hcB <;>
    rcases hcaseC with hcC | hcC <;> rcases hcaseD with hcD | hcD
  · -- (0,0,0,0): all trivial, quintuple C2 × C2 × C2 × C2 × C2
    right
    set fa : Multiplicative (ZMod 2) →* G := zmodZPowHom 2 ga hcA with hfadef
    set fb : Multiplicative (ZMod 2) →* G := zmodZPowHom 2 gb hcB with hfbdef
    set fc : Multiplicative (ZMod 2) →* G := zmodZPowHom 2 gc hcC with hfcdef
    set fd : Multiplicative (ZMod 2) →* G := zmodZPowHom 2 gd hcD with hfddef
    set fz : Multiplicative (ZMod 2) →* G := zmodZPowHom 2 z hz2 with hfzdef
    have hcaz : Commute ga z := Subgroup.mem_center_iff.mp hzc ga
    have hcbz : Commute gb z := Subgroup.mem_center_iff.mp hzc gb
    have hccz : Commute gc z := Subgroup.mem_center_iff.mp hzc gc
    have hcdz : Commute gd z := Subgroup.mem_center_iff.mp hzc gd
    have hfa_val : ∀ x : Multiplicative (ZMod 2), fa x = ga ^ (Multiplicative.toAdd x).val := by
      intro x
      have hx : x = Multiplicative.ofAdd (((Multiplicative.toAdd x).val : ZMod 2)) := by
        rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
      have hcast : ((((Multiplicative.toAdd x).val : ℕ) : ℤ) : ZMod 2)
          = ((Multiplicative.toAdd x).val : ZMod 2) := by push_cast; ring
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
    have hfd_val : ∀ x : Multiplicative (ZMod 2), fd x = gd ^ (Multiplicative.toAdd x).val := by
      intro x
      have hx : x = Multiplicative.ofAdd (((Multiplicative.toAdd x).val : ZMod 2)) := by
        rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
      have hcast : ((((Multiplicative.toAdd x).val : ℕ) : ℤ) : ZMod 2)
          = ((Multiplicative.toAdd x).val : ZMod 2) := by push_cast; ring
      conv_lhs => rw [hx, ← hcast]
      rw [hfddef, zmodZPowHom_intCast, zpow_natCast]
    have hfz_val : ∀ x : Multiplicative (ZMod 2), fz x = z ^ (Multiplicative.toAdd x).val := by
      intro x
      have hx : x = Multiplicative.ofAdd (((Multiplicative.toAdd x).val : ZMod 2)) := by
        rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
      have hcast : ((((Multiplicative.toAdd x).val : ℕ) : ℤ) : ZMod 2)
          = ((Multiplicative.toAdd x).val : ZMod 2) := by push_cast; ring
      conv_lhs => rw [hx, ← hcast]
      rw [hfzdef, zmodZPowHom_intCast, zpow_natCast]
    have hcommab : ∀ (x y : Multiplicative (ZMod 2)), Commute (fa x) (fb y) := by
      intro x y; rw [hfa_val x, hfb_val y]; exact hcab.pow_pow _ _
    set Fab := fa.noncommCoprod fb hcommab with hFabdef
    have hcommFabc : ∀ (x : Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
        (y : Multiplicative (ZMod 2)), Commute (Fab x) (fc y) := by
      intro x y
      rw [hFabdef, MonoidHom.noncommCoprod_apply, hfa_val, hfb_val, hfc_val]
      exact (hcac.pow_pow _ _).mul_left (hcbc.pow_pow _ _)
    set Fabc := Fab.noncommCoprod fc hcommFabc with hFabcdef
    have hcommFabcd : ∀ (x : (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
        × Multiplicative (ZMod 2)) (y : Multiplicative (ZMod 2)), Commute (Fabc x) (fd y) := by
      intro x y
      rw [hFabcdef, MonoidHom.noncommCoprod_apply, hFabdef, MonoidHom.noncommCoprod_apply,
        hfa_val, hfb_val, hfc_val, hfd_val]
      exact ((hcad.pow_pow _ _).mul_left (hcbd.pow_pow _ _)).mul_left (hccd.pow_pow _ _)
    set Fabcd := Fabc.noncommCoprod fd hcommFabcd with hFabcddef
    have hcommFabcdz : ∀ (x : ((Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
        × Multiplicative (ZMod 2)) × Multiplicative (ZMod 2)) (y : Multiplicative (ZMod 2)),
        Commute (Fabcd x) (fz y) := by
      intro x y
      rw [hFabcddef, MonoidHom.noncommCoprod_apply, hFabcdef, MonoidHom.noncommCoprod_apply,
        hFabdef, MonoidHom.noncommCoprod_apply, hfa_val, hfb_val, hfc_val, hfd_val, hfz_val]
      exact (((hcaz.pow_pow _ _).mul_left (hcbz.pow_pow _ _)).mul_left
        (hccz.pow_pow _ _)).mul_left (hcdz.pow_pow _ _)
    set Φ := Fabcd.noncommCoprod fz hcommFabcdz with hΦdef
    have hinj : Function.Injective Φ := by
      refine (injective_iff_map_eq_one _).mpr ?_
      rintro ⟨⟨⟨⟨x, y⟩, u⟩, v⟩, w⟩ habcdvw
      simp only [hΦdef, hFabcddef, hFabcdef, hFabdef, MonoidHom.noncommCoprod_apply]
        at habcdvw
      rw [hfa_val x, hfb_val y, hfc_val u, hfd_val v, hfz_val w] at habcdvw
      have hxv_lt : (Multiplicative.toAdd x).val < 2 := ZMod.val_lt _
      have hyv_lt : (Multiplicative.toAdd y).val < 2 := ZMod.val_lt _
      have huv_lt : (Multiplicative.toAdd u).val < 2 := ZMod.val_lt _
      have hvv_lt : (Multiplicative.toAdd v).val < 2 := ZMod.val_lt _
      have hwv_lt : (Multiplicative.toAdd w).val < 2 := ZMod.val_lt _
      have h1 : ψa (ga ^ (Multiplicative.toAdd x).val * gb ^ (Multiplicative.toAdd y).val
          * gc ^ (Multiplicative.toAdd u).val * gd ^ (Multiplicative.toAdd v).val
          * z ^ (Multiplicative.toAdd w).val) = 1 := by rw [habcdvw]; exact map_one ψa
      simp only [map_mul, map_pow, hψaga, hψagb, hψagc, hψagd, hψaz, one_pow,
        mul_one] at h1
      have hxv0 : (Multiplicative.toAdd x).val = 0 := by
        have hdvd := orderOf_dvd_of_pow_eq_one h1
        rw [hord2] at hdvd; exact Nat.eq_zero_of_dvd_of_lt hdvd hxv_lt
      rw [hxv0, pow_zero, one_mul] at habcdvw
      have h2 : ψb (gb ^ (Multiplicative.toAdd y).val * gc ^ (Multiplicative.toAdd u).val
          * gd ^ (Multiplicative.toAdd v).val * z ^ (Multiplicative.toAdd w).val) = 1 := by
        rw [habcdvw]; exact map_one ψb
      simp only [map_mul, map_pow, hψbgb, hψbgc, hψbgd, hψbz, one_pow, mul_one] at h2
      have hyv0 : (Multiplicative.toAdd y).val = 0 := by
        have hdvd := orderOf_dvd_of_pow_eq_one h2
        rw [hord2] at hdvd; exact Nat.eq_zero_of_dvd_of_lt hdvd hyv_lt
      rw [hyv0, pow_zero, one_mul] at habcdvw
      have h3 : ψc (gc ^ (Multiplicative.toAdd u).val * gd ^ (Multiplicative.toAdd v).val
          * z ^ (Multiplicative.toAdd w).val) = 1 := by rw [habcdvw]; exact map_one ψc
      simp only [map_mul, map_pow, hψcgc, hψcgd, hψcz, one_pow, mul_one] at h3
      have huv0 : (Multiplicative.toAdd u).val = 0 := by
        have hdvd := orderOf_dvd_of_pow_eq_one h3
        rw [hord2] at hdvd; exact Nat.eq_zero_of_dvd_of_lt hdvd huv_lt
      rw [huv0, pow_zero, one_mul] at habcdvw
      have h4 : ψd (gd ^ (Multiplicative.toAdd v).val * z ^ (Multiplicative.toAdd w).val)
          = 1 := by rw [habcdvw]; exact map_one ψd
      simp only [map_mul, map_pow, hψdgd, hψdz, one_pow, mul_one] at h4
      have hvv0 : (Multiplicative.toAdd v).val = 0 := by
        have hdvd := orderOf_dvd_of_pow_eq_one h4
        rw [hord2] at hdvd; exact Nat.eq_zero_of_dvd_of_lt hdvd hvv_lt
      rw [hvv0, pow_zero, one_mul] at habcdvw
      have hww0 : (Multiplicative.toAdd w).val = 0 := by
        have hdvd : orderOf z ∣ (Multiplicative.toAdd w).val := orderOf_dvd_of_pow_eq_one habcdvw
        rw [hzp] at hdvd; exact Nat.eq_zero_of_dvd_of_lt hdvd hwv_lt
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
      have hw1 : w = 1 := by
        have h0 : Multiplicative.toAdd w = 0 := (ZMod.val_eq_zero _).mp hww0
        rw [← ofAdd_toAdd w, h0, ofAdd_zero]
      rw [hx1, hy1, hu1, hv1, hw1]; rfl
    have e_range : (((Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
        × Multiplicative (ZMod 2)) × Multiplicative (ZMod 2)) × Multiplicative (ZMod 2)
        ≃* Φ.range := MonoidHom.ofInjective hinj
    have hcardRange : Nat.card Φ.range = 32 := by
      rw [← Nat.card_congr e_range.toEquiv, Nat.card_prod, Nat.card_prod, Nat.card_prod,
        Nat.card_prod]
      simp [Nat.card_eq_fintype_card, ZMod.card]
    have hrange_top : Φ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hcardRange, hG])
    have hfin : G ≃* (((Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
        × Multiplicative (ZMod 2)) × Multiplicative (ZMod 2)) × Multiplicative (ZMod 2) :=
      (e_range.trans ((MulEquiv.subgroupCongr hrange_top).trans Subgroup.topEquiv)).symm
    exact ⟨((hfin.trans MulEquiv.prodAssoc).trans MulEquiv.prodAssoc).trans
      MulEquiv.prodAssoc⟩
  · -- (0,0,0,1): d is anchor
    left
    exact quad_c2_anchor_reduce hG hz2 hz_ne_one hcad.symm hcbd.symm hccd.symm
      hcab hcac hcbc hcD hordgd_2 (Or.inl hcA) (Or.inl hcB) (Or.inl hcC)
      ψa ψb ψc hordψaga hψagb hψagc hψagd hordψbgb hψbga hψbgc hψbgd hordψcgc
      hψcga hψcgb hψcgd
  · -- (0,0,1,0): c is anchor
    left
    exact quad_c2_anchor_reduce hG hz2 hz_ne_one hcac.symm hcbc.symm hccd
      hcab hcad hcbd hcC hordgc_2 (Or.inl hcA) (Or.inl hcB) (Or.inl hcD)
      ψa ψb ψd hordψaga hψagb hψagd hψagc hordψbgb hψbga hψbgd hψbgc hordψdgd
      hψdga hψdgb hψdgc
  · -- (0,0,1,1): c is anchor, d merges
    left
    exact quad_c2_anchor_reduce hG hz2 hz_ne_one hcac.symm hcbc.symm hccd
      hcab hcad hcbd hcC hordgc_2 (Or.inl hcA) (Or.inl hcB) (Or.inr hcD)
      ψa ψb ψd hordψaga hψagb hψagd hψagc hordψbgb hψbga hψbgd hψbgc hordψdgd
      hψdga hψdgb hψdgc
  · -- (0,1,0,0): b is anchor
    left
    exact quad_c2_anchor_reduce hG hz2 hz_ne_one hcab.symm hcbc hcbd
      hcac hcad hccd hcB hordgb_2 (Or.inl hcA) (Or.inl hcC) (Or.inl hcD)
      ψa ψc ψd hordψaga hψagc hψagd hψagb hordψcgc hψcga hψcgd hψcgb hordψdgd
      hψdga hψdgc hψdgb
  · -- (0,1,0,1): b is anchor, d merges
    left
    exact quad_c2_anchor_reduce hG hz2 hz_ne_one hcab.symm hcbc hcbd
      hcac hcad hccd hcB hordgb_2 (Or.inl hcA) (Or.inl hcC) (Or.inr hcD)
      ψa ψc ψd hordψaga hψagc hψagd hψagb hordψcgc hψcga hψcgd hψcgb hordψdgd
      hψdga hψdgc hψdgb
  · -- (0,1,1,0): b is anchor, c merges
    left
    exact quad_c2_anchor_reduce hG hz2 hz_ne_one hcab.symm hcbc hcbd
      hcac hcad hccd hcB hordgb_2 (Or.inl hcA) (Or.inr hcC) (Or.inl hcD)
      ψa ψc ψd hordψaga hψagc hψagd hψagb hordψcgc hψcga hψcgd hψcgb hordψdgd
      hψdga hψdgc hψdgb
  · -- (0,1,1,1): b is anchor, c,d merge
    left
    exact quad_c2_anchor_reduce hG hz2 hz_ne_one hcab.symm hcbc hcbd
      hcac hcad hccd hcB hordgb_2 (Or.inl hcA) (Or.inr hcC) (Or.inr hcD)
      ψa ψc ψd hordψaga hψagc hψagd hψagb hordψcgc hψcga hψcgd hψcgb hordψdgd
      hψdga hψdgc hψdgb
  · -- (1,0,0,0): a is anchor
    left
    exact quad_c2_anchor_reduce hG hz2 hz_ne_one hcab hcac hcad
      hcbc hcbd hccd hcA hordga_2 (Or.inl hcB) (Or.inl hcC) (Or.inl hcD)
      ψb ψc ψd hordψbgb hψbgc hψbgd hψbga hordψcgc hψcgb hψcgd hψcga hordψdgd
      hψdgb hψdgc hψdga
  · -- (1,0,0,1): a is anchor, d merges
    left
    exact quad_c2_anchor_reduce hG hz2 hz_ne_one hcab hcac hcad
      hcbc hcbd hccd hcA hordga_2 (Or.inl hcB) (Or.inl hcC) (Or.inr hcD)
      ψb ψc ψd hordψbgb hψbgc hψbgd hψbga hordψcgc hψcgb hψcgd hψcga hordψdgd
      hψdgb hψdgc hψdga
  · -- (1,0,1,0): a is anchor, c merges
    left
    exact quad_c2_anchor_reduce hG hz2 hz_ne_one hcab hcac hcad
      hcbc hcbd hccd hcA hordga_2 (Or.inl hcB) (Or.inr hcC) (Or.inl hcD)
      ψb ψc ψd hordψbgb hψbgc hψbgd hψbga hordψcgc hψcgb hψcgd hψcga hordψdgd
      hψdgb hψdgc hψdga
  · -- (1,0,1,1): a is anchor, c,d merge
    left
    exact quad_c2_anchor_reduce hG hz2 hz_ne_one hcab hcac hcad
      hcbc hcbd hccd hcA hordga_2 (Or.inl hcB) (Or.inr hcC) (Or.inr hcD)
      ψb ψc ψd hordψbgb hψbgc hψbgd hψbga hordψcgc hψcgb hψcgd hψcga hordψdgd
      hψdgb hψdgc hψdga
  · -- (1,1,0,0): a is anchor, b merges
    left
    exact quad_c2_anchor_reduce hG hz2 hz_ne_one hcab hcac hcad
      hcbc hcbd hccd hcA hordga_2 (Or.inr hcB) (Or.inl hcC) (Or.inl hcD)
      ψb ψc ψd hordψbgb hψbgc hψbgd hψbga hordψcgc hψcgb hψcgd hψcga hordψdgd
      hψdgb hψdgc hψdga
  · -- (1,1,0,1): a is anchor, b,d merge
    left
    exact quad_c2_anchor_reduce hG hz2 hz_ne_one hcab hcac hcad
      hcbc hcbd hccd hcA hordga_2 (Or.inr hcB) (Or.inl hcC) (Or.inr hcD)
      ψb ψc ψd hordψbgb hψbgc hψbgd hψbga hordψcgc hψcgb hψcgd hψcga hordψdgd
      hψdgb hψdgc hψdga
  · -- (1,1,1,0): a is anchor, b,c merge
    left
    exact quad_c2_anchor_reduce hG hz2 hz_ne_one hcab hcac hcad
      hcbc hcbd hccd hcA hordga_2 (Or.inr hcB) (Or.inr hcC) (Or.inl hcD)
      ψb ψc ψd hordψbgb hψbgc hψbgd hψbga hordψcgc hψcgb hψcgd hψcga hordψdgd
      hψdgb hψdgc hψdga
  · -- (1,1,1,1): a is anchor, b,c,d merge
    left
    exact quad_c2_anchor_reduce hG hz2 hz_ne_one hcab hcac hcad
      hcbc hcbd hccd hcA hordga_2 (Or.inr hcB) (Or.inr hcC) (Or.inr hcD)
      ψb ψc ψd hordψbgb hψbgc hψbgd hψbga hordψcgc hψcgb hψcgd hψcga hordψdgd
      hψdgb hψdgc hψdga

end Smallgroups.UsefulTheorems
