/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order16_Wild
import Smallgroups.UsefulTheorems.PGroupGeneration

/-!
# Order 32: generic tools for semidirect-product-shaped parents

Reusable tools for descendant branches whose order-`16` parent is a `SemidirectProduct`
(or otherwise presented by cyclic generators): `central_ext_split_iso_prod` closes the
"all cocycle bits trivial" branch (`G ≃* Q × C₂`); `central_ext_full_iso` closes a "fully
absorbed" doubled-generator branch (`G ≃* Q'` directly, no residual `C₂` factor);
`zmod_pow_eq_ofAdd_one_pow`, `monoidHom_ext_ofAdd_one`, `monoidHom_ext_prod_ofAdd_one` are
the generator-reduction lemmas used to verify `SemidirectProduct.lift` compatibility
conditions by a finite case split at the generator(s) only.
-/

namespace Smallgroups.UsefulTheorems

/-- If `z` is central of order `2` in `G` (`Nat.card G = 32`), `Q` has order `16`, and
`s : Q →* G` is an injective section that never hits `z`, then `G ≃* Q × C₂`. -/
theorem central_ext_split_iso_prod {G Q : Type*} [Group G] [Group Q] [Finite G]
    [Finite Q] (hG : Nat.card G = 32) (hQ : Nat.card Q = 16)
    {z : G} (hzc : z ∈ Subgroup.center G) (hzp : orderOf z = 2)
    (s : Q →* G) (hs : Function.Injective s) (hzrange : ∀ q : Q, s q = z → q = 1) :
    Nonempty (G ≃* Q × Multiplicative (ZMod 2)) := by
  classical
  have hz2 : z ^ 2 = 1 := by rw [← hzp]; exact pow_orderOf_eq_one z
  have hzne1 : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hzp; exact absurd hzp (by norm_num)
  set fz : Multiplicative (ZMod 2) →* G := zmodZPowHom 2 z hz2 with hfzdef
  have hfz1 : fz (Multiplicative.ofAdd (1 : ZMod 2)) = z := by
    have h := zmodZPowHom_intCast 2 z hz2 1
    simp only [Int.cast_one, zpow_one] at h
    rw [hfzdef]; exact h
  have hcommsz : ∀ q : Q, Commute (s q) z := fun q => Subgroup.mem_center_iff.mp hzc (s q)
  have hc2cases : ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = Multiplicative.ofAdd (1 : ZMod 2) :=
    by decide
  have hcomm' : ∀ (q : Q) (c : Multiplicative (ZMod 2)), Commute (s q) (fz c) := by
    intro q c
    rcases hc2cases c with rfl | rfl
    · simp
    · rw [hfz1]; exact hcommsz q
  set Φ := s.noncommCoprod fz hcomm' with hΦdef
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_one _).mpr ?_
    rintro ⟨q, c⟩ hqc
    simp only [hΦdef, MonoidHom.noncommCoprod_apply] at hqc
    rcases hc2cases c with rfl | rfl
    · rw [map_one, mul_one] at hqc
      have hq1 : q = 1 := hs (by rw [hqc, map_one])
      rw [hq1]; rfl
    · exfalso
      rw [hfz1] at hqc
      have hzinvz : z⁻¹ = z :=
        (eq_inv_of_mul_eq_one_left (by rw [← sq]; exact hz2)).symm
      have hqz : s q = z := by
        have h1 : s q = z⁻¹ := eq_inv_of_mul_eq_one_left hqc
        rwa [hzinvz] at h1
      have hq1 : q = 1 := hzrange q hqz
      rw [hq1, map_one] at hqz
      exact hzne1 hqz.symm
  have e_range : Q × Multiplicative (ZMod 2) ≃* Φ.range := MonoidHom.ofInjective hinj
  have hcardRange : Nat.card Φ.range = 32 := by
    rw [← Nat.card_congr e_range.toEquiv, Nat.card_prod]
    simp [Nat.card_eq_fintype_card, ZMod.card, hQ]
  have hrange_top : Φ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hcardRange, hG])
  exact ⟨(e_range.trans ((MulEquiv.subgroupCongr hrange_top).trans Subgroup.topEquiv)).symm⟩

/-- A power of the generator of `Multiplicative (ZMod n)` written back as a power. -/
theorem zmod_pow_eq_ofAdd_one_pow {n : ℕ} [NeZero n] (a : Multiplicative (ZMod n)) :
    a = (Multiplicative.ofAdd (1 : ZMod n)) ^ (Multiplicative.toAdd a).val := by
  have ha : a = Multiplicative.ofAdd (((Multiplicative.toAdd a).val : ZMod n)) := by
    rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
  conv_lhs => rw [ha]
  rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one]

/-- Two homomorphisms out of `Multiplicative (ZMod n)` agree everywhere as soon as they
agree at the generator. -/
theorem monoidHom_ext_ofAdd_one {G : Type*} [Group G] {n : ℕ} [NeZero n]
    {f1 f2 : Multiplicative (ZMod n) →* G}
    (h : f1 (Multiplicative.ofAdd 1) = f2 (Multiplicative.ofAdd 1)) : f1 = f2 := by
  apply MonoidHom.ext
  intro a
  rw [zmod_pow_eq_ofAdd_one_pow a, map_pow, map_pow, h]

/-- Two homomorphisms out of `Multiplicative (ZMod m) × Multiplicative (ZMod n)` agree
everywhere as soon as they agree at the two generators `(ofAdd 1, 1)` and `(1, ofAdd 1)`. -/
theorem monoidHom_ext_prod_ofAdd_one {H : Type*} [Group H] {m n : ℕ} [NeZero m]
    [NeZero n] {f1 f2 : (Multiplicative (ZMod m) × Multiplicative (ZMod n)) →* H}
    (h1 : f1 (Multiplicative.ofAdd 1, 1) = f2 (Multiplicative.ofAdd 1, 1))
    (h2 : f1 (1, Multiplicative.ofAdd 1) = f2 (1, Multiplicative.ofAdd 1)) : f1 = f2 := by
  apply MonoidHom.ext
  rintro ⟨a, b⟩
  have hab : (a, b) = (Multiplicative.ofAdd (1 : ZMod m), (1 : Multiplicative (ZMod n)))
        ^ (Multiplicative.toAdd a).val
      * ((1 : Multiplicative (ZMod m)), Multiplicative.ofAdd (1 : ZMod n))
        ^ (Multiplicative.toAdd b).val := by
    rw [Prod.pow_mk, Prod.pow_mk, one_pow, one_pow]
    have hmul : ((Multiplicative.ofAdd (1 : ZMod m)) ^ (Multiplicative.toAdd a).val,
          (1 : Multiplicative (ZMod n))) *
        ((1 : Multiplicative (ZMod m)),
          (Multiplicative.ofAdd (1 : ZMod n)) ^ (Multiplicative.toAdd b).val)
        = ((Multiplicative.ofAdd (1 : ZMod m)) ^ (Multiplicative.toAdd a).val,
          (Multiplicative.ofAdd (1 : ZMod n)) ^ (Multiplicative.toAdd b).val) := by
      simp [Prod.mk_mul_mk]
    rw [hmul]
    congr 1
    · exact zmod_pow_eq_ofAdd_one_pow a
    · exact zmod_pow_eq_ofAdd_one_pow b
  rw [hab, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, h1, h2]

/-- If an injective hom `s : Q →* G` between two groups of the SAME order-32 cardinality
exists, `G ≃* Q` (no residual `C₂` factor to split off — used for "fully absorbed"
doubled-generator branches). -/
theorem central_ext_full_iso {G Q : Type*} [Group G] [Group Q] [Finite G] [Finite Q]
    (hG : Nat.card G = 32) (hQ : Nat.card Q = 32)
    (s : Q →* G) (hs : Function.Injective s) : Nonempty (G ≃* Q) := by
  have e_range : Q ≃* s.range := MonoidHom.ofInjective hs
  have hcardRange : Nat.card s.range = 32 := by
    rw [← Nat.card_congr e_range.toEquiv, hQ]
  have hrange_top : s.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hcardRange, hG])
  exact ⟨(e_range.trans ((MulEquiv.subgroupCongr hrange_top).trans Subgroup.topEquiv)).symm⟩

end Smallgroups.UsefulTheorems
