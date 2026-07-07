/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order16_Wild
import Smallgroups.UsefulTheorems.PGroupGeneration
import Smallgroups.UsefulTheorems.Order32.GenericTools

/-! ## Descendants of `order16_wild_G11` (`Q₈ × C₂`)

`order16_wild_G11 = QuaternionGroup 2 × C₂`, a direct product. The `QuaternionGroup 2`
factor is presented as `⟨A, X | A⁴ = 1, X² = A², XAX⁻¹ = A⁻¹⟩`. We lift its two generators
exactly as for `G5` (with modulus `4` instead of `8`), then adjoin a third lift `gd` for the
`C₂` factor, commuting with both. Only the trivial-cocycle branch is recorded. -/

namespace Smallgroups.UsefulTheorems

/-- The trivial-cocycle branch over `order16_wild_G11`: both `Q₈` relator identities and the
`C₂` relator hold exactly, and the extra generator commutes with both, so `G` splits as
`order16_wild_G11 × C₂`. -/
theorem order32_of_q8c2_quotient_trivial_case {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 32) {z : G} (hzc : z ∈ Subgroup.center G) (hzp : orderOf z = 2)
    [hnorm : (Subgroup.zpowers z).Normal]
    (e : (G ⧸ Subgroup.zpowers z) ≃* order16_wild_G11)
    {ga gx gd : G}
    (hga : (QuotientGroup.mk' (Subgroup.zpowers z)) ga
      = e.symm (QuaternionGroup.a (1 : ZMod 4), 1))
    (hgx : (QuotientGroup.mk' (Subgroup.zpowers z)) gx
      = e.symm (QuaternionGroup.xa (0 : ZMod 4), 1))
    (hgd : (QuotientGroup.mk' (Subgroup.zpowers z)) gd
      = e.symm (QuaternionGroup.a (0 : ZMod 4), Multiplicative.ofAdd (1 : ZMod 2)))
    (hga4 : ga ^ 4 = 1) (hgx2 : gx ^ 2 = ga ^ 2) (hrelgca : gx * ga * gx⁻¹ = ga⁻¹)
    (hgd2 : gd ^ 2 = 1) (hcommdga : Commute gd ga) (hcommdgx : Commute gd gx) :
    Nonempty (G ≃* order16_wild_G11 × Multiplicative (ZMod 2)) := by
  classical
  set F : Multiplicative (ZMod 4) →* G := zmodZPowHom 4 ga hga4 with hFdef
  have hF1 : F (Multiplicative.ofAdd (1 : ZMod 4)) = ga := by
    rw [hFdef]
    have h := zmodZPowHom_intCast 4 ga hga4 1
    simp only [Int.cast_one, zpow_one] at h
    exact h
  have hFadd : ∀ i j : ZMod 4, F (Multiplicative.ofAdd i) * F (Multiplicative.ofAdd j)
      = F (Multiplicative.ofAdd (i + j)) := by
    intro i j; rw [← map_mul]; congr 1
  have hFneg : ∀ i : ZMod 4, (F (Multiplicative.ofAdd i))⁻¹ = F (Multiplicative.ofAdd (-i)) := by
    intro i; rw [← map_inv]; congr 1
  have hFi : ∀ i : ZMod 4, F (Multiplicative.ofAdd i) = ga ^ i.val := by
    intro i
    rw [show (Multiplicative.ofAdd i : Multiplicative (ZMod 4))
        = (Multiplicative.ofAdd (1 : ZMod 4)) ^ i.val from by
      rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_val, ZMod.cast_id]]
    rw [map_pow, hF1]
  have hconjF1 : gx * F (Multiplicative.ofAdd (1 : ZMod 4)) * gx⁻¹
      = F (Multiplicative.ofAdd (-1 : ZMod 4)) := by
    rw [hF1, ← hFneg, hF1]; exact hrelgca
  set INV : Multiplicative (ZMod 4) →* Multiplicative (ZMod 4) :=
    { toFun := fun m => m⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        change (a * b)⁻¹ = a⁻¹ * b⁻¹
        rw [mul_comm a⁻¹ b⁻¹, mul_inv_rev] } with hINVdef
  have hcompInv : (MulAut.conj gx).toMonoidHom.comp F = F.comp INV := by
    apply monoidHom_ext_ofAdd_one
    change gx * F (Multiplicative.ofAdd (1 : ZMod 4)) * gx⁻¹
      = F (INV (Multiplicative.ofAdd (1 : ZMod 4)))
    change gx * F (Multiplicative.ofAdd (1 : ZMod 4)) * gx⁻¹
      = F ((Multiplicative.ofAdd (1 : ZMod 4))⁻¹)
    rw [← ofAdd_neg]; exact hconjF1
  have hconjF : ∀ x : Multiplicative (ZMod 4), gx * F x * gx⁻¹ = F x⁻¹ := by
    intro x
    have h := DFunLike.congr_fun hcompInv x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    rw [show INV x = x⁻¹ from rfl] at h
    exact h
  have hswap : ∀ i : ZMod 4, F (Multiplicative.ofAdd i) * gx
      = gx * F (Multiplicative.ofAdd (-i)) := by
    intro i
    have h := hconjF (Multiplicative.ofAdd (-i))
    rw [show (Multiplicative.ofAdd (-i) : Multiplicative (ZMod 4))⁻¹
      = Multiplicative.ofAdd i from by rw [← ofAdd_neg, neg_neg]] at h
    have hstep : gx * F (Multiplicative.ofAdd (-i)) * gx⁻¹ * gx
        = F (Multiplicative.ofAdd i) * gx := by rw [h]
    rw [inv_mul_cancel_right] at hstep
    exact hstep.symm
  have hga2eq : F (Multiplicative.ofAdd (2 : ZMod 4)) = ga ^ 2 := by
    rw [show (Multiplicative.ofAdd (2 : ZMod 4) : Multiplicative (ZMod 4))
        = (Multiplicative.ofAdd (1 : ZMod 4)) ^ 2 from by
      rw [← ofAdd_nsmul]; norm_num]
    rw [map_pow, hF1]
  set f : QuaternionGroup 2 → G := fun q => match q with
    | QuaternionGroup.a i => F (Multiplicative.ofAdd i)
    | QuaternionGroup.xa i => gx * F (Multiplicative.ofAdd i) with hfdef
  have hs_a : ∀ i : ZMod 4, f (QuaternionGroup.a i) = F (Multiplicative.ofAdd i) := fun _ => rfl
  have hs_xa : ∀ i : ZMod 4, f (QuaternionGroup.xa i) = gx * F (Multiplicative.ofAdd i) :=
    fun _ => rfl
  have hmap_mul : ∀ x y : QuaternionGroup 2, f (x * y) = f x * f y := by
    rintro (i | i) (j | j)
    · change f (QuaternionGroup.a (i + j)) = _
      change F (Multiplicative.ofAdd (i + j))
        = F (Multiplicative.ofAdd i) * F (Multiplicative.ofAdd j)
      rw [hFadd]
    · change f (QuaternionGroup.xa (j - i)) = _
      change gx * F (Multiplicative.ofAdd (j - i)) =
        F (Multiplicative.ofAdd i) * (gx * F (Multiplicative.ofAdd j))
      have hchain : F (Multiplicative.ofAdd i) * (gx * F (Multiplicative.ofAdd j))
          = gx * F (Multiplicative.ofAdd (j - i)) := by
        calc F (Multiplicative.ofAdd i) * (gx * F (Multiplicative.ofAdd j))
            = F (Multiplicative.ofAdd i) * gx * F (Multiplicative.ofAdd j) := by group
          _ = gx * F (Multiplicative.ofAdd (-i)) * F (Multiplicative.ofAdd j) := by rw [hswap]
          _ = gx * (F (Multiplicative.ofAdd (-i)) * F (Multiplicative.ofAdd j)) := by group
          _ = gx * F (Multiplicative.ofAdd (-i + j)) := by rw [hFadd]
          _ = gx * F (Multiplicative.ofAdd (j - i)) := by congr 2; abel_nf
      exact hchain.symm
    · change f (QuaternionGroup.xa (i + j)) = _
      change gx * F (Multiplicative.ofAdd (i + j)) =
        (gx * F (Multiplicative.ofAdd i)) * F (Multiplicative.ofAdd j)
      have hassoc : (gx * F (Multiplicative.ofAdd i)) * F (Multiplicative.ofAdd j)
          = gx * (F (Multiplicative.ofAdd i) * F (Multiplicative.ofAdd j)) := by group
      rw [hassoc, hFadd]
    · change f (QuaternionGroup.a ((2 : ZMod 4) + j - i)) = _
      change F (Multiplicative.ofAdd ((2 : ZMod 4) + j - i)) =
        (gx * F (Multiplicative.ofAdd i)) * (gx * F (Multiplicative.ofAdd j))
      have hchain : (gx * F (Multiplicative.ofAdd i)) * (gx * F (Multiplicative.ofAdd j))
          = F (Multiplicative.ofAdd ((2 : ZMod 4) + j - i)) := by
        calc (gx * F (Multiplicative.ofAdd i)) * (gx * F (Multiplicative.ofAdd j))
            = gx * (F (Multiplicative.ofAdd i) * gx) * F (Multiplicative.ofAdd j) := by group
          _ = gx * (gx * F (Multiplicative.ofAdd (-i))) * F (Multiplicative.ofAdd j) := by
                rw [hswap]
          _ = (gx * gx) * (F (Multiplicative.ofAdd (-i)) * F (Multiplicative.ofAdd j)) := by
                group
          _ = gx ^ 2 * F (Multiplicative.ofAdd (-i + j)) := by rw [hFadd, sq]
          _ = ga ^ 2 * F (Multiplicative.ofAdd (-i + j)) := by rw [hgx2]
          _ = F (Multiplicative.ofAdd (2 : ZMod 4)) * F (Multiplicative.ofAdd (-i + j)) := by
                rw [hga2eq]
          _ = F (Multiplicative.ofAdd ((2 : ZMod 4) + (-i + j))) := by rw [hFadd]
          _ = F (Multiplicative.ofAdd ((2 : ZMod 4) + j - i)) := by congr 2; abel
      exact hchain.symm
  set s1 : QuaternionGroup 2 →* G := MonoidHom.mk' f hmap_mul with hs1def
  have hs1_a : ∀ i : ZMod 4, s1 (QuaternionGroup.a i) = F (Multiplicative.ofAdd i) := hs_a
  have hs1_xa : ∀ i : ZMod 4, s1 (QuaternionGroup.xa i) = gx * F (Multiplicative.ofAdd i) := hs_xa
  set fg : Multiplicative (ZMod 2) →* G := zmodZPowHom 2 gd hgd2 with hfgdef
  have hfgd : fg (Multiplicative.ofAdd (1 : ZMod 2)) = gd := by
    rw [hfgdef]
    have h := zmodZPowHom_intCast 2 gd hgd2 1
    simp only [Int.cast_one, zpow_one] at h
    exact h
  have hcommdF : ∀ i : ZMod 4, Commute gd (F (Multiplicative.ofAdd i)) := by
    intro i; rw [hFi]; exact hcommdga.pow_right _
  have hc2cases : ∀ c : Multiplicative (ZMod 2), c = 1 ∨ c = Multiplicative.ofAdd (1 : ZMod 2) :=
    by decide
  have hcomm' : ∀ (q : QuaternionGroup 2) (c : Multiplicative (ZMod 2)),
      Commute (s1 q) (fg c) := by
    intro q c
    have hcommq : Commute gd (s1 q) := by
      rcases q with i | i
      · rw [hs1_a]; exact hcommdF i
      · rw [hs1_xa]; exact hcommdgx.mul_right (hcommdF i)
    rcases hc2cases c with rfl | rfl
    · simp
    · rw [hfgd]; exact hcommq.symm
  set s : order16_wild_G11 →* G := s1.noncommCoprod fg hcomm' with hsdef
  have hπga : (QuotientGroup.mk' (Subgroup.zpowers z)) ga
      = e.symm (QuaternionGroup.a (1 : ZMod 4), 1) := hga
  have hπgx : (QuotientGroup.mk' (Subgroup.zpowers z)) gx
      = e.symm (QuaternionGroup.xa (0 : ZMod 4), 1) := hgx
  have hπgd : (QuotientGroup.mk' (Subgroup.zpowers z)) gd
      = e.symm (QuaternionGroup.a (0 : ZMod 4), Multiplicative.ofAdd (1 : ZMod 2)) := hgd
  have hπs1 : ∀ q : QuaternionGroup 2,
      (QuotientGroup.mk' (Subgroup.zpowers z)) (s1 q) = e.symm (q, 1) := by
    rintro (i | i)
    · change (QuotientGroup.mk' (Subgroup.zpowers z)) (f (QuaternionGroup.a i)) = _
      rw [hs_a, hFi, map_pow, hπga, ← map_pow]
      rw [show ((QuaternionGroup.a (1:ZMod 4), (1:Multiplicative (ZMod 2))) : QuaternionGroup 2
          × Multiplicative (ZMod 2)) ^ i.val
          = (QuaternionGroup.a (1:ZMod 4) ^ i.val, (1:Multiplicative (ZMod 2))) from by
        rw [Prod.pow_mk]; simp]
      rw [QuaternionGroup.a_one_pow]
      congr 2
      rw [ZMod.natCast_val, ZMod.cast_id]
    · change (QuotientGroup.mk' (Subgroup.zpowers z)) (f (QuaternionGroup.xa i)) = _
      rw [hs_xa, map_mul, hFi, map_pow, hπgx, hπga, ← map_pow]
      rw [show ((QuaternionGroup.a (1:ZMod 4), (1:Multiplicative (ZMod 2))) : QuaternionGroup 2
          × Multiplicative (ZMod 2)) ^ i.val
          = (QuaternionGroup.a (1:ZMod 4) ^ i.val, (1:Multiplicative (ZMod 2))) from by
        rw [Prod.pow_mk]; simp]
      rw [QuaternionGroup.a_one_pow, ← map_mul]
      rw [show ((QuaternionGroup.xa (0:ZMod 4), (1:Multiplicative (ZMod 2))) : QuaternionGroup 2
          × Multiplicative (ZMod 2)) *
          (QuaternionGroup.a (i.val : ZMod 4), (1:Multiplicative (ZMod 2)))
          = (QuaternionGroup.xa (0:ZMod 4) * QuaternionGroup.a (i.val : ZMod 4),
            (1:Multiplicative (ZMod 2))) from by simp]
      rw [QuaternionGroup.xa_mul_a]
      congr 2
      rw [zero_add, ZMod.natCast_val, ZMod.cast_id]
  have hπs : ∀ q : order16_wild_G11,
      (QuotientGroup.mk' (Subgroup.zpowers z)) (s q) = e.symm q := by
    rintro ⟨q1, c⟩
    change (QuotientGroup.mk' (Subgroup.zpowers z)) (s1 q1 * fg c) = _
    rw [map_mul, hπs1]
    rcases hc2cases c with rfl | rfl
    · rw [fg.map_one, map_one, mul_one]
    · rw [hfgd, hπgd, ← map_mul]
      congr 2
      simp
  have hz2 : z ^ 2 = 1 := by rw [← hzp]; exact pow_orderOf_eq_one z
  have hzne1 : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hzp; exact absurd hzp (by norm_num)
  have hs_inj : Function.Injective s := by
    intro q1 q2 hq
    have h1 := hπs q1
    have h2 := hπs q2
    rw [hq] at h1
    have : e.symm q1 = e.symm q2 := h1.symm.trans h2
    exact e.symm.injective this
  have hzrange : ∀ q : order16_wild_G11, s q = z → q = 1 := by
    intro q hqz
    have h1 := hπs q
    have hzker : z ∈ (QuotientGroup.mk' (Subgroup.zpowers z)).ker := by
      rw [QuotientGroup.ker_mk']; exact Subgroup.mem_zpowers z
    have hπz : (QuotientGroup.mk' (Subgroup.zpowers z)) z = 1 := MonoidHom.mem_ker.mp hzker
    rw [hqz, hπz] at h1
    have h2 : q = e 1 := by
      have := congrArg e h1.symm
      simpa using this
    rw [h2, map_one]
  exact central_ext_split_iso_prod hG (card_order16_wild_G11) hzc hzp s hs_inj hzrange

end Smallgroups.UsefulTheorems
