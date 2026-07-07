/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order16_Wild
import Smallgroups.UsefulTheorems.PGroupGeneration
import Smallgroups.UsefulTheorems.Order32.GenericTools

/-! ## Descendants of `order16_wild_G5` (`QuaternionGroup 4`, generalized quaternion `Q₁₆`)

`order16_wild_G5 = QuaternionGroup 4`, presented as `⟨A, X | A⁸ = 1, X² = A⁴, XAX⁻¹ = A⁻¹⟩`
(Mathlib writes `a i`/`xa i` for `Aⁱ`/`X·Aⁱ`). Unlike `G2`–`G4`/`G8`–`G10` this is not built
via `SemidirectProduct`, so the lift `s : QuaternionGroup 4 →* G` is constructed directly by
cases on the two constructors, using the relator identities as the multiplicativity proof.
Only the trivial-cocycle branch is recorded: `ga⁸ = 1`, `gx² = ga⁴`, and the conjugation
relation hold exactly (not just mod `z`). -/

namespace Smallgroups.UsefulTheorems

/-- The trivial-cocycle branch over `order16_wild_G5`: both relator identities hold exactly
(no `z`-twist), so `G` splits as `order16_wild_G5 × C₂`. -/
theorem order32_of_q16_quotient_trivial_case {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 32) {z : G} (hzc : z ∈ Subgroup.center G) (hzp : orderOf z = 2)
    [hnorm : (Subgroup.zpowers z).Normal]
    (e : (G ⧸ Subgroup.zpowers z) ≃* order16_wild_G5)
    {ga gx : G}
    (hga : (QuotientGroup.mk' (Subgroup.zpowers z)) ga
      = e.symm (QuaternionGroup.a (1 : ZMod 8)))
    (hgx : (QuotientGroup.mk' (Subgroup.zpowers z)) gx
      = e.symm (QuaternionGroup.xa (0 : ZMod 8)))
    (hga8 : ga ^ 8 = 1) (hgx2 : gx ^ 2 = ga ^ 4) (hrelgca : gx * ga * gx⁻¹ = ga⁻¹) :
    Nonempty (G ≃* order16_wild_G5 × Multiplicative (ZMod 2)) := by
  classical
  set F : Multiplicative (ZMod 8) →* G := zmodZPowHom 8 ga hga8 with hFdef
  have hF1 : F (Multiplicative.ofAdd (1 : ZMod 8)) = ga := by
    rw [hFdef]
    have h := zmodZPowHom_intCast 8 ga hga8 1
    simp only [Int.cast_one, zpow_one] at h
    exact h
  have hFadd : ∀ i j : ZMod 8, F (Multiplicative.ofAdd i) * F (Multiplicative.ofAdd j)
      = F (Multiplicative.ofAdd (i + j)) := by
    intro i j; rw [← map_mul]; congr 1
  have hFneg : ∀ i : ZMod 8, (F (Multiplicative.ofAdd i))⁻¹ = F (Multiplicative.ofAdd (-i)) := by
    intro i; rw [← map_inv]; congr 1
  have hFi : ∀ i : ZMod 8, F (Multiplicative.ofAdd i) = ga ^ i.val := by
    intro i
    rw [show (Multiplicative.ofAdd i : Multiplicative (ZMod 8))
        = (Multiplicative.ofAdd (1 : ZMod 8)) ^ i.val from by
      rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_val, ZMod.cast_id]]
    rw [map_pow, hF1]
  have hconjF1 : gx * F (Multiplicative.ofAdd (1 : ZMod 8)) * gx⁻¹
      = F (Multiplicative.ofAdd (-1 : ZMod 8)) := by
    rw [hF1, ← hFneg, hF1]; exact hrelgca
  set INV : Multiplicative (ZMod 8) →* Multiplicative (ZMod 8) :=
    { toFun := fun m => m⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        change (a * b)⁻¹ = a⁻¹ * b⁻¹
        rw [mul_comm a⁻¹ b⁻¹, mul_inv_rev] } with hINVdef
  have hcompInv : (MulAut.conj gx).toMonoidHom.comp F = F.comp INV := by
    apply monoidHom_ext_ofAdd_one
    change gx * F (Multiplicative.ofAdd (1 : ZMod 8)) * gx⁻¹
      = F (INV (Multiplicative.ofAdd (1 : ZMod 8)))
    change gx * F (Multiplicative.ofAdd (1 : ZMod 8)) * gx⁻¹
      = F ((Multiplicative.ofAdd (1 : ZMod 8))⁻¹)
    rw [← ofAdd_neg]; exact hconjF1
  have hconjF : ∀ x : Multiplicative (ZMod 8), gx * F x * gx⁻¹ = F x⁻¹ := by
    intro x
    have h := DFunLike.congr_fun hcompInv x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    rw [show INV x = x⁻¹ from rfl] at h
    exact h
  have hswap : ∀ i : ZMod 8, F (Multiplicative.ofAdd i) * gx
      = gx * F (Multiplicative.ofAdd (-i)) := by
    intro i
    have h := hconjF (Multiplicative.ofAdd (-i))
    rw [show (Multiplicative.ofAdd (-i) : Multiplicative (ZMod 8))⁻¹
      = Multiplicative.ofAdd i from by rw [← ofAdd_neg, neg_neg]] at h
    have hstep : gx * F (Multiplicative.ofAdd (-i)) * gx⁻¹ * gx
        = F (Multiplicative.ofAdd i) * gx := by rw [h]
    rw [inv_mul_cancel_right] at hstep
    exact hstep.symm
  have hga4eq : F (Multiplicative.ofAdd (4 : ZMod 8)) = ga ^ 4 := by
    rw [show (Multiplicative.ofAdd (4 : ZMod 8) : Multiplicative (ZMod 8))
        = (Multiplicative.ofAdd (1 : ZMod 8)) ^ 4 from by
      rw [← ofAdd_nsmul]; norm_num]
    rw [map_pow, hF1]
  set f : QuaternionGroup 4 → G := fun q => match q with
    | QuaternionGroup.a i => F (Multiplicative.ofAdd i)
    | QuaternionGroup.xa i => gx * F (Multiplicative.ofAdd i) with hfdef
  have hs_a : ∀ i : ZMod 8, f (QuaternionGroup.a i) = F (Multiplicative.ofAdd i) := fun _ => rfl
  have hs_xa : ∀ i : ZMod 8, f (QuaternionGroup.xa i) = gx * F (Multiplicative.ofAdd i) :=
    fun _ => rfl
  have hmap_mul : ∀ x y : QuaternionGroup 4, f (x * y) = f x * f y := by
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
    · change f (QuaternionGroup.a ((4 : ZMod 8) + j - i)) = _
      change F (Multiplicative.ofAdd ((4 : ZMod 8) + j - i)) =
        (gx * F (Multiplicative.ofAdd i)) * (gx * F (Multiplicative.ofAdd j))
      have hchain : (gx * F (Multiplicative.ofAdd i)) * (gx * F (Multiplicative.ofAdd j))
          = F (Multiplicative.ofAdd ((4 : ZMod 8) + j - i)) := by
        calc (gx * F (Multiplicative.ofAdd i)) * (gx * F (Multiplicative.ofAdd j))
            = gx * (F (Multiplicative.ofAdd i) * gx) * F (Multiplicative.ofAdd j) := by group
          _ = gx * (gx * F (Multiplicative.ofAdd (-i))) * F (Multiplicative.ofAdd j) := by
                rw [hswap]
          _ = (gx * gx) * (F (Multiplicative.ofAdd (-i)) * F (Multiplicative.ofAdd j)) := by
                group
          _ = gx ^ 2 * F (Multiplicative.ofAdd (-i + j)) := by rw [hFadd, sq]
          _ = ga ^ 4 * F (Multiplicative.ofAdd (-i + j)) := by rw [hgx2]
          _ = F (Multiplicative.ofAdd (4 : ZMod 8)) * F (Multiplicative.ofAdd (-i + j)) := by
                rw [hga4eq]
          _ = F (Multiplicative.ofAdd ((4 : ZMod 8) + (-i + j))) := by rw [hFadd]
          _ = F (Multiplicative.ofAdd ((4 : ZMod 8) + j - i)) := by congr 2; abel
      exact hchain.symm
  set s : QuaternionGroup 4 →* G := MonoidHom.mk' f hmap_mul with hsdef
  have hπga : (QuotientGroup.mk' (Subgroup.zpowers z)) ga
      = e.symm (QuaternionGroup.a (1 : ZMod 8)) := hga
  have hπgx : (QuotientGroup.mk' (Subgroup.zpowers z)) gx
      = e.symm (QuaternionGroup.xa (0 : ZMod 8)) := hgx
  have hπs : ∀ q : QuaternionGroup 4,
      (QuotientGroup.mk' (Subgroup.zpowers z)) (s q) = e.symm q := by
    rintro (i | i)
    · change (QuotientGroup.mk' (Subgroup.zpowers z)) (f (QuaternionGroup.a i)) = _
      rw [hs_a, hFi, map_pow, hπga, ← map_pow, QuaternionGroup.a_one_pow]
      congr 2
      rw [ZMod.natCast_val, ZMod.cast_id]
    · change (QuotientGroup.mk' (Subgroup.zpowers z)) (f (QuaternionGroup.xa i)) = _
      rw [hs_xa, map_mul, hFi, map_pow, hπgx, hπga, ← map_pow, QuaternionGroup.a_one_pow,
        ← map_mul, QuaternionGroup.xa_mul_a]
      congr 2
      rw [zero_add, ZMod.natCast_val, ZMod.cast_id]
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
  have hzrange : ∀ q : QuaternionGroup 4, s q = z → q = 1 := by
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
  exact central_ext_split_iso_prod hG card_quaternion_group_4 hzc hzp s hs_inj hzrange

end Smallgroups.UsefulTheorems
