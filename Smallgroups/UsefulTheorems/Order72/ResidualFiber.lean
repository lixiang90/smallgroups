/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order72.ResidualProof

/-!
# Fiber-product identification of the order-`3` kernel residual branches

This file finishes the residual branch of the order-`72` classification: if `G` has a
surjection `G ⧸ K ≃* S₄` with `|K| = 3`, then `G` is one of the three representatives
`C₃.S₄`, `C₃ × S₄`, `C₃ ⋊[sign] S₄`.  Together with the order-`6` kernel branch
(`order72_kernel_order_six_branch_repCases`) this proves

* `order72_residual_kernel_cases_to_repCases`,

eliminating the axiom formerly assumed in `Order72/Classification.lean`.

The argument follows the template of the `RD = D₃ × C₃` branch already formalised in
`ResidualProof.lean`: the quotient of `G` by the normal Klein complement `N` (order `4`)
is a nonabelian group of order `18`; the map `G → S₄ × (G ⧸ N)` embeds `G` as a Goursat
subgroup with `goursatFst = V₄`; each of the three order-`18` possibilities is then
identified with the corresponding fiber product over the common `D₃`-quotient.  Twists
by automorphisms of `D₃` are absorbed by inner automorphisms of `S₄`
(`order72_S4_fiber_twist_mulEquiv`), using `Aut(D₃) = Inn(D₃)`.
-/

namespace Smallgroups.UsefulTheorems

open Equiv

/-- `V₄` is normal in `S₄` (global instance for this development). -/
instance instOrder72S4V4NormalFiber : order72_S4_V4.Normal := order72_S4_V4_normal

variable {G : Type} [Group G]

/-! ## Surjectivity and kernels of the standard quotient maps -/

section QuotientMaps

/-- The quotient model `S₄ → D₃` is surjective. -/
theorem order72_S4ToD3Quot_surjective :
    Function.Surjective order72_S4ToD3Quot := by
  intro d
  obtain ⟨q, hq⟩ := (Classical.choice order72_S4_quotient_V4_mulEquiv_D3).surjective d
  obtain ⟨s, hs⟩ := QuotientGroup.mk'_surjective order72_S4_V4 q
  refine ⟨s, ?_⟩
  change (Classical.choice order72_S4_quotient_V4_mulEquiv_D3)
    ((QuotientGroup.mk' order72_S4_V4) s) = d
  rw [hs, hq]

/-- The pairing-action map `S₄ → S₃` is surjective. -/
theorem order72_S4ToS3_perm_surjective :
    Function.Surjective order72_S4ToS3_perm := by
  decide +kernel

/-- The quotient `S₄ → D₃` via `S₃ = Perm (Fin 3)` is surjective. -/
theorem order72_S4ToS3_surjective :
    Function.Surjective order72_S4ToS3 :=
  order72_perm3_to_d3.surjective.comp order72_S4ToS3_perm_surjective

/-- Membership in the Klein four `V₄ ≤ S₄`: the identity and the double
transpositions. -/
theorem order72_S4_V4_mem_iff (σ : order72_S4) :
    σ ∈ order72_S4_V4 ↔ σ = 1 ∨ σ.cycleType = {2, 2} := by
  constructor
  · intro hσ
    rw [order72_S4_V4, Subgroup.mem_map] at hσ
    obtain ⟨a, ha, haa⟩ := hσ
    rw [← haa]
    rw [← SetLike.mem_coe, alternatingGroup.coe_kleinFour_of_card_eq_four (α := Fin 4)
      (by simp), Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq] at ha
    rcases ha with ha1 | ha2
    · exact Or.inl (congrArg Subtype.val ha1)
    · exact Or.inr ha2
  · rintro (rfl | hcycle)
    · exact Subgroup.one_mem _
    · have hA4 : σ ∈ alternatingGroup (Fin 4) := by
        rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_of_cycleType, hcycle]
        decide
      exact Subgroup.mem_map.mpr ⟨⟨σ, hA4⟩, by
        rw [← SetLike.mem_coe, alternatingGroup.coe_kleinFour_of_card_eq_four (α := Fin 4)
          (by simp), Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
        exact Or.inr hcycle, rfl⟩

/-- The kernel of the pairing-action map `S₄ → S₃` is `V₄`. -/
theorem order72_S4ToS3_perm_ker_eq_V4 : order72_S4ToS3_perm.ker = order72_S4_V4 := by
  ext σ
  rw [MonoidHom.mem_ker, order72_S4_V4_mem_iff]
  revert σ
  decide +kernel

/-- The kernel of `S₄ → D₃` through `S₃` is `V₄`. -/
theorem order72_S4ToS3_ker_eq_V4 : order72_S4ToS3.ker = order72_S4_V4 := by
  rw [← order72_S4ToS3_perm_ker_eq_V4]
  ext σ
  simp only [MonoidHom.mem_ker, order72_S4ToS3, MonoidHom.coe_comp,
    MulEquiv.coe_toMonoidHom, Function.comp_apply]
  rw [← map_one order72_perm3_to_d3, order72_perm3_to_d3.injective.eq_iff]

theorem order72_S4ToD3Quot_range_top : order72_S4ToD3Quot.range = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro d
  obtain ⟨s, hs⟩ := order72_S4ToD3Quot_surjective d
  rw [MonoidHom.mem_range]
  exact ⟨s, hs⟩

theorem order72_S4ToS3_range_top : order72_S4ToS3.range = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro d
  obtain ⟨s, hs⟩ := order72_S4ToS3_surjective d
  rw [MonoidHom.mem_range]
  exact ⟨s, hs⟩

/-- The quotient identification `S₄/V₄ ≃ D₃` factoring `order72_S4ToD3Quot`. -/
noncomputable def order72_S4_quotV4_mulEquiv_D3 :
    order72_S4 ⧸ order72_S4_V4 ≃* DihedralGroup 3 :=
  (QuotientGroup.quotientMulEquivOfEq order72_S4ToD3Quot_ker_eq_V4.symm).trans
    ((QuotientGroup.quotientKerEquivRange order72_S4ToD3Quot).trans
      ((MulEquiv.subgroupCongr order72_S4ToD3Quot_range_top).trans Subgroup.topEquiv))

theorem order72_S4_quotV4_mulEquiv_D3_mk (s : order72_S4) :
    order72_S4_quotV4_mulEquiv_D3 ((QuotientGroup.mk' order72_S4_V4) s) =
      order72_S4ToD3Quot s := rfl

/-- The quotient identification `S₄/V₄ ≃ D₃` factoring `order72_S4ToS3`. -/
noncomputable def order72_S4_quotV4_mulEquiv_D3_of_S4ToS3 :
    order72_S4 ⧸ order72_S4_V4 ≃* DihedralGroup 3 :=
  (QuotientGroup.quotientMulEquivOfEq order72_S4ToS3_ker_eq_V4.symm).trans
    ((QuotientGroup.quotientKerEquivRange order72_S4ToS3).trans
      ((MulEquiv.subgroupCongr order72_S4ToS3_range_top).trans Subgroup.topEquiv))

theorem order72_S4_quotV4_mulEquiv_D3_of_S4ToS3_mk (s : order72_S4) :
    order72_S4_quotV4_mulEquiv_D3_of_S4ToS3 ((QuotientGroup.mk' order72_S4_V4) s) =
      order72_S4ToS3 s := rfl

/-- The two standard quotients `S₄ → D₃` differ by an automorphism of `D₃`. -/
noncomputable def order72_S4ToS3_twist : MulAut (DihedralGroup 3) :=
  order72_S4_quotV4_mulEquiv_D3.symm.trans order72_S4_quotV4_mulEquiv_D3_of_S4ToS3

theorem order72_S4ToS3_twist_apply (s : order72_S4) :
    order72_S4ToS3_twist (order72_S4ToD3Quot s) = order72_S4ToS3 s := by
  have h1 : order72_S4_quotV4_mulEquiv_D3.symm (order72_S4ToD3Quot s) =
      (QuotientGroup.mk' order72_S4_V4) s := by
    rw [← order72_S4_quotV4_mulEquiv_D3_mk s, MulEquiv.symm_apply_apply]
  rw [order72_S4ToS3_twist, MulEquiv.trans_apply, h1,
    order72_S4_quotV4_mulEquiv_D3_of_S4ToS3_mk]

end QuotientMaps

/-! ## The `D₉ → D₃` quotient -/

section D9Quotient

theorem order72_D9ToS3_apply_r (i : ZMod 9) :
    order72_D9ToS3 (DihedralGroup.r i) = DihedralGroup.r
      ((ZMod.castHom (by norm_num : 3 ∣ 9) (ZMod 3)).toAddMonoidHom i) := rfl

theorem order72_D9ToS3_apply_sr (i : ZMod 9) :
    order72_D9ToS3 (DihedralGroup.sr i) = DihedralGroup.sr
      ((ZMod.castHom (by norm_num : 3 ∣ 9) (ZMod 3)).toAddMonoidHom i) := rfl

theorem order72_D9ToS3_surjective : Function.Surjective order72_D9ToS3 := by
  intro y
  have h2 : ∀ j : ZMod 3,
      ((ZMod.castHom (by norm_num : 3 ∣ 9) (ZMod 3)).toAddMonoidHom
        ((j.val : ZMod 9))) = j := by
    intro j
    rw [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, ZMod.castHom_apply,
      ZMod.cast_eq_val, ZMod.val_natCast_of_lt (n := 9) (a := j.val)
        ((ZMod.val_lt j).trans (by norm_num)), ZMod.natCast_zmod_val]
  cases y with
  | r j => exact ⟨DihedralGroup.r ((j.val : ZMod 9)), by
      rw [order72_D9ToS3_apply_r, h2]⟩
  | sr j => exact ⟨DihedralGroup.sr ((j.val : ZMod 9)), by
      rw [order72_D9ToS3_apply_sr, h2]⟩

theorem order72_D9ToS3_range_top : order72_D9ToS3.range = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro d
  obtain ⟨x, hx⟩ := order72_D9ToS3_surjective d
  rw [MonoidHom.mem_range]
  exact ⟨x, hx⟩

theorem order72_D9ToS3_castHom_eq_zero_iff (i : ZMod 9) :
    (ZMod.castHom (by norm_num : 3 ∣ 9) (ZMod 3)).toAddMonoidHom i = 0 ↔
      3 ∣ i.val := by
  rw [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, ZMod.castHom_apply,
    ZMod.cast_eq_val]
  exact CharP.cast_eq_zero_iff (ZMod 3) 3 _

/-- The kernel of `D₉ → D₃` is the rotation subgroup `⟨r³⟩`. -/
theorem order72_D9ToS3_ker_eq_zpowers :
    order72_D9ToS3.ker = Subgroup.zpowers (DihedralGroup.r (3 : ZMod 9)) := by
  ext x
  constructor
  · intro hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_zpowers_iff]
    cases x with
    | r i =>
        rw [order72_D9ToS3_apply_r] at hx
        have hi0 : (ZMod.castHom (by norm_num : 3 ∣ 9) (ZMod 3)).toAddMonoidHom i = 0 := by
          have hri : DihedralGroup.r
              ((ZMod.castHom (by norm_num : 3 ∣ 9) (ZMod 3)).toAddMonoidHom i) =
            DihedralGroup.r (0 : ZMod 3) := by
            rw [hx, DihedralGroup.r_zero]
          rwa [DihedralGroup.r.injEq] at hri
        obtain ⟨k, hk⟩ := (order72_D9ToS3_castHom_eq_zero_iff i).mp hi0
        refine ⟨(k : ℤ), ?_⟩
        rw [DihedralGroup.r_zpow]
        have h3k : (3 : ZMod 9) * ((k : ℤ) : ZMod 9) = i := by
          rw [← ZMod.natCast_zmod_val i, hk]
          norm_cast
        rw [h3k]
    | sr i =>
        exfalso
        rw [order72_D9ToS3_apply_sr] at hx
        exact (by decide +kernel +revert : ∀ j : ZMod 3,
          (DihedralGroup.sr j : DihedralGroup 3) ≠ 1) _ hx
  · intro hx
    rw [Subgroup.mem_zpowers_iff] at hx
    obtain ⟨k, hk⟩ := hx
    rw [MonoidHom.mem_ker, ← hk, DihedralGroup.r_zpow, order72_D9ToS3_apply_r]
    have h3 : (ZMod.castHom (by norm_num : 3 ∣ 9) (ZMod 3)).toAddMonoidHom
        (3 : ZMod 9) = 0 := by
      rw [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, ZMod.castHom_apply,
        ZMod.cast_eq_val]
      decide
    have hmap : (ZMod.castHom (by norm_num : 3 ∣ 9) (ZMod 3)).toAddMonoidHom
        ((3 : ZMod 9) * ((k : ℤ) : ZMod 9)) = 0 := by
      rw [show (3 : ZMod 9) * ((k : ℤ) : ZMod 9) = k • (3 : ZMod 9) by
        rw [zsmul_eq_mul, mul_comm], map_zsmul, h3, smul_zero]
    rw [hmap, DihedralGroup.r_zero]

theorem order72_D9ToS3_ker_card : Nat.card order72_D9ToS3.ker = 3 := by
  have hv : ((3 : ZMod 9).val) = 3 := by decide
  rw [order72_D9ToS3_ker_eq_zpowers, Nat.card_zpowers, DihedralGroup.orderOf_r, hv]
  norm_num

/-- `D₉` has a unique subgroup of order `3`: the kernel of `D₉ → D₃`. -/
theorem order72_D9_subgroup_card_three_eq_D9ToS3_ker
    (U : Subgroup order72_D9) (hU : Nat.card U = 3) :
    U = order72_D9ToS3.ker := by
  apply Subgroup.eq_of_le_of_card_ge
  · intro x hx
    rw [MonoidHom.mem_ker]
    have hx3 : x ^ 3 = 1 := by
      have hdvd := orderOf_dvd_natCard (⟨x, hx⟩ : U)
      rw [hU] at hdvd
      have h2 : (⟨x, hx⟩ : U) ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
      have h3 := congrArg (fun y : U => (y : order72_D9)) h2
      simpa using h3
    cases x with
    | r i =>
        rw [order72_D9ToS3_apply_r]
        have hpow : (DihedralGroup.r i : DihedralGroup 9) ^ 3 = 1 := hx3
        rw [pow_succ, pow_succ, pow_one, DihedralGroup.r_mul_r,
          DihedralGroup.r_mul_r] at hpow
        have h30 : i * (3 : ZMod 9) = 0 := by
          have hri : DihedralGroup.r (i * (3 : ZMod 9)) =
              DihedralGroup.r (0 : ZMod 9) := by
            have hassoc : i * (3 : ZMod 9) = i + i + i := by ring
            rw [hassoc, hpow, DihedralGroup.r_zero]
          rwa [DihedralGroup.r.injEq] at hri
        have hφ0 : (ZMod.castHom (by norm_num : 3 ∣ 9) (ZMod 3)).toAddMonoidHom i = 0 := by
          rw [order72_D9ToS3_castHom_eq_zero_iff]
          have hdvd9 : 9 ∣ i.val * 3 := by
            have hv : (i * (3 : ZMod 9)).val = 0 := by rw [h30]; rfl
            rw [ZMod.val_mul, show ((3 : ZMod 9).val) = 3 from by decide] at hv
            exact Nat.dvd_of_mod_eq_zero hv
          obtain ⟨t, ht⟩ := hdvd9
          exact ⟨t, by omega⟩
        rw [hφ0, DihedralGroup.r_zero]
    | sr i =>
        exfalso
        have hpow : (DihedralGroup.sr i : DihedralGroup 9) ^ 3 = 1 := hx3
        have hsq : (DihedralGroup.sr i : DihedralGroup 9) ^ 2 = 1 := by
          rw [pow_two, DihedralGroup.sr_mul_sr, sub_self, DihedralGroup.r_zero]
        rw [pow_succ, hsq, one_mul] at hpow
        exact (by decide +kernel +revert : ∀ j : ZMod 9,
          (DihedralGroup.sr j : DihedralGroup 9) ≠ 1) i hpow
  · rw [hU, order72_D9ToS3_ker_card]

/-- The quotient identification `D₉/⟨r³⟩ ≃ D₃` factoring `order72_D9ToS3`. -/
noncomputable def order72_D9_quotKer_mulEquiv_D3 :
    order72_D9 ⧸ order72_D9ToS3.ker ≃* DihedralGroup 3 :=
  (QuotientGroup.quotientKerEquivRange order72_D9ToS3).trans
    ((MulEquiv.subgroupCongr order72_D9ToS3_range_top).trans Subgroup.topEquiv)

theorem order72_D9_quotKer_mulEquiv_D3_mk (x : order72_D9) :
    order72_D9_quotKer_mulEquiv_D3 ((QuotientGroup.mk' order72_D9ToS3.ker) x) =
      order72_D9ToS3 x := rfl

end D9Quotient

/-! ## Generic fiber tools -/

section FiberTools

/-- **Untwisting by an inner automorphism of `S₄`.**  Two fiber products of
`q : Q →* D₃` with `S₄ → D₃` that differ by a twist `σ ∈ Aut(D₃)` are isomorphic:
`Aut(D₃) = Inn(D₃)` and `S₄ → D₃` is surjective, so the twist is realised by
conjugation on the `S₄` factor. -/
theorem order72_S4_fiber_twist_mulEquiv {Q : Type*} [Group Q]
    (q : Q →* DihedralGroup 3) (σ : MulAut (DihedralGroup 3))
    {I F : Subgroup (order72_S4 × Q)}
    (hI : ∀ p, p ∈ I ↔ σ (order72_S4ToD3Quot p.1) = q p.2)
    (hF : ∀ p, p ∈ F ↔ order72_S4ToD3Quot p.1 = q p.2) :
    Nonempty (I ≃* F) := by
  obtain ⟨d, hd⟩ := order72_mulAut_conj_dihedral_three_surjective σ
  obtain ⟨u, hu⟩ := order72_S4ToD3Quot_surjective d
  have hσx : ∀ x : DihedralGroup 3, σ x = d * x * d⁻¹ := by
    intro x
    rw [← hd]
    rfl
  let Ψ : order72_S4 × Q ≃* order72_S4 × Q :=
    MulEquiv.prodCongr (MulAut.conj u) (MulEquiv.refl Q)
  have hmap : I.map Ψ.toMonoidHom = F := by
    ext p
    constructor
    · intro hp
      rw [Subgroup.mem_map] at hp
      obtain ⟨y, hy, hyx⟩ := hp
      rw [hF]
      have hyI := (hI y).mp hy
      rw [← hyx]
      change order72_S4ToD3Quot (Ψ y).1 = q (Ψ y).2
      change order72_S4ToD3Quot (u * y.1 * u⁻¹) = q y.2
      rw [map_mul, map_mul, map_inv, hu, ← hyI, hσx]
    · intro hp
      rw [Subgroup.mem_map]
      refine ⟨Ψ.symm p, ?_, ?_⟩
      · rw [hI]
        have hΨ : (Ψ.symm p).1 = u⁻¹ * p.1 * u := by
          change (MulAut.conj u⁻¹) p.1 = u⁻¹ * p.1 * u
          rfl
        change σ (order72_S4ToD3Quot (Ψ.symm p).1) = q (Ψ.symm p).2
        rw [hΨ]
        change σ (order72_S4ToD3Quot (u⁻¹ * p.1 * u)) = q p.2
        have hτ : order72_S4ToD3Quot (u⁻¹ * p.1 * u) =
            d⁻¹ * order72_S4ToD3Quot p.1 * d := by
          rw [map_mul, map_mul, map_inv, hu]
        rw [hτ, hσx]
        have hpF := (hF p).mp hp
        rw [← hpF]
        group
      · apply Prod.ext
        · change (MulAut.conj u) (u⁻¹ * p.1 * u) = p.1
          rw [MulAut.conj_apply]
          group
        · rfl
  exact ⟨(MulEquiv.subgroupMap Ψ I).trans (MulEquiv.subgroupCongr hmap)⟩

/-- **Goursat in fiber form.**  A Goursat subgroup of `S₄ × Q` with `goursatFst = V₄`
and `goursatSnd = q.ker` is the `σ`-twisted fiber of `q` for some `σ ∈ Aut(D₃)`. -/
theorem order72_goursat_fiber_mem_iff {Q : Type*} [Group Q]
    (I : Subgroup (order72_S4 × Q))
    (hI₁ : Function.Surjective (Prod.fst ∘ I.subtype))
    (hI₂ : Function.Surjective (Prod.snd ∘ I.subtype))
    (q : Q →* DihedralGroup 3) (hq_surj : Function.Surjective q)
    (hF : I.goursatFst = order72_S4_V4) (hS : I.goursatSnd = q.ker) :
    ∃ σ : MulAut (DihedralGroup 3),
      ∀ p, p ∈ I ↔ σ (order72_S4ToD3Quot p.1) = q p.2 := by
  haveI : I.goursatFst.Normal := Subgroup.normal_goursatFst hI₁
  haveI : I.goursatSnd.Normal := Subgroup.normal_goursatSnd hI₂
  haveI : q.ker.Normal := MonoidHom.normal_ker q
  obtain ⟨e, he⟩ := Subgroup.goursat_surjective hI₁ hI₂
  have hq_range : q.range = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro d
    obtain ⟨x, hx⟩ := hq_surj d
    rw [MonoidHom.mem_range]
    exact ⟨x, hx⟩
  let eQ : Q ⧸ q.ker ≃* DihedralGroup 3 :=
    (QuotientGroup.quotientKerEquivRange q).trans
      ((MulEquiv.subgroupCongr hq_range).trans Subgroup.topEquiv)
  have heQmk : ∀ x : Q, eQ ((QuotientGroup.mk' q.ker) x) = q x := fun x => rfl
  let eF : order72_S4 ⧸ order72_S4_V4 ≃* order72_S4 ⧸ I.goursatFst :=
    QuotientGroup.quotientMulEquivOfEq hF.symm
  let eS : Q ⧸ I.goursatSnd ≃* Q ⧸ q.ker := QuotientGroup.quotientMulEquivOfEq hS
  let σ : MulAut (DihedralGroup 3) :=
    ((order72_S4_quotV4_mulEquiv_D3.symm.trans eF).trans e).trans (eS.trans eQ)
  refine ⟨σ, fun p => ?_⟩
  have hkey : ∀ p : order72_S4 × Q,
      σ (order72_S4ToD3Quot p.1) = eQ (eS (e ((QuotientGroup.mk' I.goursatFst) p.1))) := by
    intro p
    have h1 : order72_S4_quotV4_mulEquiv_D3.symm (order72_S4ToD3Quot p.1) =
        (QuotientGroup.mk' order72_S4_V4) p.1 := by
      rw [← order72_S4_quotV4_mulEquiv_D3_mk p.1, MulEquiv.symm_apply_apply]
    change eQ (eS (e (eF (order72_S4_quotV4_mulEquiv_D3.symm (order72_S4ToD3Quot p.1))))) = _
    rw [h1]
    rw [show eF ((QuotientGroup.mk' order72_S4_V4) p.1) =
      (QuotientGroup.mk' I.goursatFst) p.1 from
      QuotientGroup.quotientMulEquivOfEq_mk hF.symm p.1]
  constructor
  · intro hp
    have hgraph : e ((QuotientGroup.mk' I.goursatFst) p.1) =
        (QuotientGroup.mk' I.goursatSnd) p.2 := by
      have hmem : (((QuotientGroup.mk' I.goursatFst).prodMap
          (QuotientGroup.mk' I.goursatSnd)).comp I.subtype) ⟨p, hp⟩ ∈
            e.toMonoidHom.graph := by
        rw [← he]
        exact ⟨⟨p, hp⟩, rfl⟩
      simpa [MonoidHom.mem_graph] using hmem
    rw [hkey, hgraph]
    change eQ (eS ((QuotientGroup.mk' I.goursatSnd) p.2)) = q p.2
    rw [show eS ((QuotientGroup.mk' I.goursatSnd) p.2) =
      (QuotientGroup.mk' q.ker) p.2 from QuotientGroup.quotientMulEquivOfEq_mk hS p.2,
      heQmk]
  · intro hq_eq
    have hgraph : e ((QuotientGroup.mk' I.goursatFst) p.1) =
        (QuotientGroup.mk' I.goursatSnd) p.2 := by
      have hσ : eQ (eS (e ((QuotientGroup.mk' I.goursatFst) p.1))) = q p.2 := by
        rw [← hkey]
        exact hq_eq
      have hright : eQ (eS ((QuotientGroup.mk' I.goursatSnd) p.2)) = q p.2 := by
        rw [show eS ((QuotientGroup.mk' I.goursatSnd) p.2) =
          (QuotientGroup.mk' q.ker) p.2 from
          QuotientGroup.quotientMulEquivOfEq_mk hS p.2, heQmk]
      apply eS.injective
      apply eQ.injective
      exact hσ.trans hright.symm
    have hmemGraph :
        ((QuotientGroup.mk' I.goursatFst).prodMap
          (QuotientGroup.mk' I.goursatSnd)) p ∈ e.toMonoidHom.graph := by
      simpa [MonoidHom.mem_graph] using hgraph
    have hmemRange :
        ((QuotientGroup.mk' I.goursatFst).prodMap
          (QuotientGroup.mk' I.goursatSnd)) p ∈
            (((QuotientGroup.mk' I.goursatFst).prodMap
              (QuotientGroup.mk' I.goursatSnd)).comp I.subtype).range := by
      rw [he]
      exact hmemGraph
    obtain ⟨y, hy⟩ := hmemRange
    rcases y with ⟨⟨a, b⟩, hyI⟩
    have hqa : (QuotientGroup.mk' I.goursatFst) p.1 =
        (QuotientGroup.mk' I.goursatFst) a := by
      exact congrArg Prod.fst hy.symm
    have hqb : (QuotientGroup.mk' I.goursatSnd) p.2 =
        (QuotientGroup.mk' I.goursatSnd) b := by
      exact congrArg Prod.snd hy.symm
    have haDiff : p.1 * a⁻¹ ∈ I.goursatFst := by
      have hraw : p.1⁻¹ * a ∈ I.goursatFst := QuotientGroup.eq.mp hqa
      have hrawInv : a⁻¹ * p.1 ∈ I.goursatFst := by
        simpa [div_eq_mul_inv] using I.goursatFst.inv_mem hraw
      have hconj := (inferInstance : I.goursatFst.Normal).conj_mem
        (a⁻¹ * p.1) hrawInv p.1
      simpa [mul_assoc] using hconj
    have hbDiff : p.2 * b⁻¹ ∈ I.goursatSnd := by
      have hraw : p.2⁻¹ * b ∈ I.goursatSnd := QuotientGroup.eq.mp hqb
      have hrawInv : b⁻¹ * p.2 ∈ I.goursatSnd := by
        simpa [div_eq_mul_inv] using I.goursatSnd.inv_mem hraw
      have hconj := (inferInstance : I.goursatSnd.Normal).conj_mem
        (b⁻¹ * p.2) hrawInv p.2
      simpa [mul_assoc] using hconj
    have hdiff : (p.1 * a⁻¹, p.2 * b⁻¹) ∈ I :=
      (Subgroup.goursatFst_prod_goursatSnd_le I) ⟨haDiff, hbDiff⟩
    have hprod : (p.1 * a⁻¹, p.2 * b⁻¹) * (a, b) = p := by
      ext <;> simp [mul_assoc]
    rw [← hprod]
    exact I.mul_mem hdiff hyI

end FiberTools

/-! ## The `RC = D₉` branch: `G ≃* C₃.S₄` -/

section RCBranch

/-- The standard fiber product of `S₄ → D₃` with `D₉ → D₃`, as a subgroup of
`S₄ × D₉`. -/
noncomputable def order72_S4_RC_fiber :
Subgroup (order72_S4 × Smallgroups.Classifications.Order18.RC) where
  carrier := { p | order72_S4ToD3Quot p.1 = order72_D9ToS3 p.2 }
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change order72_S4ToD3Quot (x.1 * y.1) = order72_D9ToS3 (x.2 * y.2)
    rw [map_mul, map_mul, hx, hy]
  inv_mem' := by
    intro x hx
    change order72_S4ToD3Quot x.1⁻¹ = order72_D9ToS3 x.2⁻¹
    rw [map_inv, map_inv, hx]

theorem order72_S4_RC_fiber_mem_iff (p : order72_S4 × Smallgroups.Classifications.Order18.RC) :
    p ∈ order72_S4_RC_fiber ↔ order72_S4ToD3Quot p.1 = order72_D9ToS3 p.2 := Iff.rfl

/-- The fiber product of the pairing-action quotient `S₄ → D₃` with `D₉ → D₃`:
the `C₃.S₄` representative written on `S₄ × D₉`. -/
noncomputable def order72_S4_RC_fiberS3 :
Subgroup (order72_S4 × Smallgroups.Classifications.Order18.RC) where
  carrier := { p | order72_S4ToS3 p.1 = order72_D9ToS3 p.2 }
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change order72_S4ToS3 (x.1 * y.1) = order72_D9ToS3 (x.2 * y.2)
    rw [map_mul, map_mul, hx, hy]
  inv_mem' := by
    intro x hx
    change order72_S4ToS3 x.1⁻¹ = order72_D9ToS3 x.2⁻¹
    rw [map_inv, map_inv, hx]

theorem order72_S4_RC_fiberS3_mem_iff (p : order72_S4 × Smallgroups.Classifications.Order18.RC) :
    p ∈ order72_S4_RC_fiberS3 ↔ order72_S4ToS3 p.1 = order72_D9ToS3 p.2 := Iff.rfl

/-- The `C₃.S₄` representative (a subgroup of `D₉ × S₄`) is the `S₃`-model fiber. -/
noncomputable def order72_res_C3S4_mulEquiv_fiberS3 :
    order72_res_C3S4 ≃* order72_S4_RC_fiberS3 where
  toFun x := ⟨(x.1.2, x.1.1), by
    obtain ⟨⟨d, s⟩, hx⟩ := x
    change order72_S4ToS3 s = order72_D9ToS3 d
    rw [order72_mem_res_C3S4_subgroup_iff] at hx
    exact (order72_perm3_to_d3.symm.injective hx).symm⟩
  invFun y := ⟨(y.1.2, y.1.1), by
    obtain ⟨⟨s, d⟩, hy⟩ := y
    change order72_S4ToS3 s = order72_D9ToS3 d at hy
    rw [order72_mem_res_C3S4_subgroup_iff]
    exact congrArg (⇑order72_perm3_to_d3.symm) hy.symm⟩
  left_inv := by
    intro x
    rcases x with ⟨⟨d, s⟩, hx⟩
    rfl
  right_inv := by
    intro y
    rcases y with ⟨⟨s, d⟩, hy⟩
    rfl
  map_mul' := by
    intro x y
    rfl

/-- The `D₉` standard fiber is the non-split representative `C₃.S₄`. -/
theorem order72_S4_RC_fiber_mulEquiv_res_C3S4 :
    Nonempty (order72_S4_RC_fiber ≃* order72_res_C3S4) := by
  obtain ⟨e⟩ := order72_S4_fiber_twist_mulEquiv order72_D9ToS3 order72_S4ToS3_twist
    (fun p => by
      rw [order72_S4_RC_fiberS3_mem_iff, ← order72_S4ToS3_twist_apply])
    order72_S4_RC_fiber_mem_iff
  exact ⟨e.symm.trans order72_res_C3S4_mulEquiv_fiberS3.symm⟩

/-- A Goursat subgroup of `S₄ × D₉` with `goursatFst = V₄` and `goursatSnd = ⟨r³⟩`
is the non-split representative `C₃.S₄`. -/
theorem order72_S4_RC_subgroup_mulEquiv_C3S4_of_goursat
    (I : Subgroup (order72_S4 × Smallgroups.Classifications.Order18.RC))
    (hI₁ : Function.Surjective (Prod.fst ∘ I.subtype))
    (hI₂ : Function.Surjective (Prod.snd ∘ I.subtype))
    (hF : I.goursatFst = order72_S4_V4)
    (hS : I.goursatSnd = order72_D9ToS3.ker) :
    Nonempty (I ≃* order72_res_C3S4) := by
  obtain ⟨σ, hσ⟩ := order72_goursat_fiber_mem_iff I hI₁ hI₂ order72_D9ToS3
    order72_D9ToS3_surjective hF hS
  obtain ⟨e1⟩ := order72_S4_fiber_twist_mulEquiv order72_D9ToS3 σ hσ
    order72_S4_RC_fiber_mem_iff
  obtain ⟨e2⟩ := order72_S4_RC_fiber_mulEquiv_res_C3S4
  exact ⟨e1.trans e2⟩

/-- The `RC = D₉` order-`18` quotient branch gives `G ≃* C₃.S₄`. -/
theorem order72_S4_RC_branch_mulEquiv_C3S4
    [Finite G] {K W : Subgroup G} [K.Normal] [W.Normal]
    (_hKW : K ≤ W) (_hKcard : Nat.card K = 3) {L : Subgroup W}
    (hLcomp : (K.subgroupOf W).IsComplement' L)
    [(L.map W.subtype : Subgroup G).Normal]
    (eS4 : G ⧸ K ≃* order72_S4)
    (eRC : G ⧸ (L.map W.subtype : Subgroup G) ≃*
      Smallgroups.Classifications.Order18.RC)
    (hL_le_V : ∀ {g : G}, g ∈ (L.map W.subtype : Subgroup G) →
      eS4 ((QuotientGroup.mk' K) g) ∈ order72_S4_V4)
    (hV_liftL : ∀ {a : order72_S4}, a ∈ order72_S4_V4 →
      ∃ g : G, g ∈ (L.map W.subtype : Subgroup G) ∧
        eS4 ((QuotientGroup.mk' K) g) = a)
    (hKimage : K.map (eRC.toMonoidHom.comp
      (QuotientGroup.mk' (L.map W.subtype : Subgroup G))) =
        order72_D9ToS3.ker) :
    Nonempty (G ≃* order72_res_C3S4) := by
  let N : Subgroup G := L.map W.subtype
  haveI : N.Normal := (inferInstance : (L.map W.subtype : Subgroup G).Normal)
  have hKN : Disjoint K N := by
    dsimp [N]
    exact order36_C3_layer_disjoint_klein_complement_map K W hLcomp
  let φ : G →* order72_S4 × Smallgroups.Classifications.Order18.RC :=
    (eS4.toMonoidHom.comp (QuotientGroup.mk' K)).prod
      (eRC.toMonoidHom.comp (QuotientGroup.mk' N))
  have hG_range : Nonempty (G ≃* φ.range) := by
    dsimp [φ]
    exact order72_two_quotient_product_range_mulEquiv K N hKN eS4 eRC
  have hproj := order72_two_quotient_product_range_proj_surjective K N eS4 eRC
  have hF : φ.range.goursatFst = order72_S4_V4 := by
    dsimp [φ]
    exact order72_two_quotient_product_range_goursatFst_eq_of_exact
      K N eS4 eRC order72_S4_V4 hL_le_V hV_liftL
  have hS : φ.range.goursatSnd = order72_D9ToS3.ker := by
    have hS0 := order72_two_quotient_product_range_goursatSnd_eq_K_image
      K N eS4 eRC
    dsimp [φ, N] at hS0 hKimage ⊢
    rw [hS0]
    exact hKimage
  obtain ⟨eGI⟩ := hG_range
  obtain ⟨eI⟩ :=
    order72_S4_RC_subgroup_mulEquiv_C3S4_of_goursat
      φ.range hproj.1 hproj.2 hF hS
  exact ⟨eGI.trans eI⟩

end RCBranch

/-! ## The `RE = (C₃)² ⋊₋₁ C₂` branch: `G ≃* C₃ ⋊[sign] S₄` -/

section REBranch

/-- The normal `C₃²` factor of `RE = (C₃)² ⋊₋₁ C₂`. -/
abbrev order72_RE_N : Type := Multiplicative (ZMod 3 × ZMod 3)

/-- The parity quotient `D₃ → C₂`: rotations are trivial, reflections are not. -/
noncomputable def order72_D3ToZMod2 : DihedralGroup 3 →* Multiplicative (ZMod 2) :=
  MonoidHom.mk'
    (fun x => match x with
      | DihedralGroup.r _ => 1
      | DihedralGroup.sr _ => Multiplicative.ofAdd 1)
    (by
      intro x y
      cases x <;> cases y <;>
        simp [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
          DihedralGroup.sr_mul_sr, ← ofAdd_add, show (1 + 1 : ZMod 2) = 0 from by decide])

theorem order72_D3ToZMod2_r (i : ZMod 3) :
    order72_D3ToZMod2 (DihedralGroup.r i) = 1 := rfl

theorem order72_D3ToZMod2_sr (i : ZMod 3) :
    order72_D3ToZMod2 (DihedralGroup.sr i) = Multiplicative.ofAdd 1 := rfl

theorem order72_D3ToZMod2_surjective : Function.Surjective order72_D3ToZMod2 := by
  intro y
  have hd : ∀ u : Multiplicative (ZMod 2), u = 1 ∨ u = Multiplicative.ofAdd 1 := by
    decide
  rcases hd y with rfl | rfl
  · exact ⟨DihedralGroup.r 0, order72_D3ToZMod2_r 0⟩
  · exact ⟨DihedralGroup.sr 0, order72_D3ToZMod2_sr 0⟩

/-- Two homomorphisms into `C₂` with the same kernel elements coincide. -/
theorem order72_hom_to_zmod2_eq_of_same_ker {H : Type*} [Group H]
    (f g : H →* Multiplicative (ZMod 2))
    (h : ∀ x, f x = 1 ↔ g x = 1) : f = g := by
  ext x
  have hd : ∀ u : Multiplicative (ZMod 2), u = 1 ∨ u = Multiplicative.ofAdd 1 := by
    decide
  rcases hd (f x) with hf | hf <;> rcases hd (g x) with hg | hg
  · rw [hf, hg]
  · exact absurd ((h x).mp hf) (by rw [hg]; decide)
  · exact absurd ((h x).mpr hg) (by rw [hf]; decide)
  · rw [hf, hg]

/-- The sign character `S₄ → (ℤ/3)ˣ` is trivial exactly on `A₄`. -/
theorem order72_signToZmod3_eq_one_iff (s : order72_S4) :
    order72_S4_signToZmod3 s = 1 ↔ Equiv.Perm.sign s = 1 := by
  constructor
  · intro h
    rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h1 | h1
    · exact h1
    · exfalso
      rw [order72_S4_signToZmod3, MonoidHom.comp_apply, h1] at h
      exact (by decide : (Units.map (Int.castRingHom (ZMod 3)).toMonoidHom) (-1 : ℤˣ) ≠ 1) h
  · intro h
    rw [order72_S4_signToZmod3, MonoidHom.comp_apply, h, map_one]

/-- The sign action of `S₄` on `C₃` is trivial exactly on `A₄`. -/
theorem order72_signAction_eq_one_iff (s : order72_S4) :
    order72_C3S4_signAction s = 1 ↔ s ∈ alternatingGroup (Fin 4) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [order72_C3S4_signAction, MonoidHom.comp_apply,
    ← map_one (unitAutHom (p := 3)), (unitAutHom_injective (p := 3)).eq_iff,
    order72_signToZmod3_eq_one_iff, Equiv.Perm.mem_alternatingGroup]

/-- The kernel of the parity quotient `S₄ → D₃ → C₂` is `A₄`. -/
theorem order72_D3ToZMod2_comp_S4ToD3Quot_ker :
    (order72_D3ToZMod2.comp order72_S4ToD3Quot).ker = alternatingGroup (Fin 4) := by
  apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
  rw [Subgroup.index_ker]
  have hsurj : Function.Surjective (order72_D3ToZMod2.comp order72_S4ToD3Quot) :=
    order72_D3ToZMod2_surjective.comp order72_S4ToD3Quot_surjective
  have hrange : (order72_D3ToZMod2.comp order72_S4ToD3Quot).range = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro u
    obtain ⟨s, hs⟩ := hsurj u
    rw [MonoidHom.mem_range]
    exact ⟨s, hs⟩
  rw [hrange, Nat.card_congr Subgroup.topEquiv.toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_multiplicative, ZMod.card]

theorem order72_D3ToZMod2_S4ToD3Quot_eq_one_iff (s : order72_S4) :
    order72_D3ToZMod2 (order72_S4ToD3Quot s) = 1 ↔ s ∈ alternatingGroup (Fin 4) := by
  change ((order72_D3ToZMod2.comp order72_S4ToD3Quot) s = 1) ↔ _
  rw [← MonoidHom.mem_ker, order72_D3ToZMod2_comp_S4ToD3Quot_ker]

/-- Elements of the `C₃²` factor of `RE` have order dividing `3`. -/
theorem order72_RE_left_pow_three (a : order72_RE_N) : a ^ 3 = 1 := by
  obtain ⟨z, rfl⟩ := Multiplicative.ofAdd.surjective a
  rw [← ofAdd_nsmul, show (3 : ℕ) • z = (0 : ZMod 3 × ZMod 3) from by
    apply Prod.ext
    · change (3 : ℕ) • z.1 = 0
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    · change (3 : ℕ) • z.2 = 0
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul], ofAdd_zero]

/-- A nonidentity element of `Multiplicative (ZMod 3)` has order `3`. -/
theorem order72_ofAdd_zmod3_orderOf_eq_three {a : ZMod 3} (ha : a ≠ 0) :
    orderOf (Multiplicative.ofAdd a) = 3 := by
  have h3 : (Multiplicative.ofAdd a) ^ 3 = 1 := by
    rw [← ofAdd_nsmul, show (3 : ℕ) • a = (0 : ZMod 3) from by
      rw [nsmul_eq_mul, CharP.cast_eq_zero (ZMod 3) 3, zero_mul], ofAdd_zero]
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp (orderOf_dvd_of_pow_eq_one h3) with h | h
  · exfalso
    rw [orderOf_eq_one_iff] at h
    exact ha (congrArg Multiplicative.toAdd h)
  · exact h

/-- A subgroup of `RE` of order `3` lies in the `C₃²` factor. -/
theorem order72_RE_order_three_subgroup_le_leftpart (N' :
Subgroup Smallgroups.Classifications.Order18.RE)
    (hN' : Nat.card N' = 3) :
    N' ≤ (SemidirectProduct.rightHom.ker : Subgroup Smallgroups.Classifications.Order18.RE) := by
  intro x hx
  rw [MonoidHom.mem_ker]
  have hx3 : x ^ 3 = 1 := by
    have hdvd := orderOf_dvd_natCard (⟨x, hx⟩ : N')
    rw [hN'] at hdvd
    have h2 : (⟨x, hx⟩ : N') ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
    have h3 := congrArg (fun y : N' => (y : Smallgroups.Classifications.Order18.RE)) h2
    simpa using h3
  have hr3 : (SemidirectProduct.rightHom x) ^ 3 = 1 := by
    rw [← map_pow, hx3, map_one]
  have hd : ∀ u : Multiplicative (ZMod 2), u ^ 3 = 1 → u = 1 := by decide
  exact hd _ hr3

/-- For any order-`3` subgroup of the `C₃²` factor, some coordinate projection
meets it trivially. -/
theorem order72_RE_exists_projection_inf_bot (N'' : Subgroup order72_RE_N)
    (hN'' : Nat.card N'' = 3) :
    ∃ ρ : order72_RE_N →* order72_C3, N'' ⊓ ρ.ker = ⊥ := by
  haveI : Nontrivial ↥N'' := by
    rw [← Finite.one_lt_card_iff_nontrivial, hN'']
    norm_num
  obtain ⟨g, hg⟩ := exists_ne (1 : ↥N'')
  have hordg : orderOf (g : order72_RE_N) = 3 := by
    have hdvd : orderOf (g : ↥N'') ∣ 3 := by
      have h := orderOf_dvd_natCard g
      rwa [hN''] at h
    rw [Subgroup.orderOf_mk] at hdvd
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
    · exfalso
      rw [orderOf_eq_one_iff] at h
      exact hg (Subtype.ext h)
    · exact h
  have hN''eq : Subgroup.zpowers (g : order72_RE_N) = N'' := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact Subgroup.zpowers_le.mpr g.2
    · rw [Nat.card_zpowers, hordg, hN'']
  obtain ⟨z, hz⟩ := Multiplicative.ofAdd.surjective (g : order72_RE_N)
  rw [← hz] at hordg hN''eq
  have hz0 : z ≠ 0 := by
    intro h
    apply hg
    apply Subtype.ext
    rw [← hz, h]
    rfl
  have hz12 : z.1 ≠ 0 ∨ z.2 ≠ 0 := by
    by_contra h
    push Not at h
    exact hz0 (Prod.ext h.1 h.2)
  have key : ∀ (ρ : order72_RE_N →* order72_C3) (w : order72_RE_N),
      ρ (Multiplicative.ofAdd z) ≠ 1 →
      w ∈ Subgroup.zpowers (Multiplicative.ofAdd z) → w ∈ ρ.ker → w = 1 := by
    intro ρ w hρ hwz hwk
    rw [Subgroup.mem_zpowers_iff] at hwz
    obtain ⟨k, hk⟩ := hwz
    rw [MonoidHom.mem_ker, ← hk, map_zpow] at hwk
    have hordρ : orderOf (ρ (Multiplicative.ofAdd z)) = 3 := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp
        (orderOf_dvd_of_pow_eq_one
          (show (ρ (Multiplicative.ofAdd z)) ^ 3 = 1 from by
            rw [← map_pow, order72_RE_left_pow_three, map_one])) with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hρ
      · exact h
    have h3k : (3 : ℤ) ∣ k := by
      have h := orderOf_dvd_iff_zpow_eq_one.mpr hwk
      rw [hordρ] at h
      exact_mod_cast h
    rw [← hk]
    have h3k' : (orderOf (Multiplicative.ofAdd z) : ℤ) ∣ k := by
      rw [hordg]
      exact_mod_cast h3k
    exact orderOf_dvd_iff_zpow_eq_one.mp h3k'
  rcases hz12 with hz1 | hz1
  · refine ⟨(AddMonoidHom.fst (ZMod 3) (ZMod 3)).toMultiplicative, ?_⟩
    rw [← hN''eq, Subgroup.eq_bot_iff_forall]
    intro w hw
    rw [Subgroup.mem_inf] at hw
    exact key _ w (by
      have hne : (AddMonoidHom.fst (ZMod 3) (ZMod 3)).toMultiplicative
          (Multiplicative.ofAdd z) = Multiplicative.ofAdd z.1 := rfl
      rw [hne]
      intro h1
      exact hz1 (congrArg Multiplicative.toAdd h1)) hw.1 hw.2
  · refine ⟨(AddMonoidHom.snd (ZMod 3) (ZMod 3)).toMultiplicative, ?_⟩
    rw [← hN''eq, Subgroup.eq_bot_iff_forall]
    intro w hw
    rw [Subgroup.mem_inf] at hw
    exact key _ w (by
      have hne : (AddMonoidHom.snd (ZMod 3) (ZMod 3)).toMultiplicative
          (Multiplicative.ofAdd z) = Multiplicative.ofAdd z.2 := rfl
      rw [hne]
      intro h1
      exact hz1 (congrArg Multiplicative.toAdd h1)) hw.1 hw.2

/-- The parity component of `RE` factors through any `D₃` quotient by an order-`3`
subgroup of the `C₃²` factor. -/
theorem order72_RE_c2U_comp_q_eq_rightHom
(N' : Subgroup Smallgroups.Classifications.Order18.RE) [N'.Normal]
    (hN' : Nat.card N' = 3) (e : Smallgroups.Classifications.Order18.RE ⧸ N' ≃* DihedralGroup 3) :
    (order72_D3ToZMod2.comp (e.toMonoidHom.comp (QuotientGroup.mk' N'))) =
      SemidirectProduct.rightHom := by
  apply order72_hom_to_zmod2_eq_of_same_ker
  intro x
  have hleft : N' ≤ (SemidirectProduct.rightHom.ker :
  Subgroup Smallgroups.Classifications.Order18.RE) :=
    order72_RE_order_three_subgroup_le_leftpart N' hN'
  constructor
  · intro h
    by_contra hr
    have hd : ∀ u : Multiplicative (ZMod 2), u = 1 ∨ u = Multiplicative.ofAdd 1 := by
      decide
    have hx2 : x ^ 2 = 1 := by
      rcases hd (SemidirectProduct.rightHom x) with h1 | h1
      · exact absurd h1 hr
      · have hxr : x.right = Multiplicative.ofAdd 1 := by
          rw [← SemidirectProduct.rightHom_eq_right]
          exact h1
        apply SemidirectProduct.ext
        · rw [pow_two, SemidirectProduct.mul_left, hxr, invActionHom_gen, invAut_apply,
            mul_inv_cancel]
          rfl
        · rw [pow_two, SemidirectProduct.mul_right, hxr, ← ofAdd_add,
            show (1 + 1 : ZMod 2) = 0 from by decide, ofAdd_zero]
          rfl
    have hqx2 : ((e.toMonoidHom.comp (QuotientGroup.mk' N')) x) ^ 2 = 1 := by
      rw [← map_pow, hx2, map_one]
    have hq1 : (e.toMonoidHom.comp (QuotientGroup.mk' N')) x = 1 := by
      cases hq : (e.toMonoidHom.comp (QuotientGroup.mk' N')) x with
      | r i =>
          rw [hq] at hqx2
          have hi : i + i = 0 := by
            have hri : DihedralGroup.r (i + i) = DihedralGroup.r (0 : ZMod 3) := by
              rw [← DihedralGroup.r_mul_r, ← pow_two, hqx2, DihedralGroup.r_zero]
            rwa [DihedralGroup.r.injEq] at hri
          have hi0 : i = 0 := by
            have h2 : (2 : ZMod 3) * i = 0 := by rw [two_mul]; exact hi
            rcases mul_eq_zero.mp h2 with h2 | h2
            · exact absurd h2 (by decide)
            · exact h2
          rw [hi0, DihedralGroup.r_zero]
      | sr i =>
          exfalso
          rw [hq] at hqx2
          rw [MonoidHom.comp_apply, hq, order72_D3ToZMod2_sr] at h
          exact (by decide : (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) ≠ 1) h
    have hxN : x ∈ N' := by
      have hmk : (QuotientGroup.mk' N') x = 1 := by
        rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← map_one e] at hq1
        exact e.injective hq1
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmk
    exact hr ((MonoidHom.mem_ker).mp (hleft hxN))
  · intro h
    change order72_D3ToZMod2 ((e.toMonoidHom.comp (QuotientGroup.mk' N')) x) = 1
    have hxr : x.right = 1 := by
      rw [← SemidirectProduct.rightHom_eq_right, h]
    have hxinl : x = SemidirectProduct.inl x.left := by
      have h2 := SemidirectProduct.inl_left_mul_inr_right x
      rw [hxr, map_one, mul_one] at h2
      exact h2.symm
    have hqx3 : ((e.toMonoidHom.comp (QuotientGroup.mk' N')) x) ^ 3 = 1 := by
      rw [← map_pow, hxinl, ← map_pow, order72_RE_left_pow_three, map_one, map_one]
    cases hq : (e.toMonoidHom.comp (QuotientGroup.mk' N')) x with
    | r i =>
        exact order72_D3ToZMod2_r i
    | sr i =>
        exfalso
        rw [hq] at hqx3
        have hsq : (DihedralGroup.sr i : DihedralGroup 3) ^ 2 = 1 := by
          rw [pow_two, DihedralGroup.sr_mul_sr, sub_self, DihedralGroup.r_zero]
        rw [pow_succ, hsq, one_mul] at hqx3
        exact (by decide +kernel +revert : ∀ j : ZMod 3,
          (DihedralGroup.sr j : DihedralGroup 3) ≠ 1) i hqx3

/-- The action compatibility along the fiber: the `C₂` part of `x ∈ RE` and the sign
of `s ∈ S₄` induce the same action on `C₃` when `τ s = q x`. -/
theorem order72_RE_action_compatible
(N' : Subgroup Smallgroups.Classifications.Order18.RE) [N'.Normal]
    (hN' : Nat.card N' = 3) (e : Smallgroups.Classifications.Order18.RE ⧸ N' ≃* DihedralGroup 3)
    {s : order72_S4} {x : Smallgroups.Classifications.Order18.RE}
    (h : order72_S4ToD3Quot s = (e.toMonoidHom.comp (QuotientGroup.mk' N')) x)
    (ρ : order72_RE_N →* order72_C3) (y : order72_RE_N) :
    ρ ((invActionHom order72_RE_N) x.right y) =
      order72_C3S4_signAction s (ρ y) := by
  have hc2 : order72_D3ToZMod2 (order72_S4ToD3Quot s) = x.right := by
    have h1 : order72_D3ToZMod2 (order72_S4ToD3Quot s) =
        SemidirectProduct.rightHom x := by
      rw [h, ← MonoidHom.comp_apply, order72_RE_c2U_comp_q_eq_rightHom N' hN' e]
    rw [SemidirectProduct.rightHom_eq_right] at h1
    exact h1
  have hd : ∀ u : Multiplicative (ZMod 2), u = 1 ∨ u = Multiplicative.ofAdd 1 := by
    decide
  rcases hd x.right with ht | ht
  · rw [ht, map_one]
    have hs : order72_C3S4_signAction s = 1 := by
      rw [order72_signAction_eq_one_iff, ← order72_D3ToZMod2_S4ToD3Quot_eq_one_iff]
      rw [hc2, ht]
    rw [hs]
    rfl
  · rw [ht, invActionHom_gen, invAut_apply, map_inv]
    have hsign : Equiv.Perm.sign s = -1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h1 | h1
      · exfalso
        have hA4 : s ∈ alternatingGroup (Fin 4) := Equiv.Perm.mem_alternatingGroup.mpr h1
        rw [← order72_D3ToZMod2_S4ToD3Quot_eq_one_iff] at hA4
        rw [hc2, ht] at hA4
        exact (by decide : (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) ≠ 1) hA4
      · exact h1
    obtain ⟨m, hm⟩ := Multiplicative.ofAdd.surjective (ρ y)
    rw [← hm, order72_C3S4_signAction, MonoidHom.comp_apply, order72_S4_signToZmod3,
      MonoidHom.comp_apply, hsign, unitAutHom_apply]
    have hu : (Units.map (Int.castRingHom (ZMod 3)).toMonoidHom) (-1 : ℤˣ) =
        (-1 : (ZMod 3)ˣ) := by
      apply Units.ext
      decide
    rw [hu, show ((-1 : (ZMod 3)ˣ) : ZMod 3) = -1 from rfl, neg_one_mul, ofAdd_neg]

/-- The standard fiber product of `S₄ → D₃` with `RE → D₃`, as a subgroup of
`S₄ × RE`. -/
noncomputable def order72_S4_RE_fiber
(q : Smallgroups.Classifications.Order18.RE →* DihedralGroup 3) :
    Subgroup (order72_S4 × Smallgroups.Classifications.Order18.RE) where
  carrier := { p | order72_S4ToD3Quot p.1 = q p.2 }
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change order72_S4ToD3Quot (x.1 * y.1) = q (x.2 * y.2)
    rw [map_mul, map_mul, hx, hy]
  inv_mem' := by
    intro x hx
    change order72_S4ToD3Quot x.1⁻¹ = q x.2⁻¹
    rw [map_inv, map_inv, hx]

theorem order72_S4_RE_fiber_mem_iff (q : Smallgroups.Classifications.Order18.RE →* DihedralGroup 3)
    (p : order72_S4 × Smallgroups.Classifications.Order18.RE) :
    p ∈ order72_S4_RE_fiber q ↔ order72_S4ToD3Quot p.1 = q p.2 := Iff.rfl

/-- The `RE` standard fiber is the split representative `C₃ ⋊[sign] S₄`. -/
theorem order72_S4_RE_fiber_mulEquiv_C3sS4
(N' : Subgroup Smallgroups.Classifications.Order18.RE) [N'.Normal]
    (hN' : Nat.card N' = 3) (e : Smallgroups.Classifications.Order18.RE ⧸ N' ≃* DihedralGroup 3) :
    Nonempty (order72_S4_RE_fiber (e.toMonoidHom.comp (QuotientGroup.mk' N')) ≃*
      order72_res_C3sS4) := by
  let q : Smallgroups.Classifications.Order18.RE →* DihedralGroup 3 :=
  e.toMonoidHom.comp (QuotientGroup.mk' N')
  have hqker : q.ker = N' := by
    ext x
    rw [MonoidHom.mem_ker]
    change ((e.toMonoidHom.comp (QuotientGroup.mk' N')) x = 1) ↔ x ∈ N'
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← map_one e,
      e.injective.eq_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hq_surj : Function.Surjective q :=
    e.surjective.comp (QuotientGroup.mk'_surjective N')
  have hleft : N' ≤ (SemidirectProduct.rightHom.ker :
  Subgroup Smallgroups.Classifications.Order18.RE) :=
    order72_RE_order_three_subgroup_le_leftpart N' hN'
  -- the left projection on the `C₃²` part
  let leftRes : ↥(SemidirectProduct.rightHom.ker :
  Subgroup Smallgroups.Classifications.Order18.RE) →* order72_RE_N := {
    toFun := fun x => x.1.left
    map_one' := rfl
    map_mul' := by
      intro x y
      have hx : x.1.right = 1 := by
        have := x.2
        rw [MonoidHom.mem_ker, SemidirectProduct.rightHom_eq_right] at this
        exact this
      change (x.1 * y.1).left = x.1.left * y.1.left
      rw [SemidirectProduct.mul_left, hx, map_one]
      simp }
  have hleftRes_inj : Function.Injective leftRes := by
    intro x y hxy
    apply Subtype.ext
    apply SemidirectProduct.ext
    · exact hxy
    · have hx : x.1.right = 1 := by
        have := x.2
        rw [MonoidHom.mem_ker, SemidirectProduct.rightHom_eq_right] at this
        exact this
      have hy : y.1.right = 1 := by
        have := y.2
        rw [MonoidHom.mem_ker, SemidirectProduct.rightHom_eq_right] at this
        exact this
      rw [hx, hy]
  let N'' : Subgroup order72_RE_N :=
    (N'.subgroupOf (SemidirectProduct.rightHom.ker :
    Subgroup Smallgroups.Classifications.Order18.RE)).map leftRes
  have hN''card : Nat.card N'' = 3 := by
    have h1 : Nat.card ↥N'' =
        Nat.card ↥(N'.subgroupOf (SemidirectProduct.rightHom.ker :
        Subgroup Smallgroups.Classifications.Order18.RE)) :=
      Subgroup.card_map_of_injective hleftRes_inj
    have h2 : Nat.card ↥(N'.subgroupOf (SemidirectProduct.rightHom.ker :
        Subgroup Smallgroups.Classifications.Order18.RE)) = Nat.card ↥N' :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hleft).toEquiv
    rw [h1, h2, hN']
  obtain ⟨ρ, hρ⟩ := order72_RE_exists_projection_inf_bot N'' hN''card
  -- the candidate homomorphism
  haveI : ∀ p, Decidable (p ∈ order72_S4_RE_fiber q) :=
    fun p => decidable_of_iff (order72_S4ToD3Quot p.1 = q p.2) Iff.rfl
  haveI : Fintype Smallgroups.Classifications.Order18.RE :=
    Fintype.ofEquiv _ SemidirectProduct.equivProd.symm
  haveI : Fintype ↥(order72_S4_RE_fiber q) := Subtype.fintype _
  haveI : Fintype order72_res_C3sS4 := Fintype.ofEquiv _ SemidirectProduct.equivProd.symm
  let θ : ↥(order72_S4_RE_fiber q) →* order72_res_C3sS4 :=
    MonoidHom.mk'
      (fun p => ⟨ρ p.1.2.left, p.1.1⟩)
      (by
        intro a b
        obtain ⟨⟨sa, xa⟩, ha⟩ := a
        obtain ⟨⟨sb, xb⟩, hb⟩ := b
        apply SemidirectProduct.ext
        · change ρ ((xa * xb).left) =
            ρ xa.left * order72_C3S4_signAction sa (ρ xb.left)
          rw [SemidirectProduct.mul_left, map_mul,
            order72_RE_action_compatible N' hN' e
              (show order72_S4ToD3Quot sa =
                (e.toMonoidHom.comp (QuotientGroup.mk' N')) xa from ha) ρ xb.left]
        · rfl)
  have hθinj : Function.Injective θ := by
    refine (injective_iff_map_eq_one θ).mpr ?_
    intro a ha
    obtain ⟨⟨s, x⟩, hx⟩ := a
    have hs : s = 1 := by
      have h1 := congrArg SemidirectProduct.right ha
      exact h1
    have hxN' : x ∈ N' := by
      have hqx : q x = 1 := by
        have hxmem : order72_S4ToD3Quot s = q x := hx
        rw [hs, map_one] at hxmem
        exact hxmem.symm
      rw [← hqker]
      rwa [MonoidHom.mem_ker]
    have hxright : x.right = 1 := by
      have := hleft hxN'
      rw [MonoidHom.mem_ker, SemidirectProduct.rightHom_eq_right] at this
      exact this
    have hxlN'' : x.left ∈ N'' := by
      rw [Subgroup.mem_map]
      refine ⟨⟨x, hleft hxN'⟩, ?_, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      exact hxN'
    have hxl1 : x.left = 1 := by
      have h1 : x.left ∈ N'' ⊓ ρ.ker := by
        rw [Subgroup.mem_inf]
        refine ⟨hxlN'', ?_⟩
        rw [MonoidHom.mem_ker]
        have h2 := congrArg SemidirectProduct.left ha
        exact h2
      rw [hρ] at h1
      exact h1
    have hx1 : x = 1 := SemidirectProduct.ext hxl1 hxright
    exact Subtype.ext (Prod.ext hs hx1)
  -- cardinality for bijectivity
  let π₁ : ↥(order72_S4_RE_fiber q) →* order72_S4 :=
    (MonoidHom.fst order72_S4
    Smallgroups.Classifications.Order18.RE).comp (order72_S4_RE_fiber q).subtype
  have hπ₁range : π₁.range = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro s
    rw [MonoidHom.mem_range]
    obtain ⟨x, hx⟩ := hq_surj (order72_S4ToD3Quot s)
    exact ⟨⟨(s, x), hx.symm⟩, rfl⟩
  have hker3 : Nat.card ↥π₁.ker = 3 := by
    let ε : ↥q.ker ≃ ↥π₁.ker := {
      toFun := fun x => ⟨⟨(1, x), by
        change order72_S4ToD3Quot 1 = q x
        rw [map_one]
        exact ((MonoidHom.mem_ker).mp x.2).symm⟩, by
        rw [MonoidHom.mem_ker]
        rfl⟩
      invFun := fun y => ⟨(y.1.1.2), by
        have hmem : order72_S4ToD3Quot y.1.1.1 = q y.1.1.2 := y.1.2
        have hy2 := y.2
        rw [MonoidHom.mem_ker] at hy2
        have h11 : y.1.1.1 = 1 := hy2
        rw [h11, map_one] at hmem
        exact (MonoidHom.mem_ker).mpr hmem.symm⟩
      left_inv := fun x => rfl
      right_inv := by
        intro y
        obtain ⟨⟨⟨s, x⟩, hmem⟩, hker⟩ := y
        rw [MonoidHom.mem_ker] at hker
        have hker2 : s = 1 := hker
        subst hker2
        rfl }
    calc Nat.card ↥π₁.ker = Nat.card ↥q.ker := Nat.card_congr ε.symm
      _ = Nat.card ↥N' := Nat.card_congr (MulEquiv.subgroupCongr hqker).toEquiv
      _ = 3 := hN'
  have hcardF72 : Nat.card ↥(order72_S4_RE_fiber q) = 72 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup π₁.ker
    have hquot : Nat.card (↥(order72_S4_RE_fiber q) ⧸ π₁.ker) = 24 := by
      have h1 : Nat.card (↥(order72_S4_RE_fiber q) ⧸ π₁.ker) =
          Nat.card ↥(⊤ : Subgroup order72_S4) :=
        Nat.card_congr ((QuotientGroup.quotientKerEquivRange π₁).trans
          (MulEquiv.subgroupCongr hπ₁range)).toEquiv
      have h2 : Nat.card ↥(⊤ : Subgroup order72_S4) = Nat.card order72_S4 :=
        Nat.card_congr Subgroup.topEquiv.toEquiv
      rw [h1, h2, Nat.card_perm, Nat.card_fin]
      norm_num [Nat.factorial]
    rw [hquot, hker3] at h
    omega
  have hbij : Function.Bijective θ :=
    (Fintype.bijective_iff_injective_and_card θ).mpr ⟨hθinj, by
      rw [← Nat.card_eq_fintype_card, hcardF72, ← Nat.card_eq_fintype_card,
        card_order72_res_C3sS4]⟩
  exact ⟨MulEquiv.ofBijective θ hbij⟩

/-- A Goursat subgroup of `S₄ × RE` with `goursatFst = V₄` and an order-`3`
`goursatSnd` is the split representative `C₃ ⋊[sign] S₄`. -/
theorem order72_S4_RE_subgroup_mulEquiv_C3sS4_of_goursat
    (I : Subgroup (order72_S4 × Smallgroups.Classifications.Order18.RE))
    (hI₁ : Function.Surjective (Prod.fst ∘ I.subtype))
    (hI₂ : Function.Surjective (Prod.snd ∘ I.subtype))
    (hF : I.goursatFst = order72_S4_V4)
    (N' : Subgroup Smallgroups.Classifications.Order18.RE) [N'.Normal]
    (hN'card : Nat.card N' = 3)
    (hS : I.goursatSnd = N')
    (e : Smallgroups.Classifications.Order18.RE ⧸ N' ≃* DihedralGroup 3) :
    Nonempty (I ≃* order72_res_C3sS4) := by
  let q : Smallgroups.Classifications.Order18.RE →* DihedralGroup 3 :=
    e.toMonoidHom.comp (QuotientGroup.mk' N')
  have hqker : q.ker = N' := by
    ext x
    rw [MonoidHom.mem_ker]
    change ((e.toMonoidHom.comp (QuotientGroup.mk' N')) x = 1) ↔ x ∈ N'
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← map_one e,
      e.injective.eq_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hq_surj : Function.Surjective q :=
    e.surjective.comp (QuotientGroup.mk'_surjective N')
  obtain ⟨σ, hσ⟩ := order72_goursat_fiber_mem_iff I hI₁ hI₂ q hq_surj hF
    (by rw [hS, hqker])
  obtain ⟨e1⟩ := order72_S4_fiber_twist_mulEquiv q σ hσ
    (order72_S4_RE_fiber_mem_iff q)
  obtain ⟨e2⟩ := order72_S4_RE_fiber_mulEquiv_C3sS4 N' hN'card e
  exact ⟨e1.trans e2⟩

/-- The quotient of `RE` by a normal order-`3` subgroup is `D₃`: it has order `6`
and is nonabelian. -/
theorem order72_RE_quotient_order_three_mulEquiv_D3
    (N' : Subgroup Smallgroups.Classifications.Order18.RE) [N'.Normal]
    (hN' : Nat.card N' = 3) :
    Nonempty (Smallgroups.Classifications.Order18.RE ⧸ N' ≃* DihedralGroup 3) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcard : Nat.card (Smallgroups.Classifications.Order18.RE ⧸ N') = 6 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N'
    rw [hN', card_R5 3] at h
    omega
  have hnotcomm : ¬ ∀ a b : Smallgroups.Classifications.Order18.RE ⧸ N',
      a * b = b * a := by
    intro hcomm
    have hex : ∃ n₀ : order72_RE_N, SemidirectProduct.inl n₀ ∉ N' := by
      by_contra hall
      push Not at hall
      haveI : Finite ↥N' := Nat.finite_of_card_ne_zero (by rw [hN']; norm_num)
      have hcardle : Nat.card order72_RE_N ≤ Nat.card ↥N' :=
        Nat.card_le_card_of_injective
          (fun n => (⟨SemidirectProduct.inl n, hall n⟩ : ↥N'))
          (fun a b hab => SemidirectProduct.inl_injective (Subtype.ext_iff.mp hab))
      have hcard9 : Nat.card order72_RE_N = 9 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_prod,
          ZMod.card]
      rw [hN', hcard9] at hcardle
      norm_num at hcardle
    obtain ⟨n₀, hn₀⟩ := hex
    let t : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1
    have hmem : SemidirectProduct.inl (n₀ ^ 2) ∈ N' := by
      have hq := hcomm ((QuotientGroup.mk' N') (SemidirectProduct.inr t))
        ((QuotientGroup.mk' N') (SemidirectProduct.inl n₀))
      rw [← map_mul, ← map_mul] at hq
      have hmemN : (SemidirectProduct.inr t * SemidirectProduct.inl n₀)⁻¹ *
          (SemidirectProduct.inl n₀ * SemidirectProduct.inr t) ∈ N' :=
        QuotientGroup.eq.mp hq
      have hcompute : ((SemidirectProduct.inr t * SemidirectProduct.inl n₀)⁻¹ *
          (SemidirectProduct.inl n₀ * SemidirectProduct.inr t) :
          Smallgroups.Classifications.Order18.RE) =
          SemidirectProduct.inl (n₀⁻¹ * n₀⁻¹) := by
        have ht2 : t⁻¹ = t := by
          change (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2))⁻¹ =
            (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2))
          decide
        apply SemidirectProduct.ext
        · simp [ht2, SemidirectProduct.mul_left, SemidirectProduct.inv_left,
            SemidirectProduct.left_inl, SemidirectProduct.left_inr,
            SemidirectProduct.right_inl, SemidirectProduct.right_inr, t,
            invActionHom_gen, invAut_apply]
        · simp [ht2, SemidirectProduct.mul_right, SemidirectProduct.inv_right,
            SemidirectProduct.right_inl, SemidirectProduct.right_inr, t,
            ← ofAdd_add, show (1 + 1 : ZMod 2) = 0 from by decide]
      rw [hcompute] at hmemN
      have hmeminv := N'.inv_mem hmemN
      rw [← map_inv] at hmeminv
      have hpos : (n₀⁻¹ * n₀⁻¹)⁻¹ = n₀ ^ 2 := by
        rw [mul_inv_rev, inv_inv, pow_two]
      rwa [hpos] at hmeminv
    have hn0mem : SemidirectProduct.inl n₀ ∈ N' := by
      have h4 : (SemidirectProduct.inl n₀) ^ 4 ∈ N' := by
        have hsq4 : (SemidirectProduct.inl n₀ : Smallgroups.Classifications.Order18.RE) ^ 4 =
            (SemidirectProduct.inl (n₀ ^ 2)) ^ 2 := by
          rw [← map_pow, ← map_pow, ← pow_mul]
        rw [hsq4]
        exact N'.pow_mem hmem 2
      have h4eq : (SemidirectProduct.inl n₀ : Smallgroups.Classifications.Order18.RE) ^ 4 =
          SemidirectProduct.inl n₀ := by
        rw [← map_pow, pow_succ, order72_RE_left_pow_three, one_mul]
      rwa [h4eq] at h4
    exact hn₀ hn0mem
  rcases Smallgroups.Classifications.Order6.classification hcard with hcyc | hdih
  · obtain ⟨e⟩ := hcyc
    exact False.elim (hnotcomm (by
      intro a b
      apply e.injective
      rw [map_mul, map_mul, mul_comm]))
  · exact hdih

end REBranch

/-! ## Assembly of the order-`3` kernel branch -/

section Assembly

/-- The image of a normal order-`3` kernel in any quotient by a disjoint normal
subgroup still has order `3`. -/
theorem order72_K_image_card_eq_three {Q : Type*} [Group Q]
    (K N : Subgroup G) [N.Normal] (hKcard : Nat.card K = 3)
    (hKA : Disjoint K N) (eQ : G ⧸ N ≃* Q) :
    Nat.card (K.map (eQ.toMonoidHom.comp (QuotientGroup.mk' N))) = 3 := by
  let f : G →* Q := eQ.toMonoidHom.comp (QuotientGroup.mk' N)
  let ψ : K →* Q := f.comp K.subtype
  have hψ_inj : Function.Injective ψ := by
    refine (injective_iff_map_eq_one ψ).mpr ?_
    intro x hx
    have hxA : (x : G) ∈ N := by
      have hq : (QuotientGroup.mk' N) (x : G) = 1 := by
        apply eQ.injective
        simpa [ψ, f] using hx
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hq
    have hxbot : (x : G) ∈ (⊥ : Subgroup G) :=
      (disjoint_iff_inf_le.mp hKA) ⟨x.property, hxA⟩
    exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
  have hψrange : ψ.range = K.map f := by
    ext z
    constructor
    · intro hz
      rw [MonoidHom.mem_range] at hz
      obtain ⟨x, hx⟩ := hz
      rw [Subgroup.mem_map]
      exact ⟨(x : G), x.property, by simpa [ψ, f] using hx⟩
    · intro hz
      rw [Subgroup.mem_map] at hz
      obtain ⟨g, hgK, hgz⟩ := hz
      rw [MonoidHom.mem_range]
      exact ⟨⟨g, hgK⟩, by simpa [ψ, f] using hgz⟩
  rw [← hψrange]
  have hcard : Nat.card K = Nat.card (ψ.range : Subgroup Q) :=
    Nat.card_congr (Equiv.ofInjective ψ hψ_inj)
  rw [← hcard, hKcard]

/-- In the `RD = D₃ × C₃` quotient branch, the kernel image is the central `C₃`
factor (not the rotation subgroup): otherwise `G ⧸ W` would be commutative. -/
theorem order72_RD_K_image_eq_centralKernel
    [Finite G] {K W : Subgroup G} [K.Normal] [W.Normal]
    (hKW : K ≤ W) (hKcard : Nat.card K = 3) (hWcard : Nat.card W = 12)
    {L : Subgroup W} (hLcomp : (K.subgroupOf W).IsComplement' L)
    (hLcard : Nat.card L = 4)
    [(L.map W.subtype : Subgroup G).Normal]
    (hGW : Nonempty (G ⧸ W ≃* DihedralGroup 3))
    (eRD : G ⧸ (L.map W.subtype : Subgroup G) ≃*
      Smallgroups.Classifications.Order18.RD) :
    K.map (eRD.toMonoidHom.comp (QuotientGroup.mk' (L.map W.subtype : Subgroup G))) =
      order72_RD_centralKernel := by
  let N : Subgroup G := L.map W.subtype
  haveI : N.Normal := (inferInstance : (L.map W.subtype : Subgroup G).Normal)
  have hNW : N ≤ W := Subgroup.map_subtype_le L
  have hNcard : Nat.card N = 4 := order36_klein_complement_map_card W hLcard
  have hKN : Disjoint K N := order36_C3_layer_disjoint_klein_complement_map K W hLcomp
  have hUcard : Nat.card (K.map (eRD.toMonoidHom.comp (QuotientGroup.mk' N))) = 3 := by
    dsimp [N]
    exact order72_K_image_card_eq_three K (L.map W.subtype) hKcard hKN eRD
  have hUnormal : (K.map (eRD.toMonoidHom.comp (QuotientGroup.mk' N))).Normal :=
    (inferInstance : K.Normal).map _ (eRD.surjective.comp (QuotientGroup.mk'_surjective N))
  haveI := hUnormal
  have hWmapcard : Nat.card (W.map (eRD.toMonoidHom.comp (QuotientGroup.mk' N))) = 3 := by
    have hmapmap : W.map (eRD.toMonoidHom.comp (QuotientGroup.mk' N)) =
        (W.map (QuotientGroup.mk' N)).map eRD.toMonoidHom := by
      rw [Subgroup.map_map]
    rw [hmapmap, Subgroup.card_map_of_injective eRD.injective]
    let φ : ↥W →* G ⧸ N := (QuotientGroup.mk' N).comp W.subtype
    have hφker : φ.ker = N.subgroupOf W := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
      change (QuotientGroup.mk' N) (x : G) = 1 ↔ (x : G) ∈ N
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hφrange : φ.range = W.map (QuotientGroup.mk' N) := by
      ext z
      rw [MonoidHom.mem_range]
      constructor
      · rintro ⟨w, rfl⟩
        rw [Subgroup.mem_map]
        exact ⟨(w : G), w.2, rfl⟩
      · intro hz
        rw [Subgroup.mem_map] at hz
        obtain ⟨g, hgW, hgz⟩ := hz
        exact ⟨⟨g, hgW⟩, hgz⟩
    have hcardW : Nat.card ↥W = Nat.card (↥W ⧸ φ.ker) * Nat.card ↥φ.ker :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    have hquotcard : Nat.card (↥W ⧸ φ.ker) = Nat.card ↥φ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    have hkercard : Nat.card ↥φ.ker = 4 := by
      rw [hφker]
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNW).toEquiv).trans hNcard
    have h12 : 12 = Nat.card ↥φ.range * 4 := by
      rw [hquotcard, hkercard, hWcard] at hcardW
      exact hcardW
    have hr3 : Nat.card ↥φ.range = 3 := by omega
    rw [← hφrange, hr3]
  have hKleW : K.map (eRD.toMonoidHom.comp (QuotientGroup.mk' N)) ≤
      W.map (eRD.toMonoidHom.comp (QuotientGroup.mk' N)) := Subgroup.map_mono hKW
  have hWeq : W.map (eRD.toMonoidHom.comp (QuotientGroup.mk' N)) =
      K.map (eRD.toMonoidHom.comp (QuotientGroup.mk' N)) :=
    (Subgroup.eq_of_le_of_card_ge hKleW (le_of_eq (by rw [hWmapcard, hUcard]))).symm
  rcases order72_RD_normal_order_three_eq_rotation_or_central _ hUcard with hrot | hcent
  · exfalso
    haveI : (W.map (QuotientGroup.mk' N)).Normal :=
      (inferInstance : W.Normal).map _ (QuotientGroup.mk'_surjective N)
    let e1 : (G ⧸ N) ⧸ (W.map (QuotientGroup.mk' N)) ≃* G ⧸ W :=
      QuotientGroup.quotientQuotientEquivQuotient N W hNW
    let ψ : G ⧸ N →* Smallgroups.Classifications.Order18.RD ⧸
        (K.map (eRD.toMonoidHom.comp (QuotientGroup.mk' N))) :=
      (QuotientGroup.mk' (K.map (eRD.toMonoidHom.comp (QuotientGroup.mk' N)))).comp
        eRD.toMonoidHom
    have hψsurj : Function.Surjective ψ :=
      (QuotientGroup.mk'_surjective _).comp eRD.surjective
    have hψrange : ψ.range = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro z
      obtain ⟨x, hx⟩ := hψsurj z
      rw [MonoidHom.mem_range]
      exact ⟨x, hx⟩
    have hψker : ψ.ker = W.map (QuotientGroup.mk' N) := by
      ext x
      rw [MonoidHom.mem_ker]
      change (QuotientGroup.mk' (K.map (eRD.toMonoidHom.comp (QuotientGroup.mk' N))))
          (eRD x) = 1 ↔ x ∈ W.map (QuotientGroup.mk' N)
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← hWeq,
        ← Subgroup.map_map]
      exact Subgroup.mem_map_iff_mem eRD.injective
    let e2 : (G ⧸ N) ⧸ (W.map (QuotientGroup.mk' N)) ≃*
        Smallgroups.Classifications.Order18.RD ⧸
          (K.map (eRD.toMonoidHom.comp (QuotientGroup.mk' N))) :=
      (QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
        ((QuotientGroup.quotientKerEquivRange ψ).trans
          ((MulEquiv.subgroupCongr hψrange).trans Subgroup.topEquiv))
    haveI : order72_RD_rotationKernel.Normal := order72_RD_rotationKernel_normal
    have hcomm : ∀ a b : G ⧸ W, a * b = b * a := by
      intro a b
      let eT := e1.symm.trans (e2.trans (QuotientGroup.quotientMulEquivOfEq hrot))
      have h := order72_RD_rotationKernel_quotient_comm (eT a) (eT b)
      apply eT.injective
      simpa [eT, map_mul] using h
    obtain ⟨eD3⟩ := hGW
    have hD3not : ¬ ∀ a b : DihedralGroup 3, a * b = b * a := by decide +kernel
    exact hD3not (fun a b => by
      have hcomm2 := hcomm (eD3.symm a) (eD3.symm b)
      apply eD3.symm.injective
      simpa [map_mul] using hcomm2)
  · exact hcent

/-- The `RE = (C₃)² ⋊₋₁ C₂` order-`18` quotient branch gives `G ≃* C₃ ⋊[sign] S₄`. -/
theorem order72_S4_RE_branch_mulEquiv_C3sS4
    [Finite G] {K W : Subgroup G} [K.Normal] [W.Normal]
    (_hKW : K ≤ W) (hKcard : Nat.card K = 3) {L : Subgroup W}
    (hLcomp : (K.subgroupOf W).IsComplement' L)
    [(L.map W.subtype : Subgroup G).Normal]
    (eS4 : G ⧸ K ≃* order72_S4)
    (eRE : G ⧸ (L.map W.subtype : Subgroup G) ≃*
      Smallgroups.Classifications.Order18.RE)
    (hL_le_V : ∀ {g : G}, g ∈ (L.map W.subtype : Subgroup G) →
      eS4 ((QuotientGroup.mk' K) g) ∈ order72_S4_V4)
    (hV_liftL : ∀ {a : order72_S4}, a ∈ order72_S4_V4 →
      ∃ g : G, g ∈ (L.map W.subtype : Subgroup G) ∧
        eS4 ((QuotientGroup.mk' K) g) = a) :
    Nonempty (G ≃* order72_res_C3sS4) := by
  let N : Subgroup G := L.map W.subtype
  haveI : N.Normal := (inferInstance : (L.map W.subtype : Subgroup G).Normal)
  have hKN : Disjoint K N := by
    dsimp [N]
    exact order36_C3_layer_disjoint_klein_complement_map K W hLcomp
  let φ : G →* order72_S4 × Smallgroups.Classifications.Order18.RE :=
    (eS4.toMonoidHom.comp (QuotientGroup.mk' K)).prod
      (eRE.toMonoidHom.comp (QuotientGroup.mk' N))
  have hG_range : Nonempty (G ≃* φ.range) := by
    dsimp [φ]
    exact order72_two_quotient_product_range_mulEquiv K N hKN eS4 eRE
  have hproj := order72_two_quotient_product_range_proj_surjective K N eS4 eRE
  have hF : φ.range.goursatFst = order72_S4_V4 := by
    dsimp [φ]
    exact order72_two_quotient_product_range_goursatFst_eq_of_exact
      K N eS4 eRE order72_S4_V4 hL_le_V hV_liftL
  have hS : φ.range.goursatSnd = K.map (eRE.toMonoidHom.comp (QuotientGroup.mk' N)) := by
    dsimp [φ, N]
    exact order72_two_quotient_product_range_goursatSnd_eq_K_image K N eS4 eRE
  have hN'card : Nat.card (K.map (eRE.toMonoidHom.comp (QuotientGroup.mk' N))) = 3 := by
    dsimp [N]
    exact order72_K_image_card_eq_three K (L.map W.subtype) hKcard hKN eRE
  have hN'normal : (K.map (eRE.toMonoidHom.comp (QuotientGroup.mk' N))).Normal :=
    (inferInstance : K.Normal).map _ (eRE.surjective.comp (QuotientGroup.mk'_surjective N))
  haveI := hN'normal
  obtain ⟨eN'⟩ := order72_RE_quotient_order_three_mulEquiv_D3 _ hN'card
  obtain ⟨eGI⟩ := hG_range
  obtain ⟨eI⟩ := order72_S4_RE_subgroup_mulEquiv_C3sS4_of_goursat
    φ.range hproj.1 hproj.2 hF _ hN'card hS eN'
  exact ⟨eGI.trans eI⟩

/-- **The order-`3` kernel branch.**  A group of order `72` with `G ⧸ K ≃ S₄` for a
normal kernel `K` of order `3` is one of `C₃.S₄`, `C₃ × S₄`, `C₃ ⋊[sign] S₄`. -/
theorem order72_S4_quotient_branch_repCases [Finite G]
    (hG : Nat.card G = 72) (K : Subgroup G) [K.Normal] (hK : Nat.card K = 3)
    (hquot : Nonempty (G ⧸ K ≃* order72_S4)) :
    Nonempty (G ≃* order72_res_C3S4) ∨ Nonempty (G ≃* order72_res_C3xS4) ∨
      Nonempty (G ≃* order72_res_C3sS4) := by
  obtain ⟨eS4⟩ := hquot
  obtain ⟨W, hWnormal, hKW, hWcard, hKcenterW, hGWquot, hpowW, L, hLcomp, hLcard,
    hLleV, hVLiftL⟩ :=
    order72_S4_equiv_klein_preimage_central_complement (G := G) hG K hK eS4
  haveI : W.Normal := hWnormal
  have hLnormal : (L.map W.subtype : Subgroup G).Normal :=
    order72_klein_complement_map_normal_of_center_preimage hKcenterW hKW hK hLcomp hpowW
  have hLmapcard : Nat.card (L.map W.subtype : Subgroup G) = 4 :=
    order36_klein_complement_map_card W hLcard
  haveI : (L.map W.subtype : Subgroup G).Normal := hLnormal
  have hquot18 : Nat.card (G ⧸ (L.map W.subtype : Subgroup G)) = 18 := by
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (L.map W.subtype)
    rw [hG, hLmapcard] at hcard
    omega
  have hQcases := Smallgroups.Classifications.Order18.classification hquot18
  have hAW : (L.map W.subtype : Subgroup G) ≤ W := Subgroup.map_subtype_le L
  have hnotRA := order72_not_order18_RA_quotient_of_D3_layer hAW hGWquot
  have hnotRB := order72_not_order18_RB_quotient_of_D3_layer hAW hGWquot
  rcases hQcases with hRA | hRB | hRC | hRD | hRE
  · exact False.elim (hnotRA hRA)
  · exact False.elim (hnotRB hRB)
  · obtain ⟨eRC⟩ := hRC
    have hKN : Disjoint K (L.map W.subtype : Subgroup G) :=
      order36_C3_layer_disjoint_klein_complement_map K W hLcomp
    have hKimage : K.map (eRC.toMonoidHom.comp
        (QuotientGroup.mk' (L.map W.subtype : Subgroup G))) = order72_D9ToS3.ker :=
      order72_D9_subgroup_card_three_eq_D9ToS3_ker _
        (order72_K_image_card_eq_three K (L.map W.subtype : Subgroup G) hK hKN eRC)
    exact Or.inl (order72_S4_RC_branch_mulEquiv_C3S4 hKW hK hLcomp eS4 eRC
      (fun hg => hLleV hg) (fun ha => hVLiftL ha) hKimage)
  · obtain ⟨eRD⟩ := hRD
    have hKimage := order72_RD_K_image_eq_centralKernel hKW hK hWcard hLcomp hLcard
      hGWquot eRD
    exact Or.inr (Or.inl (order72_S4_RD_branch_mulEquiv_C3xS4_of_central_kernel
      hKW hK hLcomp eS4 eRD (fun hg => hLleV hg) (fun ha => hVLiftL ha) hKimage))
  · obtain ⟨eRE⟩ := hRE
    exact Or.inr (Or.inr (order72_S4_RE_branch_mulEquiv_C3sS4 hKW hK hLcomp eS4 eRE
      (fun hg => hLleV hg) (fun ha => hVLiftL ha)))

/-- **The residual kernel analysis identifies the representative.**  This eliminates
the axiom `order72_residual_kernel_cases_to_repCases` from `Classification.lean`. -/
theorem order72_residual_kernel_cases_to_repCases [Finite G]
    (hG : Nat.card G = 72) (hker : order72ResidualKernelCases G) :
    order72ResidualRepCases G := by
  rcases hker with ⟨hSyl2, hψcases⟩
  rcases hψcases with ⟨ψ, hψ⟩
  rcases hψ with hψ3 | hψ6
  · have hquot : Nonempty (G ⧸ ψ.ker ≃* order72_S4) :=
      order72_quotient_ker_mulEquiv_S4_of_range_top ψ hψ3.2
    rcases order72_S4_quotient_branch_repCases hG ψ.ker hψ3.1 hquot with h1 | h2 | h3
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
  · exact order72_kernel_order_six_branch_repCases hG hSyl2 ψ hψ6.1 hψ6.2

end Assembly

end Smallgroups.UsefulTheorems
