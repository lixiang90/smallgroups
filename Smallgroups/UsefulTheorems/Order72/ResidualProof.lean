/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order72.Residual
import Smallgroups.UsefulTheorems.Order36
import Smallgroups.UsefulTheorems.PGroupGeneration.CentralExtension
import Smallgroups.Classifications.Classifications_1_to_10.Order6
import Smallgroups.Classifications.Classifications_11_to_20.Order18

/-!
# Elimination of the residual-kernel-to-representative axiom

This file proves `order72_residual_kernel_cases_to_repCases` (the last open assumption of the
order-`72` classification) by analysing the kernel `K` of the permutation action `ψ` of `G` on
its four Sylow `3`-subgroups:

* `|K| = 6`  =>  `G ≃* S₃ × A₄`                                  (Stage 1);
* `|K| = 3`  =>  `G ≃* C₃.S₄`, `C₃ × S₄` or `C₃ ⋊[sign] S₄`      (Stage 2).

The two stages are assembled in `order72_residual_kernel_cases_to_repCases` at the end.
-/

namespace Smallgroups.UsefulTheorems

open P3Group

variable {G : Type} [Group G]

/-! ## Quotient interfaces for the two residual kernel branches -/

section QuotientInterfaces

/-- If the residual action has full image `S₄`, its kernel quotient is `S₄`. -/
theorem order72_quotient_ker_mulEquiv_S4_of_range_top
    (ψ : G →* Equiv.Perm (Fin 4)) (hψrange : ψ.range = ⊤) :
    Nonempty (G ⧸ ψ.ker ≃* order72_S4) := by
  exact ⟨((QuotientGroup.quotientKerEquivRange ψ).trans
    (MulEquiv.subgroupCongr hψrange)).trans Subgroup.topEquiv⟩

/-- If the residual action has image `A₄`, its kernel quotient is `A₄`. -/
theorem order72_quotient_ker_mulEquiv_A4_of_range_alt
    (ψ : G →* Equiv.Perm (Fin 4)) (hψrange : ψ.range = alternatingGroup (Fin 4)) :
    Nonempty (G ⧸ ψ.ker ≃* alternatingGroup (Fin 4)) := by
  exact ⟨(QuotientGroup.quotientKerEquivRange ψ).trans
    (MulEquiv.subgroupCongr hψrange)⟩

/-- A packaged form of the two quotient conclusions contained in
`order72ResidualKernelCases`. -/
theorem order72_residual_kernel_cases_quotient_cases [Finite G]
    (hker : order72ResidualKernelCases G) :
    (∃ ψ : G →* Equiv.Perm (Fin 4),
        Nat.card ψ.ker = 3 ∧ ψ.range = ⊤ ∧ Nonempty (G ⧸ ψ.ker ≃* order72_S4)) ∨
      (∃ ψ : G →* Equiv.Perm (Fin 4),
        Nat.card ψ.ker = 6 ∧ ψ.range = alternatingGroup (Fin 4) ∧
          Nonempty (G ⧸ ψ.ker ≃* alternatingGroup (Fin 4))) := by
  rcases hker.2 with ⟨ψ, hψ⟩
  rcases hψ with hψ3 | hψ6
  · exact Or.inl ⟨ψ, hψ3.1, hψ3.2,
      order72_quotient_ker_mulEquiv_S4_of_range_top ψ hψ3.2⟩
  · exact Or.inr ⟨ψ, hψ6.1, hψ6.2,
      order72_quotient_ker_mulEquiv_A4_of_range_alt ψ hψ6.2⟩

end QuotientInterfaces

/-! ## Stage 1: `|K| = 6` implies `G ≃* S₃ × A₄` -/

section Stage1

/-- `A₄` has no normal subgroup of order `3`. -/
theorem order72_A4_no_normal_subgroup_order_three
    (N : Subgroup (alternatingGroup (Fin 4))) [N.Normal] : Nat.card N ≠ 3 := by
  intro hN
  have hA4 : Nat.card (alternatingGroup (Fin 4)) = 12 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  have hquot : Nat.card (alternatingGroup (Fin 4) ⧸ N) = 4 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hN, hA4] at h
    omega
  have hquot_sq : Nat.card (alternatingGroup (Fin 4) ⧸ N) = 2 ^ 2 := by
    rw [hquot]
    norm_num
  haveI : IsMulCommutative (alternatingGroup (Fin 4) ⧸ N) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hquot_sq
  have hcomm : commutator (alternatingGroup (Fin 4)) ≤ N :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  have hklein : alternatingGroup.kleinFour (Fin 4) ≤ N := by
    simpa [alternatingGroup.kleinFour_eq_commutator (α := Fin 4) (by simp)] using hcomm
  have hV : Nat.card (alternatingGroup.kleinFour (Fin 4)) = 4 := by
    simpa using alternatingGroup.kleinFour_card_of_card_eq_four (α := Fin 4) (by simp)
  have hdvd : Nat.card (alternatingGroup.kleinFour (Fin 4)) ∣ Nat.card N :=
    Subgroup.card_dvd_of_le hklein
  rw [hV, hN] at hdvd
  norm_num at hdvd

/-- The center of `S₃`, represented as `DihedralGroup 3`, is trivial. -/
theorem order72_center_dihedral_three_eq_bot :
    Subgroup.center (DihedralGroup 3) = ⊥ := by
  exact DihedralGroup.center_eq_bot_of_odd_ne_one (by exact ⟨1, by norm_num⟩ : Odd 3)
    (by norm_num : (3 : ℕ) ≠ 1)

/-- `Aut(S₃)` has order `6`, with `S₃` represented as `DihedralGroup 3`. -/
theorem order72_card_mulAut_dihedral_three :
    Nat.card (MulAut (DihedralGroup 3)) = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- The conjugation map `S₃ → Aut(S₃)` is injective. -/
theorem order72_mulAut_conj_dihedral_three_injective :
    Function.Injective (MulAut.conj : DihedralGroup 3 →* MulAut (DihedralGroup 3)) := by
  intro a b hab
  have h : MulAut.conj (a * b⁻¹) = 1 := by
    rw [map_mul, hab, map_inv, mul_inv_cancel]
  have hc : a * b⁻¹ ∈ Subgroup.center (DihedralGroup 3) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hx := congrArg (fun φ : MulAut (DihedralGroup 3) => φ x) h
    rw [MulAut.conj_apply] at hx
    calc
      x * (a * b⁻¹) = ((a * b⁻¹) * x * (a * b⁻¹)⁻¹) * (a * b⁻¹) := by
        rw [hx]
        simp
      _ = (a * b⁻¹) * x := by group
  rw [order72_center_dihedral_three_eq_bot] at hc
  have hab1 : a * b⁻¹ = 1 := Subgroup.mem_bot.mp hc
  exact eq_of_mul_inv_eq_one hab1

/-- Every automorphism of `S₃` is inner. -/
theorem order72_mulAut_conj_dihedral_three_surjective :
    Function.Surjective (MulAut.conj : DihedralGroup 3 →* MulAut (DihedralGroup 3)) := by
  classical
  have hbij :
      Function.Bijective (MulAut.conj : DihedralGroup 3 →* MulAut (DihedralGroup 3)) :=
    (Fintype.bijective_iff_injective_and_card
      (MulAut.conj : DihedralGroup 3 →* MulAut (DihedralGroup 3))).mpr
      ⟨order72_mulAut_conj_dihedral_three_injective, by
        rw [DihedralGroup.card, ← Nat.card_eq_fintype_card,
          order72_card_mulAut_dihedral_three]⟩
  exact hbij.surjective

/-- Any subgroup isomorphic to `S₃` has trivial center. -/
theorem order72_center_subgroup_eq_bot_of_mulEquiv_dihedral_three {K : Subgroup G}
    (e : K ≃* DihedralGroup 3) :
    Subgroup.center K = ⊥ := by
  have hcard : Nat.card (Subgroup.center K) = 1 := by
    exact (card_center_eq_of_mulEquiv e).trans
      (card_center_of_eq_bot order72_center_dihedral_three_eq_bot)
  exact Subgroup.eq_bot_of_card_eq _ hcard

/-- An `S₃` subgroup meets its ambient centralizer trivially. -/
theorem order72_inf_centralizer_eq_bot_of_mulEquiv_dihedral_three {K : Subgroup G}
    (e : K ≃* DihedralGroup 3) :
    K ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
  apply le_antisymm
  · intro x hx
    have hxK : x ∈ K := hx.1
    have hxC : x ∈ Subgroup.centralizer (K : Set G) := hx.2
    have hxcent : (⟨x, hxK⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hcomm := (Subgroup.mem_centralizer_iff.mp hxC) (y : G) y.2
      exact Subtype.ext hcomm
    have hxbot : (⟨x, hxK⟩ : K) ∈ (⊥ : Subgroup K) := by
      rwa [← order72_center_subgroup_eq_bot_of_mulEquiv_dihedral_three e]
    have hx1 : x = 1 := congrArg Subtype.val (Subgroup.mem_bot.mp hxbot)
    simp [hx1]
  · exact bot_le

/-- If `K ≃ S₃` is normal, every element of `G` differs by an element of `K` from
an element centralizing `K`. -/
theorem order72_exists_kernel_translate_mem_centralizer_of_dihedral_kernel
    {K : Subgroup G} [K.Normal] (e : K ≃* DihedralGroup 3) (g : G) :
    ∃ k : K, (k : G)⁻¹ * g ∈ Subgroup.centralizer (K : Set G) := by
  let α : MulAut (DihedralGroup 3) :=
    e.symm.trans ((MulAut.conjNormal (H := K) g).trans e)
  obtain ⟨d, hd⟩ := order72_mulAut_conj_dihedral_three_surjective α
  let k : K := e.symm d
  refine ⟨k, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hxK
  let xK : K := ⟨x, hxK⟩
  have happ := congrArg (fun φ : MulAut (DihedralGroup 3) => φ (e xK)) hd
  have hleft : (MulAut.conj d) (e xK) = e (k * xK * k⁻¹) := by
    simp [k, MulAut.conj_apply]
  have hright : α (e xK) = e ((MulAut.conjNormal (H := K) g) xK) := by
    simp [α]
  have heq : e (k * xK * k⁻¹) = e ((MulAut.conjNormal (H := K) g) xK) := by
    rw [← hleft, happ, hright]
  have hK : k * xK * k⁻¹ = (MulAut.conjNormal (H := K) g) xK := e.injective heq
  have hG : (k : G) * x * (k : G)⁻¹ = g * x * g⁻¹ := congrArg Subtype.val hK
  calc
    x * ((k : G)⁻¹ * g) = (k : G)⁻¹ * ((k : G) * x * (k : G)⁻¹) * g := by group
    _ = (k : G)⁻¹ * (g * x * g⁻¹) * g := by rw [hG]
    _ = ((k : G)⁻¹ * g) * x := by group

/-- A normal `S₃` subgroup splits off from the ambient group as a direct product with
its centralizer. -/
theorem order72_mulEquiv_prod_centralizer_of_dihedral_kernel
    {K : Subgroup G} [K.Normal] (e : K ≃* DihedralGroup 3) :
    Nonempty (G ≃* K × Subgroup.centralizer (K : Set G)) := by
  let C : Subgroup G := Subgroup.centralizer (K : Set G)
  have hcomm : ∀ k : K, ∀ c : C, Commute ((K.subtype) k) (C.subtype c) := by
    intro k c
    rw [commute_iff_eq]
    exact (Subgroup.mem_centralizer_iff.mp c.2) (k : G) k.2
  let Φ : K × C →* G := K.subtype.noncommCoprod C.subtype hcomm
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_one Φ).mpr ?_
    rintro ⟨k, c⟩ hkc
    change (k : G) * (c : G) = 1 at hkc
    have hk_eq_cinv : (k : G) = (c : G)⁻¹ := eq_inv_of_mul_eq_one_left hkc
    have hk_inf : (k : G) ∈ K ⊓ C := by
      exact ⟨k.2, by rw [hk_eq_cinv]; exact C.inv_mem c.2⟩
    have hk_bot : (k : G) ∈ (⊥ : Subgroup G) := by
      rwa [← order72_inf_centralizer_eq_bot_of_mulEquiv_dihedral_three e]
    have hk1 : (k : G) = 1 := Subgroup.mem_bot.mp hk_bot
    have hc1 : (c : G) = 1 := by
      rw [hk1, one_mul] at hkc
      exact hkc
    apply Prod.ext
    · exact Subtype.ext hk1
    · exact Subtype.ext hc1
  have hsurj : Function.Surjective Φ := by
    intro g
    obtain ⟨k, hkC⟩ := order72_exists_kernel_translate_mem_centralizer_of_dihedral_kernel e g
    refine ⟨(k, ⟨(k : G)⁻¹ * g, hkC⟩), ?_⟩
    change (k : G) * ((k : G)⁻¹ * g) = g
    group
  exact ⟨(MulEquiv.ofBijective Φ ⟨hinj, hsurj⟩).symm⟩

/-- The `|K| = 6`, `K ≃ S₃` residual branch gives the representative `S₃ × A₄`. -/
theorem order72_dihedral_kernel_branch_mulEquiv_S3xA4 [Finite G]
    (hG : Nat.card G = 72) (ψ : G →* Equiv.Perm (Fin 4))
    (hψker : Nat.card ψ.ker = 6)
    (hψrange : ψ.range = alternatingGroup (Fin 4))
    (hKiso : Nonempty (ψ.ker ≃* DihedralGroup 3)) :
    Nonempty (G ≃* order72_res_S3xA4) := by
  obtain ⟨eK⟩ := hKiso
  let C : Subgroup G := Subgroup.centralizer (ψ.ker : Set G)
  obtain ⟨eprod⟩ := order72_mulEquiv_prod_centralizer_of_dihedral_kernel eK
  have hcardC : Nat.card C = 12 := by
    have h := Nat.card_congr eprod.toEquiv
    rw [hG, Nat.card_prod, hψker] at h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 6)
      (h.symm.trans (by norm_num : 72 = 6 * 12))
  let φC0 : C →* Equiv.Perm (Fin 4) := ψ.comp C.subtype
  let φC : C →* alternatingGroup (Fin 4) :=
    φC0.codRestrict (alternatingGroup (Fin 4)) (by
      intro c
      rw [← hψrange]
      exact ⟨(c : G), rfl⟩)
  have hφC_inj : Function.Injective φC := by
    refine (injective_iff_map_eq_one φC).mpr ?_
    intro c hc
    have hcψ : ψ (c : G) = 1 := congrArg Subtype.val hc
    have hcKer : (c : G) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      exact hcψ
    have hcInf : (c : G) ∈ ψ.ker ⊓ C := ⟨hcKer, c.2⟩
    have hcBot : (c : G) ∈ (⊥ : Subgroup G) := by
      rwa [← order72_inf_centralizer_eq_bot_of_mulEquiv_dihedral_three eK]
    exact Subtype.ext (Subgroup.mem_bot.mp hcBot)
  haveI : Fintype C := Fintype.ofFinite C
  have hcardCft : Fintype.card C = 12 := by
    rwa [← Nat.card_eq_fintype_card]
  have hcardA4ft : Fintype.card (alternatingGroup (Fin 4)) = 12 := by
    rw [← Nat.card_eq_fintype_card, nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  have hφC_bij : Function.Bijective φC :=
    (Fintype.bijective_iff_injective_and_card φC).mpr
      ⟨hφC_inj, by rw [hcardCft, hcardA4ft]⟩
  let eC : C ≃* alternatingGroup (Fin 4) := MulEquiv.ofBijective φC hφC_bij
  exact ⟨eprod.trans (MulEquiv.prodCongr eK eC)⟩

/-- The dihedral order-`6` kernel subcase as a residual representative alternative. -/
theorem order72_dihedral_kernel_branch_repCases [Finite G]
    (hG : Nat.card G = 72) (ψ : G →* Equiv.Perm (Fin 4))
    (hψker : Nat.card ψ.ker = 6)
    (hψrange : ψ.range = alternatingGroup (Fin 4))
    (hKiso : Nonempty (ψ.ker ≃* DihedralGroup 3)) :
    order72ResidualRepCases G := by
  exact Or.inr <| Or.inr <| Or.inr <|
    order72_dihedral_kernel_branch_mulEquiv_S3xA4 hG ψ hψker hψrange hKiso

/-- The order-`2` elements of `CyclicRep 6` are trivial or the unique element `3`. -/
theorem order72_cyclicRep_six_sq_eq_one {y : CyclicRep 6} (hy : y ^ 2 = 1) :
    y = 1 ∨ y = Multiplicative.ofAdd 3 := by
  have : ∀ y : CyclicRep 6, y ^ 2 = 1 → y = 1 ∨ y = Multiplicative.ofAdd 3 := by
    decide +kernel
  exact this y hy

/-- In a cyclic group of order `6`, conjugation-invariance of the unique order-`2` element. -/
theorem order72_normal_unique_order_two_mem_center {K : Subgroup G} [K.Normal]
    (x : G) (hxK : x ∈ K) (hx2 : orderOf x = 2)
    (hxuniq : ∀ y : G, y ∈ K → orderOf y = 2 → y = x) : x ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  intro g
  have hconj : g * x * g⁻¹ ∈ K := (inferInstance : K.Normal).conj_mem x hxK g
  have hord : orderOf (g * x * g⁻¹) = 2 := by
    have hsemi : SemiconjBy g x (g * x * g⁻¹) := by
      change g * x = g * x * g⁻¹ * g
      group
    exact (SemiconjBy.orderOf_eq g hsemi).symm.trans hx2
  have hfix : g * x * g⁻¹ = x := hxuniq (g * x * g⁻¹) hconj hord
  calc
    g * x = (g * x * g⁻¹) * g := by group
    _ = x * g := by rw [hfix]

/-- A normal cyclic order-`6` subgroup contributes a central involution. -/
theorem order72_cyclic_order_six_normal_subgroup_has_central_involution
    {K : Subgroup G} [K.Normal] (e : K ≃* CyclicRep 6) :
    ∃ x : G, x ∈ K ∧ orderOf x = 2 ∧ x ∈ Subgroup.center G := by
  let xK : K := e.symm (Multiplicative.ofAdd (3 : ZMod 6))
  have hx2K : orderOf xK = 2 := by
    rw [← MulEquiv.orderOf_eq e xK]
    have hx : orderOf (e xK) = orderOf (Multiplicative.ofAdd (3 : ZMod 6)) := by
      simp [xK]
    rw [hx]
    rw [orderOf_ofAdd_eq_addOrderOf]
    change addOrderOf ((3 : ℕ) : ZMod 6) = 2
    rw [ZMod.addOrderOf_coe' 6 (by norm_num : (3 : ℕ) ≠ 0)]
    norm_num
  have hx2 : orderOf (xK : G) = 2 := by
    rwa [← Subgroup.orderOf_mk xK.1 xK.2]
  have hxuniq : ∀ y : G, y ∈ K → orderOf y = 2 → y = (xK : G) := by
    intro y hyK hy2
    let yK : K := ⟨y, hyK⟩
    have hy2K : orderOf yK = 2 := by
      rwa [Subgroup.orderOf_mk y hyK]
    have hy2e : orderOf (e yK) = 2 := by
      rw [MulEquiv.orderOf_eq e yK, hy2K]
    have hy_sq : (e yK) ^ 2 = 1 := by
      rw [← hy2e]
      exact pow_orderOf_eq_one (e yK)
    rcases order72_cyclicRep_six_sq_eq_one hy_sq with h | h
    · have hy1 : yK = 1 := e.injective (by simpa using h)
      rw [hy1, orderOf_one] at hy2K
      norm_num at hy2K
    · have hx : e xK = Multiplicative.ofAdd (3 : ZMod 6) := by
        simp [xK]
      exact congrArg Subtype.val (e.injective (h.trans hx.symm))
  exact ⟨xK, xK.2, hx2,
    order72_normal_unique_order_two_mem_center (xK : G) xK.2 hx2 hxuniq⟩

/-- If a normal cyclic order-`6` subgroup has quotient `A₄`, then it is central. -/
theorem order72_cyclic_order_six_A4_quotient_le_center [Finite G]
    {K : Subgroup G} [K.Normal] (e : K ≃* CyclicRep 6)
    (hquot : Nonempty (G ⧸ K ≃* alternatingGroup (Fin 4))) :
    K ≤ Subgroup.center G := by
  have hKcard : Nat.card K = 6 := by
    rw [Nat.card_congr e.toEquiv, card_cyclicRep (by norm_num : (6 : ℕ) ≠ 0)]
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hKcard]; norm_num)
  have hKcomm : ∀ x y : K, x * y = y * x := by
    intro x y
    apply e.injective
    rw [map_mul, map_mul, mul_comm]
  have hAutK : Nat.card (MulAut K) = 2 := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  let φ : G →* MulAut K := MulAut.conjNormal
  have hKker : K ≤ φ.ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change k * (x : G) * k⁻¹ = (x : G)
    have hcomm : (⟨k, hk⟩ : K) * x = x * ⟨k, hk⟩ := hKcomm _ _
    have hcommG : k * (x : G) = (x : G) * k := congrArg Subtype.val hcomm
    calc
      k * (x : G) * k⁻¹ = ((x : G) * k) * k⁻¹ := by rw [hcommG]
      _ = (x : G) := by group
  let φQ : G ⧸ K →* MulAut K := QuotientGroup.lift K φ hKker
  obtain ⟨eQ⟩ := hquot
  let ψ : alternatingGroup (Fin 4) →* MulAut K := φQ.comp eQ.symm.toMonoidHom
  have hψ : ψ = 1 := order36_A4_hom_to_order_two_trivial hAutK ψ
  have hφ : φ = 1 := by
    apply MonoidHom.ext
    intro g
    have hq : ψ (eQ ((QuotientGroup.mk' K) g)) = 1 := by
      rw [hψ]
      rfl
    simpa [ψ, φQ] using hq
  intro k hk
  rw [Subgroup.mem_center_iff]
  intro g
  let kk : K := ⟨k, hk⟩
  have hg : φ g = 1 := congrArg (fun f : G →* MulAut K => f g) hφ
  have happ : (φ g) kk = kk := by
    rw [hg]
    rfl
  have hconj : g * k * g⁻¹ = k := by
    have happ_coe := congrArg (fun x : K => (x : G)) happ
    simpa [φ, kk] using happ_coe
  calc
    g * k = (g * k * g⁻¹) * g := by group
    _ = k * g := by rw [hconj]

/-- An order-`6` kernel is cyclic or dihedral. -/
theorem order72_kernel_order_six_cyclic_or_dihedral
    (ψ : G →* Equiv.Perm (Fin 4)) (hψker : Nat.card ψ.ker = 6) :
    Nonempty (ψ.ker ≃* CyclicRep 6) ∨ Nonempty (ψ.ker ≃* DihedralGroup 3) :=
  Smallgroups.Classifications.Order6.classification hψker

/-- In the cyclic subcase of an order-`6` kernel, the ambient group has a central
involution lying in the kernel; otherwise the kernel is `S₃`. -/
theorem order72_kernel_order_six_central_involution_or_dihedral
    (ψ : G →* Equiv.Perm (Fin 4)) (hψker : Nat.card ψ.ker = 6) :
    (∃ x : G, x ∈ ψ.ker ∧ orderOf x = 2 ∧ x ∈ Subgroup.center G) ∨
      Nonempty (ψ.ker ≃* DihedralGroup 3) := by
  rcases order72_kernel_order_six_cyclic_or_dihedral ψ hψker with hcyc | hdih
  · haveI : ψ.ker.Normal := MonoidHom.normal_ker ψ
    exact Or.inl (order72_cyclic_order_six_normal_subgroup_has_central_involution hcyc.some)
  · exact Or.inr hdih

/-- A central element generates a normal cyclic subgroup. -/
theorem order72_zpowers_normal_of_mem_center {z : G} (hz : z ∈ Subgroup.center G) :
    (Subgroup.zpowers z).Normal :=
  normal_of_le_center (Subgroup.zpowers_le.mpr hz)

/-- Quotienting an order-`72` group by an order-`2` cyclic subgroup gives order `36`. -/
theorem order72_card_quotient_zpowers_of_order_two [Finite G]
    (hG : Nat.card G = 72) {z : G} (hz2 : orderOf z = 2)
    [(Subgroup.zpowers z).Normal] :
    Nat.card (G ⧸ Subgroup.zpowers z) = 36 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers z)
  rw [Nat.card_zpowers, hz2, hG] at h
  omega

/-- In the cyclic order-`6` kernel subcase, quotienting by the central involution gives an
order-`36` group. -/
theorem order72_cyclic_kernel_order_six_has_order36_quotient [Finite G]
    (hG : Nat.card G = 72) (ψ : G →* Equiv.Perm (Fin 4))
    (hcyc : Nonempty (ψ.ker ≃* CyclicRep 6)) :
    ∃ z : G, z ∈ ψ.ker ∧ orderOf z = 2 ∧ z ∈ Subgroup.center G ∧
      Nat.card (G ⧸ Subgroup.zpowers z) = 36 := by
  haveI : ψ.ker.Normal := MonoidHom.normal_ker ψ
  obtain ⟨z, hzker, hz2, hzcent⟩ :=
    order72_cyclic_order_six_normal_subgroup_has_central_involution hcyc.some
  haveI : (Subgroup.zpowers z).Normal := order72_zpowers_normal_of_mem_center hzcent
  exact ⟨z, hzker, hz2, hzcent,
    order72_card_quotient_zpowers_of_order_two hG hz2⟩

/-- A normal subgroup of order `8` in an order-`72` group is the unique Sylow-`2`
subgroup. -/
theorem order72_normal_order_eight_subgroup_forces_unique_sylow_two [Finite G]
    (hG : Nat.card G = 72) {P : Subgroup G} (hPnorm : P.Normal)
    (hPcard : Nat.card P = 8) :
    Nat.card (Sylow 2 G) = 1 := by
  have hfact : (Nat.card G).factorization 2 = 3 := by
    rw [hG]
    decide +kernel
  have hP_sylow_card : Nat.card P = 2 ^ (Nat.card G).factorization 2 := by
    rw [hPcard, hfact]
    norm_num
  let PS : Sylow 2 G := Sylow.ofCard P hP_sylow_card
  have hPSnorm : (PS : Subgroup G).Normal := by
    dsimp [PS]
    exact hPnorm
  haveI : Unique (Sylow 2 G) := Sylow.unique_of_normal PS hPSnorm
  exact Nat.card_unique

/-- Pulling back a normal order-`4` subgroup from a quotient by a central involution gives
a normal Sylow-`2` subgroup of the order-`72` group. -/
theorem order72_comap_order_four_quotient_subgroup_forces_unique_sylow_two [Finite G]
    (hG : Nat.card G = 72) {Z : Subgroup G} [Z.Normal] (hZcard : Nat.card Z = 2)
    {A : Subgroup (G ⧸ Z)} [A.Normal] (hAcard : Nat.card A = 4) :
    Nat.card (Sylow 2 G) = 1 := by
  let P : Subgroup G := A.comap (QuotientGroup.mk' Z)
  have hPnorm : P.Normal := by
    dsimp [P]
    exact (inferInstance : A.Normal).comap (QuotientGroup.mk' Z)
  have hPcard : Nat.card P = 8 := by
    have hpre := QuotientGroup.card_preimage_mk Z (A : Set (G ⧸ Z))
    change Nat.card P = Nat.card Z * Nat.card A at hpre
    rw [hZcard, hAcard] at hpre
    exact hpre
  exact order72_normal_order_eight_subgroup_forces_unique_sylow_two hG hPnorm hPcard

/-- The cyclic order-`6` kernel subcase would force a unique Sylow-`2` subgroup. -/
theorem order72_cyclic_kernel_order_six_forces_unique_sylow_two [Finite G]
    (hG : Nat.card G = 72) (ψ : G →* Equiv.Perm (Fin 4))
    (hψker : Nat.card ψ.ker = 6)
    (hψrange : ψ.range = alternatingGroup (Fin 4))
    (hcyc : Nonempty (ψ.ker ≃* CyclicRep 6)) :
    Nat.card (Sylow 2 G) = 1 := by
  have hquot : Nonempty (G ⧸ ψ.ker ≃* alternatingGroup (Fin 4)) :=
    order72_quotient_ker_mulEquiv_A4_of_range_alt ψ hψrange
  have hKcenter : ψ.ker ≤ Subgroup.center G := by
    haveI : ψ.ker.Normal := MonoidHom.normal_ker ψ
    exact order72_cyclic_order_six_A4_quotient_le_center hcyc.some hquot
  obtain ⟨z, hzker, hz2, hzcent, hQcard⟩ :=
    order72_cyclic_kernel_order_six_has_order36_quotient hG ψ hcyc
  let Z : Subgroup G := Subgroup.zpowers z
  haveI : Z.Normal := order72_zpowers_normal_of_mem_center hzcent
  have hZcard : Nat.card Z = 2 := by
    dsimp [Z]
    rw [Nat.card_zpowers, hz2]
  have hZleK : Z ≤ ψ.ker := by
    intro y hy
    rw [Subgroup.mem_zpowers_iff] at hy
    obtain ⟨n, rfl⟩ := hy
    exact ψ.ker.zpow_mem hzker n
  let Q : Type := G ⧸ Z
  let KQ : Subgroup Q := ψ.ker.map (QuotientGroup.mk' Z)
  have hKQnormal : KQ.Normal := by
    dsimp [KQ]
    exact (MonoidHom.normal_ker ψ).map (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
  haveI : KQ.Normal := hKQnormal
  have hKQcenter : KQ ≤ Subgroup.center Q := by
    intro q hq
    rw [Subgroup.mem_center_iff]
    intro x
    rw [Subgroup.mem_map] at hq
    obtain ⟨k, hk, hkq⟩ := hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z x
    rw [← hkq]
    change (QuotientGroup.mk' Z) g * (QuotientGroup.mk' Z) k =
      (QuotientGroup.mk' Z) k * (QuotientGroup.mk' Z) g
    rw [← map_mul, ← map_mul]
    exact congrArg (QuotientGroup.mk' Z) ((Subgroup.mem_center_iff.mp (hKcenter hk)) g)
  have hKQcard : Nat.card KQ = 3 := by
    have hpre := QuotientGroup.card_preimage_mk Z (KQ : Set Q)
    have hpre_eq : ((QuotientGroup.mk' Z) ⁻¹' (KQ : Set Q)) = (ψ.ker : Set G) := by
      ext g
      constructor
      · intro hg
        change (QuotientGroup.mk' Z) g ∈ KQ at hg
        rw [Subgroup.mem_map] at hg
        obtain ⟨k, hk, hkg⟩ := hg
        have hzg : k⁻¹ * g ∈ Z := by
          rw [← QuotientGroup.eq_one_iff]
          change (QuotientGroup.mk' Z) (k⁻¹ * g) = 1
          rw [map_mul, map_inv, hkg, inv_mul_cancel]
        have hzkg : k⁻¹ * g ∈ ψ.ker := hZleK hzg
        have hkprod : k * (k⁻¹ * g) ∈ ψ.ker := ψ.ker.mul_mem hk hzkg
        have hgprod : k * (k⁻¹ * g) = g := by group
        rwa [hgprod] at hkprod
      · intro hg
        change (QuotientGroup.mk' Z) g ∈ KQ
        rw [Subgroup.mem_map]
        exact ⟨g, hg, rfl⟩
    change Nat.card ((QuotientGroup.mk' Z) ⁻¹' (KQ : Set Q)) =
      Nat.card Z * Nat.card KQ at hpre
    have hKsetcard : Nat.card (ψ.ker : Set G) = 6 := by
      change Nat.card ψ.ker = 6
      exact hψker
    rw [hpre_eq, hKsetcard, hZcard] at hpre
    omega
  have hKQquot : Nonempty (Q ⧸ KQ ≃* alternatingGroup (Fin 4)) := by
    obtain ⟨e⟩ := hquot
    exact ⟨(QuotientGroup.quotientQuotientEquivQuotient Z ψ.ker hZleK).trans e⟩
  obtain ⟨W, _hWnormal, _hKQW, _hWcard, _hWiso, _hpow2, _hpow3,
      L, _hLcomp, hLcard, _hLiso, hLnormal⟩ :=
    order36_A4_quotient_C3_klein_normal_klein_complement
      (G := Q) hQcard KQ hKQcenter hKQcard hKQquot
  let A : Subgroup Q := L.map W.subtype
  have hAcard : Nat.card A = 4 := by
    dsimp [A]
    exact order36_klein_complement_map_card W hLcard
  haveI : A.Normal := by
    dsimp [A]
    exact hLnormal
  exact order72_comap_order_four_quotient_subgroup_forces_unique_sylow_two
    (G := G) hG hZcard hAcard

/-- The residual order-`6` kernel branch is exactly the `S₃ × A₄` representative. -/
theorem order72_kernel_order_six_branch_repCases [Finite G]
    (hG : Nat.card G = 72) (hSyl2 : Nat.card (Sylow 2 G) ≠ 1)
    (ψ : G →* Equiv.Perm (Fin 4))
    (hψker : Nat.card ψ.ker = 6)
    (hψrange : ψ.range = alternatingGroup (Fin 4)) :
    order72ResidualRepCases G := by
  rcases order72_kernel_order_six_cyclic_or_dihedral ψ hψker with hcyc | hdih
  · exact False.elim
      (hSyl2 (order72_cyclic_kernel_order_six_forces_unique_sylow_two
        hG ψ hψker hψrange hcyc))
  · exact order72_dihedral_kernel_branch_repCases hG ψ hψker hψrange hdih

/-- The order-`6` residual branch split into the cyclic-kernel data and the `S₃`-kernel
data.  This is the local interface used by the final residual proof. -/
theorem order72_kernel_order_six_branch_data [Finite G]
    (hG : Nat.card G = 72) (ψ : G →* Equiv.Perm (Fin 4))
    (hψker : Nat.card ψ.ker = 6)
    (hψrange : ψ.range = alternatingGroup (Fin 4)) :
    (∃ z : G, z ∈ ψ.ker ∧ orderOf z = 2 ∧ z ∈ Subgroup.center G ∧
        Nat.card (G ⧸ Subgroup.zpowers z) = 36 ∧
        Nonempty (G ⧸ ψ.ker ≃* alternatingGroup (Fin 4))) ∨
      (Nonempty (ψ.ker ≃* DihedralGroup 3) ∧
        Nonempty (G ⧸ ψ.ker ≃* alternatingGroup (Fin 4))) := by
  have hquot : Nonempty (G ⧸ ψ.ker ≃* alternatingGroup (Fin 4)) :=
    order72_quotient_ker_mulEquiv_A4_of_range_alt ψ hψrange
  rcases order72_kernel_order_six_cyclic_or_dihedral ψ hψker with hcyc | hdih
  · obtain ⟨z, hzker, hz2, hzcent, hzquot⟩ :=
      order72_cyclic_kernel_order_six_has_order36_quotient hG ψ hcyc
    exact Or.inl ⟨z, hzker, hz2, hzcent, hzquot, hquot⟩
  · exact Or.inr ⟨hdih, hquot⟩

end Stage1

/-! ### Stage 2: the order-`3` kernel branch -/

section Stage2

/-- The Klein four subgroup of `S₄` has order `4`. -/
theorem order72_S4_V4_card : Nat.card order72_S4_V4 = 4 := by
  dsimp [order72_S4_V4]
  rw [Subgroup.card_map_of_injective]
  · simpa using alternatingGroup.kleinFour_card_of_card_eq_four (α := Fin 4) (by simp)
  · exact Subtype.coe_injective

/-- The Klein four subgroup of `S₄` is normal. -/
theorem order72_S4_V4_normal : order72_S4_V4.Normal := by
  haveI : (alternatingGroup (Fin 4) : Subgroup order72_S4).Normal :=
    alternatingGroup.normal
  haveI : (alternatingGroup.kleinFour (Fin 4)).Characteristic :=
    alternatingGroup.characteristic_kleinFour (α := Fin 4) (by simp)
  dsimp [order72_S4_V4]
  infer_instance

local instance instOrder72S4V4Normal : order72_S4_V4.Normal :=
  order72_S4_V4_normal

/-- The Klein four subgroup of `S₄` lies in `A₄`. -/
theorem order72_S4_V4_le_alternating :
    order72_S4_V4 ≤ (alternatingGroup (Fin 4) : Subgroup order72_S4) := by
  intro x hx
  dsimp [order72_S4_V4] at hx
  rw [Subgroup.mem_map] at hx
  obtain ⟨a, _ha, hax⟩ := hx
  rw [← hax]
  exact a.property

/-- Elements of the Klein four subgroup of `S₄` square to `1`. -/
theorem order72_S4_V4_sq_one {x : order72_S4} (hx : x ∈ order72_S4_V4) :
    x ^ 2 = 1 := by
  dsimp [order72_S4_V4] at hx
  rw [Subgroup.mem_map] at hx
  obtain ⟨a, ha, hax⟩ := hx
  rw [← hax]
  exact congrArg Subtype.val (order36_A4_mem_kleinFour_sq ha)

/-- The quotient `S₄/V₄` is noncommutative. -/
theorem order72_S4_quotient_V4_not_comm :
    ¬ ∀ a b : order72_S4 ⧸ order72_S4_V4, a * b = b * a := by
  let s01 : order72_S4 := Equiv.swap (0 : Fin 4) 1
  let s12 : order72_S4 := Equiv.swap (1 : Fin 4) 2
  have hnot : s01 * s12 * (s12 * s01)⁻¹ ∉ order72_S4_V4 := by
    intro hx
    have hsquare : (s01 * s12 * (s12 * s01)⁻¹) ^ 2 = 1 :=
      order72_S4_V4_sq_one hx
    have hsquare_ne : (s01 * s12 * (s12 * s01)⁻¹) ^ 2 ≠ 1 := by
      decide +kernel
    exact hsquare_ne hsquare
  intro hcomm
  have hq := hcomm ((QuotientGroup.mk' order72_S4_V4) s01)
    ((QuotientGroup.mk' order72_S4_V4) s12)
  change (QuotientGroup.mk' order72_S4_V4) (s01 * s12) =
    (QuotientGroup.mk' order72_S4_V4) (s12 * s01) at hq
  have hqmem := QuotientGroup.eq_iff_div_mem.mp hq
  exact hnot (by simpa [div_eq_mul_inv] using hqmem)

/-- `S₄/V₄` is the nonabelian group of order `6`, represented as `DihedralGroup 3`. -/
theorem order72_S4_quotient_V4_mulEquiv_D3 :
    Nonempty (order72_S4 ⧸ order72_S4_V4 ≃* DihedralGroup 3) := by
  have hcard : Nat.card (order72_S4 ⧸ order72_S4_V4) = 6 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup order72_S4_V4
    rw [order72_S4_V4_card] at h
    have hS4 : Nat.card order72_S4 = 24 := by
      rw [Nat.card_perm, Nat.card_fin]
      norm_num [Nat.factorial]
    rw [hS4] at h
    omega
  rcases Smallgroups.Classifications.Order6.classification hcard with hcyc | hdih
  · obtain ⟨e⟩ := hcyc
    exact False.elim (order72_S4_quotient_V4_not_comm (by
      intro a b
      apply e.injective
      rw [map_mul, map_mul, mul_comm]))
  · exact hdih

/-- Pull back the Klein four subgroup of `S₄` through a quotient `G/K ≃ S₄`. -/
theorem order72_S4_quotient_klein_preimage [Finite G] (hG : Nat.card G = 72)
    (K : Subgroup G) [K.Normal] (_hK : Nat.card K = 3)
    (hquot : Nonempty (G ⧸ K ≃* order72_S4)) :
    ∃ (W : Subgroup G) (_ : W.Normal), K ≤ W ∧ Nat.card W = 12 ∧
      Nonempty (W ⧸ K.subgroupOf W ≃* order72_S4_V4) := by
  obtain ⟨e⟩ := hquot
  let φ : G →* order72_S4 := e.toMonoidHom.comp (QuotientGroup.mk' K)
  let V : Subgroup order72_S4 := order72_S4_V4
  let W : Subgroup G := V.comap φ
  have hVnormal : V.Normal := by
    dsimp [V]
    exact order72_S4_V4_normal
  have hWnormal : W.Normal := by
    dsimp [W]
    exact hVnormal.comap φ
  have hKW : K ≤ W := by
    intro k hk
    have hkq : (QuotientGroup.mk' K) k = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hk
    have hφk : φ k = 1 := by
      change e ((QuotientGroup.mk' K) k) = 1
      rw [hkq]
      simp
    change φ k ∈ V
    rw [hφk]
    exact V.one_mem
  have hφ_surj : Function.Surjective φ := by
    intro a
    obtain ⟨q, hq⟩ := e.surjective a
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective K q
    refine ⟨g, ?_⟩
    change e ((QuotientGroup.mk' K) g) = a
    rw [hg, hq]
  have hV_card : Nat.card V = 4 := by
    dsimp [V]
    exact order72_S4_V4_card
  have hV_index : V.index = 6 := by
    have hmul := V.index_mul_card
    rw [hV_card] at hmul
    have hS4 : Nat.card order72_S4 = 24 := by
      rw [Nat.card_perm, Nat.card_fin]
      norm_num [Nat.factorial]
    rw [hS4] at hmul
    omega
  have hW_index : W.index = 6 := by
    dsimp [W]
    rw [V.index_comap_of_surjective hφ_surj, hV_index]
  have hWcard : Nat.card W = 12 := by
    have hmul := W.index_mul_card
    rw [hW_index, hG] at hmul
    omega
  let φW : W →* order72_S4 := φ.comp W.subtype
  have hφWker : φW.ker = K.subgroupOf W := by
    ext w
    constructor
    · intro hw
      rw [MonoidHom.mem_ker] at hw
      rw [Subgroup.mem_subgroupOf]
      have hq : (QuotientGroup.mk' K) (w : G) = 1 := by
        apply e.injective
        simpa [φW, φ] using hw
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hq
    · intro hw
      rw [Subgroup.mem_subgroupOf] at hw
      rw [MonoidHom.mem_ker]
      have hq : (QuotientGroup.mk' K) (w : G) = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hw
      change e ((QuotientGroup.mk' K) (w : G)) = 1
      rw [hq]
      simp
  have hφWrange : φW.range = V := by
    apply le_antisymm
    · intro a ha
      rw [MonoidHom.mem_range] at ha
      obtain ⟨w, hw⟩ := ha
      rw [← hw]
      change φ (w : G) ∈ V
      exact w.property
    · intro a ha
      rw [MonoidHom.mem_range]
      obtain ⟨g, hg⟩ := hφ_surj a
      have hgW : g ∈ W := by
        change φ g ∈ V
        rw [hg]
        exact ha
      refine ⟨⟨g, hgW⟩, ?_⟩
      change φ g = a
      exact hg
  haveI : (K.subgroupOf W).Normal := hφWker ▸ MonoidHom.normal_ker φW
  refine ⟨W, hWnormal, hKW, hWcard, ?_⟩
  change Nonempty (W ⧸ K.subgroupOf W ≃* V)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hφWker.symm).trans
    ((QuotientGroup.quotientKerEquivRange φW).trans (MulEquiv.subgroupCongr hφWrange))⟩

/-- If `W` is the preimage of `V₄ ≤ S₄` and `L` complements `K` inside `W`, then
`L` maps exactly onto `V₄` in the quotient `G/K ≃ S₄`. -/
theorem order72_klein_complement_S4_V4_exact
    (K W : Subgroup G) [K.Normal] {L : Subgroup W}
    (hLcomp : (K.subgroupOf W).IsComplement' L)
    (e : G ⧸ K ≃* order72_S4)
    (hmem : ∀ {g : G}, g ∈ W ↔ e ((QuotientGroup.mk' K) g) ∈ order72_S4_V4)
    (hV_liftW : ∀ {a : order72_S4}, a ∈ order72_S4_V4 →
        ∃ w : W, e ((QuotientGroup.mk' K) (w : G)) = a) :
    let A : Subgroup G := L.map W.subtype
    (∀ {g : G}, g ∈ A →
      e ((QuotientGroup.mk' K) g) ∈ order72_S4_V4) ∧
      (∀ {a : order72_S4}, a ∈ order72_S4_V4 →
        ∃ g : G, g ∈ A ∧ e ((QuotientGroup.mk' K) g) = a) := by
  intro A
  constructor
  · intro g hgA
    rw [Subgroup.mem_map] at hgA
    obtain ⟨l, hlL, hlg⟩ := hgA
    rw [← hlg]
    exact hmem.mp (l : W).property
  · intro a ha
    obtain ⟨w, hw⟩ := hV_liftW ha
    obtain ⟨⟨k, l⟩, hkl⟩ := hLcomp.2 w
    refine ⟨((l : L) : W), ?_, ?_⟩
    · rw [Subgroup.mem_map]
      exact ⟨(l : W), l.property, rfl⟩
    · have hklG : (((k : K.subgroupOf W) : W) : G) * (((l : L) : W) : G) =
          (w : G) := by
        exact congrArg (fun x : W => (x : G)) hkl
      have hkK : (((k : K.subgroupOf W) : W) : G) ∈ K := by
        exact Subgroup.mem_subgroupOf.mp k.property
      have hqk : (QuotientGroup.mk' K) (((k : K.subgroupOf W) : W) : G) = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hkK
      have hqeq :
          (QuotientGroup.mk' K) (w : G) =
            (QuotientGroup.mk' K) (((l : L) : W) : G) := by
        rw [← hklG, map_mul, hqk, one_mul]
      rw [← hqeq]
      exact hw

/-- For a fixed quotient isomorphism `G/K ≃ S₄`, the Klein-four preimage is a
central extension of `V₄` by `K` and has a complement of order `4`. -/
theorem order72_S4_equiv_klein_preimage_central_complement [Finite G]
    (hG : Nat.card G = 72) (K : Subgroup G) [K.Normal] (hK : Nat.card K = 3)
    (e : G ⧸ K ≃* order72_S4) :
    ∃ (W : Subgroup G) (_ : W.Normal), K ≤ W ∧ Nat.card W = 12 ∧
      K.subgroupOf W ≤ Subgroup.center W ∧
        Nonempty (G ⧸ W ≃* DihedralGroup 3) ∧
          (∀ {g : G}, g ∈ W → g ^ 2 ∈ K) ∧
            ∃ L : Subgroup W, (K.subgroupOf W).IsComplement' L ∧ Nat.card L = 4 ∧
              (∀ {g : G}, g ∈ (L.map W.subtype : Subgroup G) →
                e ((QuotientGroup.mk' K) g) ∈ order72_S4_V4) ∧
              (∀ {a : order72_S4}, a ∈ order72_S4_V4 →
                ∃ g : G, g ∈ (L.map W.subtype : Subgroup G) ∧
                  e ((QuotientGroup.mk' K) g) = a) := by
  let φ : G →* order72_S4 := e.toMonoidHom.comp (QuotientGroup.mk' K)
  let V : Subgroup order72_S4 := order72_S4_V4
  let W : Subgroup G := V.comap φ
  have hVnormal : V.Normal := by
    dsimp [V]
    exact order72_S4_V4_normal
  have hWnormal : W.Normal := by
    dsimp [W]
    exact hVnormal.comap φ
  have hKW : K ≤ W := by
    intro k hk
    have hkq : (QuotientGroup.mk' K) k = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hk
    have hφk : φ k = 1 := by
      change e ((QuotientGroup.mk' K) k) = 1
      rw [hkq]
      simp
    change φ k ∈ V
    rw [hφk]
    exact V.one_mem
  have hφ_surj : Function.Surjective φ := by
    intro a
    obtain ⟨q, hq⟩ := e.surjective a
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective K q
    refine ⟨g, ?_⟩
    change e ((QuotientGroup.mk' K) g) = a
    rw [hg, hq]
  have hV_card : Nat.card V = 4 := by
    dsimp [V]
    exact order72_S4_V4_card
  have hV_index : V.index = 6 := by
    have hmul := V.index_mul_card
    rw [hV_card] at hmul
    have hS4 : Nat.card order72_S4 = 24 := by
      rw [Nat.card_perm, Nat.card_fin]
      norm_num [Nat.factorial]
    rw [hS4] at hmul
    omega
  have hW_index : W.index = 6 := by
    dsimp [W]
    rw [V.index_comap_of_surjective hφ_surj, hV_index]
  have hWcard : Nat.card W = 12 := by
    have hmul := W.index_mul_card
    rw [hW_index, hG] at hmul
    omega
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  obtain ⟨eK⟩ : Nonempty (K ≃* order72_C3) := by
    simpa [order72_C3, CyclicRep] using
      (prime_classification (G := K) (p := 3) (by norm_num) hK)
  have hKcomm : ∀ x y : K, x * y = y * x := by
    intro x y
    apply eK.injective
    rw [map_mul, map_mul, mul_comm]
  have hAutK : Nat.card (MulAut K) = 2 := by
    rw [Nat.card_congr (MulAut.congr eK).toEquiv]
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  let act : G →* MulAut K := MulAut.conjNormal
  have hKker : K ≤ act.ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change k * (x : G) * k⁻¹ = (x : G)
    have hcomm : (⟨k, hk⟩ : K) * x = x * ⟨k, hk⟩ := hKcomm _ _
    have hcommG : k * (x : G) = (x : G) * k := congrArg Subtype.val hcomm
    calc
      k * (x : G) * k⁻¹ = ((x : G) * k) * k⁻¹ := by rw [hcommG]
      _ = (x : G) := by group
  let actQ : G ⧸ K →* MulAut K := QuotientGroup.lift K act hKker
  let χ : order72_S4 →* MulAut K := actQ.comp e.symm.toMonoidHom
  let χA : alternatingGroup (Fin 4) →* MulAut K :=
    χ.comp (alternatingGroup (Fin 4)).subtype
  have hχA : χA = 1 := order36_A4_hom_to_order_two_trivial hAutK χA
  have hKcenterW : K.subgroupOf W ≤ Subgroup.center W := by
    intro k hkW
    rw [Subgroup.mem_center_iff]
    intro w
    have hwAlt : φ (w : G) ∈ (alternatingGroup (Fin 4) : Subgroup order72_S4) :=
      order72_S4_V4_le_alternating w.property
    have hχ : χ (φ (w : G)) = 1 := by
      have hχA' : χA ⟨φ (w : G), hwAlt⟩ = 1 := by
        rw [hχA]
        rfl
      simpa [χA] using hχA'
    have hq : e.symm (φ (w : G)) = (QuotientGroup.mk' K) (w : G) := by
      dsimp [φ]
      rw [MulEquiv.symm_apply_apply]
    have hact : act (w : G) = 1 := by
      simpa [χ, actQ, hq] using hχ
    have happ : act (w : G) ⟨(k : W), Subgroup.mem_subgroupOf.mp hkW⟩ =
        ⟨(k : W), Subgroup.mem_subgroupOf.mp hkW⟩ := by
      rw [hact]
      rfl
    have hconj := congrArg (fun x : K => (x : G)) happ
    change (w : G) * ((k : W) : G) * (w : G)⁻¹ = ((k : W) : G) at hconj
    apply Subtype.ext
    change (w : G) * ((k : W) : G) = ((k : W) : G) * (w : G)
    calc
      (w : G) * ((k : W) : G) =
          ((w : G) * ((k : W) : G) * (w : G)⁻¹) * (w : G) := by group
      _ = ((k : W) : G) * (w : G) := by rw [hconj]
  have hpowW : ∀ {g : G}, g ∈ W → g ^ 2 ∈ K := by
    intro g hgW
    change φ g ∈ V at hgW
    have hφsq : (φ g) ^ 2 = 1 := order72_S4_V4_sq_one hgW
    have hq : ((QuotientGroup.mk' K) g) ^ 2 = 1 := by
      apply e.injective
      simpa [φ] using hφsq
    change (g : G ⧸ K) ^ 2 = 1 at hq
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hq
    exact hq
  have hGWquot : Nonempty (G ⧸ W ≃* DihedralGroup 3) := by
    haveI : W.Normal := hWnormal
    haveI : V.Normal := hVnormal
    let θ : G ⧸ W →* order72_S4 ⧸ V :=
      QuotientGroup.map W V φ (by
        intro g hgW
        exact hgW)
    have hθinj : Function.Injective θ := by
      refine (injective_iff_map_eq_one θ).mpr ?_
      intro q hq
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective W q
      have hgV : φ g ∈ V := by
        change (QuotientGroup.mk' V) (φ g) = 1 at hq
        rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hq
      change (QuotientGroup.mk' W) g = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hgV
    have hθsurj : Function.Surjective θ := by
      intro q
      obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective V q
      obtain ⟨g, hg⟩ := hφ_surj s
      refine ⟨(QuotientGroup.mk' W) g, ?_⟩
      change (QuotientGroup.mk' V) (φ g) = (QuotientGroup.mk' V) s
      rw [hg]
    let eθ : G ⧸ W ≃* order72_S4 ⧸ V := MulEquiv.ofBijective θ ⟨hθinj, hθsurj⟩
    obtain ⟨eS3⟩ := order72_S4_quotient_V4_mulEquiv_D3
    exact ⟨eθ.trans eS3⟩
  have hKWcard : Nat.card (K.subgroupOf W) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKW).toEquiv, hK]
  have hKWindex : (K.subgroupOf W).index = 4 := by
    have hmul := (K.subgroupOf W).index_mul_card
    rw [hKWcard, hWcard] at hmul
    omega
  have hcop : Nat.Coprime (Nat.card (K.subgroupOf W)) (K.subgroupOf W).index := by
    rw [hKWcard, hKWindex]
    norm_num
  haveI : (K.subgroupOf W).Normal := by infer_instance
  obtain ⟨L, hLcomp⟩ := Subgroup.exists_right_complement'_of_coprime
    (N := K.subgroupOf W) hcop
  have hLcard : Nat.card L = 4 := by
    have hindex := (Subgroup.IsComplement'.symm hLcomp).index_eq_card
    rw [hKWindex] at hindex
    exact hindex.symm
  have hmemW : ∀ {g : G}, g ∈ W ↔
      e ((QuotientGroup.mk' K) g) ∈ order72_S4_V4 := by
    intro g
    rfl
  have hV_liftW : ∀ {a : order72_S4}, a ∈ order72_S4_V4 →
      ∃ w : W, e ((QuotientGroup.mk' K) (w : G)) = a := by
    intro a ha
    obtain ⟨g, hg⟩ := hφ_surj a
    have hgW : g ∈ W := by
      change φ g ∈ V
      rw [hg]
      exact ha
    exact ⟨⟨g, hgW⟩, hg⟩
  obtain ⟨hL_le_V, hV_liftL⟩ :=
    order72_klein_complement_S4_V4_exact K W hLcomp e hmemW hV_liftW
  exact ⟨W, hWnormal, hKW, hWcard, hKcenterW, hGWquot, hpowW,
    L, hLcomp, hLcard, hL_le_V, hV_liftL⟩

/-- Local version of `order36_mem_klein_complement_of_sq_one`: it is enough that the
order-`3` kernel centralizes the Klein-four preimage `W`, not all of `G`. -/
theorem order72_mem_klein_complement_of_sq_one_of_center_preimage
    {K W : Subgroup G} [K.Normal] (hKcenterW : K.subgroupOf W ≤ Subgroup.center W)
    (hKW : K ≤ W) (hKcard : Nat.card K = 3) {L : Subgroup W}
    (hLcomp : (K.subgroupOf W).IsComplement' L)
    (hpow_in : ∀ {g : G}, g ∈ W → g ^ 2 ∈ K)
    {w : W} (hw2 : ((w : G) ^ 2) = 1) : w ∈ L := by
  have hKsubcard : Nat.card (K.subgroupOf W) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKW).toEquiv, hKcard]
  obtain ⟨⟨k, l⟩, hkl⟩ := hLcomp.2 w
  have hkK : (k : W) ∈ K.subgroupOf W := k.property
  have hlL : (l : W) ∈ L := l.property
  have hklW : (k : W) * (l : W) = w := by
    simpa using hkl
  have hl2K : ((l : W) ^ 2) ∈ K.subgroupOf W := by
    rw [Subgroup.mem_subgroupOf]
    change (((l : W) : G) ^ 2) ∈ K
    exact hpow_in (l : W).property
  have hl2L : ((l : W) ^ 2) ∈ L := L.pow_mem hlL 2
  have hl2inf : ((l : W) ^ 2) ∈ K.subgroupOf W ⊓ L := by
    rw [Subgroup.mem_inf]
    exact ⟨hl2K, hl2L⟩
  have hl2W : (l : W) ^ 2 = 1 :=
    Subgroup.mem_bot.mp ((disjoint_iff_inf_le.mp hLcomp.disjoint) hl2inf)
  have hcommW : (k : W) * (l : W) = (l : W) * (k : W) :=
    ((Subgroup.mem_center_iff.mp (hKcenterW hkK)) (l : W)).symm
  have hw2W : w ^ 2 = 1 := by
    apply Subtype.ext
    simpa using hw2
  have hkl2 : ((k : W) * (l : W)) ^ 2 = 1 := by
    rw [hklW, hw2W]
  have hkl2_eq_k2 : ((k : W) * (l : W)) ^ 2 = (k : W) ^ 2 := by
    calc
      ((k : W) * (l : W)) ^ 2
          = (k : W) * (l : W) * ((k : W) * (l : W)) := by rw [pow_two]
      _ = (k : W) * ((l : W) * (k : W)) * (l : W) := by simp [mul_assoc]
      _ = (k : W) * ((k : W) * (l : W)) * (l : W) := by rw [hcommW]
      _ = (k : W) ^ 2 * ((l : W) ^ 2) := by simp [pow_two, mul_assoc]
      _ = (k : W) ^ 2 := by rw [hl2W, mul_one]
  have hk2W : (k : W) ^ 2 = 1 := by
    rw [← hkl2_eq_k2]
    exact hkl2
  have hk2K : k ^ 2 = 1 := by
    apply Subtype.ext
    exact hk2W
  have hkord_dvd3 : orderOf k ∣ 3 := by
    have := orderOf_dvd_natCard k
    simpa [hKsubcard] using this
  have hkord_dvd2 : orderOf k ∣ 2 :=
    orderOf_dvd_of_pow_eq_one hk2K
  have hkord_one : orderOf k = 1 := by
    have hdiv : orderOf k ∣ 1 := by
      simpa using Nat.dvd_gcd hkord_dvd3 hkord_dvd2
    exact Nat.dvd_one.mp hdiv
  have hk_one : (k : W) = 1 :=
    congrArg (fun x : K.subgroupOf W => (x : W)) (orderOf_eq_one_iff.mp hkord_one)
  have hl_eq_w : (l : W) = w := by
    simpa [hk_one] using hklW
  rw [← hl_eq_w]
  exact hlL

/-- A Klein complement in the `S₄`-branch preimage is normal in the whole ambient
group, because conjugation preserves `W` and the property of squaring to `1`. -/
theorem order72_klein_complement_map_normal_of_center_preimage
    {K W : Subgroup G} [K.Normal] [W.Normal]
    (hKcenterW : K.subgroupOf W ≤ Subgroup.center W)
    (hKW : K ≤ W) (hKcard : Nat.card K = 3) {L : Subgroup W}
    (hLcomp : (K.subgroupOf W).IsComplement' L)
    (hpow_in : ∀ {g : G}, g ∈ W → g ^ 2 ∈ K) :
    (L.map W.subtype : Subgroup G).Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨l, hlL, hlx⟩ := Subgroup.mem_map.mp hx
  rw [← hlx]
  have hconjW : g * (l : G) * g⁻¹ ∈ W :=
    (inferInstance : W.Normal).conj_mem (l : G) l.property g
  let y : W := ⟨g * (l : G) * g⁻¹, hconjW⟩
  have hl2W : l ^ 2 = 1 :=
    order36_klein_complement_pow_two K W hLcomp hpow_in hlL
  have hl2G : ((l : G) ^ 2) = 1 :=
    congrArg (fun z : W => (z : G)) hl2W
  have hy2 : ((y : G) ^ 2) = 1 := by
    change (g * (l : G) * g⁻¹) ^ 2 = 1
    calc
      (g * (l : G) * g⁻¹) ^ 2 = g * ((l : G) ^ 2) * g⁻¹ := by
        simp [pow_two, mul_assoc]
      _ = 1 := by rw [hl2G]; simp
  have hyL : y ∈ L :=
    order72_mem_klein_complement_of_sq_one_of_center_preimage
      hKcenterW hKW hKcard hLcomp hpow_in hy2
  exact Subgroup.mem_map.mpr ⟨y, hyL, rfl⟩

/-- In the `S₄` quotient branch, quotienting by the normal Klein complement gives a
group of order `18`. -/
theorem order72_S4_quotient_normal_klein_complement_quotient18 [Finite G]
    (hG : Nat.card G = 72) (K : Subgroup G) [K.Normal] (hK : Nat.card K = 3)
    (hquot : Nonempty (G ⧸ K ≃* order72_S4)) :
    ∃ (W : Subgroup G) (_ : W.Normal), K ≤ W ∧ Nat.card W = 12 ∧
      K.subgroupOf W ≤ Subgroup.center W ∧
        Nonempty (G ⧸ W ≃* DihedralGroup 3) ∧
          ∃ L : Subgroup W, (K.subgroupOf W).IsComplement' L ∧ Nat.card L = 4 ∧
            (L.map W.subtype : Subgroup G).Normal ∧
              Nat.card (G ⧸ (L.map W.subtype : Subgroup G)) = 18 := by
  obtain ⟨e⟩ := hquot
  obtain ⟨W, hWnormal, hKW, hWcard, hKcenterW, hGWquot, hpowW, L, hLcomp, hLcard,
    _hLleV, _hVLiftL⟩ :=
    order72_S4_equiv_klein_preimage_central_complement (G := G) hG K hK e
  haveI : W.Normal := hWnormal
  have hLnormal : (L.map W.subtype : Subgroup G).Normal :=
    order72_klein_complement_map_normal_of_center_preimage
      hKcenterW hKW hK hLcomp hpowW
  have hLmapcard : Nat.card (L.map W.subtype : Subgroup G) = 4 :=
    order36_klein_complement_map_card W hLcard
  haveI : (L.map W.subtype : Subgroup G).Normal := hLnormal
  have hquot18 : Nat.card (G ⧸ (L.map W.subtype : Subgroup G)) = 18 := by
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (L.map W.subtype : Subgroup G)
    rw [hG, hLmapcard] at hcard
    omega
  exact ⟨W, hWnormal, hKW, hWcard, hKcenterW, hGWquot,
    L, hLcomp, hLcard, hLnormal, hquot18⟩

/-- The normal Klein complement quotient in the `S₄` branch falls under the standard
classification of groups of order `18`. -/
theorem order72_S4_quotient_normal_klein_complement_order18_cases [Finite G]
    (hG : Nat.card G = 72) (K : Subgroup G) [K.Normal] (hK : Nat.card K = 3)
    (hquot : Nonempty (G ⧸ K ≃* order72_S4)) :
    ∃ (W : Subgroup G) (_ : W.Normal), K ≤ W ∧ Nat.card W = 12 ∧
      K.subgroupOf W ≤ Subgroup.center W ∧
        Nonempty (G ⧸ W ≃* DihedralGroup 3) ∧
          ∃ L : Subgroup W, (K.subgroupOf W).IsComplement' L ∧ Nat.card L = 4 ∧
            ∃ _ : (L.map W.subtype : Subgroup G).Normal,
              Nat.card (G ⧸ (L.map W.subtype : Subgroup G)) = 18 ∧
                (Nonempty ((G ⧸ (L.map W.subtype : Subgroup G)) ≃*
                    Smallgroups.Classifications.Order18.RA) ∨
                  Nonempty ((G ⧸ (L.map W.subtype : Subgroup G)) ≃*
                    Smallgroups.Classifications.Order18.RB) ∨
                  Nonempty ((G ⧸ (L.map W.subtype : Subgroup G)) ≃*
                    Smallgroups.Classifications.Order18.RC) ∨
                  Nonempty ((G ⧸ (L.map W.subtype : Subgroup G)) ≃*
                    Smallgroups.Classifications.Order18.RD) ∨
                  Nonempty ((G ⧸ (L.map W.subtype : Subgroup G)) ≃*
                    Smallgroups.Classifications.Order18.RE)) := by
  obtain ⟨W, hWnormal, hKW, hWcard, hKcenterW, hGWquot, L, hLcomp, hLcard,
    hLnormal, hquot18⟩ :=
    order72_S4_quotient_normal_klein_complement_quotient18
      (G := G) hG K hK hquot
  haveI : (L.map W.subtype : Subgroup G).Normal := hLnormal
  have hQcases :
      Nonempty ((G ⧸ (L.map W.subtype : Subgroup G)) ≃*
          Smallgroups.Classifications.Order18.RA) ∨
        Nonempty ((G ⧸ (L.map W.subtype : Subgroup G)) ≃*
          Smallgroups.Classifications.Order18.RB) ∨
        Nonempty ((G ⧸ (L.map W.subtype : Subgroup G)) ≃*
          Smallgroups.Classifications.Order18.RC) ∨
        Nonempty ((G ⧸ (L.map W.subtype : Subgroup G)) ≃*
          Smallgroups.Classifications.Order18.RD) ∨
        Nonempty ((G ⧸ (L.map W.subtype : Subgroup G)) ≃*
          Smallgroups.Classifications.Order18.RE) :=
    Smallgroups.Classifications.Order18.classification hquot18
  exact ⟨W, hWnormal, hKW, hWcard, hKcenterW, hGWquot, L, hLcomp, hLcard, hLnormal,
    hquot18, hQcases⟩

/-- If `A ≤ W` and `G/W ≃ S₃`, then `G/A` cannot be commutative. -/
theorem order72_quotient_not_comm_of_D3_quotient
    {A W : Subgroup G} [A.Normal] [W.Normal] (hAW : A ≤ W)
    (hGW : Nonempty (G ⧸ W ≃* DihedralGroup 3)) :
    ¬ ∀ a b : G ⧸ A, a * b = b * a := by
  intro hcomm
  let B : Subgroup (G ⧸ A) := W.map (QuotientGroup.mk' A)
  haveI : B.Normal := by
    dsimp [B]
    exact (inferInstance : W.Normal).map (QuotientGroup.mk' A)
      (QuotientGroup.mk'_surjective A)
  have hcommQuot : ∀ a b : (G ⧸ A) ⧸ B, a * b = b * a := by
    intro a b
    obtain ⟨a0, rfl⟩ := QuotientGroup.mk'_surjective B a
    obtain ⟨b0, rfl⟩ := QuotientGroup.mk'_surjective B b
    change (QuotientGroup.mk' B) (a0 * b0) = (QuotientGroup.mk' B) (b0 * a0)
    rw [hcomm a0 b0]
  let eQ : (G ⧸ A) ⧸ B ≃* G ⧸ W :=
    QuotientGroup.quotientQuotientEquivQuotient A W hAW
  have hcommGW : ∀ a b : G ⧸ W, a * b = b * a := by
    intro a b
    have h := hcommQuot (eQ.symm a) (eQ.symm b)
    simpa using congrArg eQ h
  obtain ⟨eD3⟩ := hGW
  have hcommD3 : ∀ a b : DihedralGroup 3, a * b = b * a := by
    intro a b
    have h := hcommGW (eD3.symm a) (eD3.symm b)
    simpa using congrArg eD3 h
  have hD3not : ¬ ∀ a b : DihedralGroup 3, a * b = b * a := by
    decide +kernel
  exact hD3not hcommD3

/-- The cyclic order-`18` quotient case is incompatible with the `S₃` quotient layer. -/
theorem order72_not_order18_RA_quotient_of_D3_layer
    {A W : Subgroup G} [A.Normal] [W.Normal] (hAW : A ≤ W)
    (hGW : Nonempty (G ⧸ W ≃* DihedralGroup 3)) :
    ¬ Nonempty (G ⧸ A ≃* Smallgroups.Classifications.Order18.RA) := by
  intro hQ
  obtain ⟨eQ⟩ := hQ
  exact order72_quotient_not_comm_of_D3_quotient hAW hGW (by
    intro a b
    apply eQ.injective
    rw [map_mul, map_mul, mul_comm])

/-- The abelian `C₃ × C₆` order-`18` quotient case is incompatible with the
`S₃` quotient layer. -/
theorem order72_not_order18_RB_quotient_of_D3_layer
    {A W : Subgroup G} [A.Normal] [W.Normal] (hAW : A ≤ W)
    (hGW : Nonempty (G ⧸ W ≃* DihedralGroup 3)) :
    ¬ Nonempty (G ⧸ A ≃* Smallgroups.Classifications.Order18.RB) := by
  intro hQ
  obtain ⟨eQ⟩ := hQ
  exact order72_quotient_not_comm_of_D3_quotient hAW hGW (by
    intro a b
    apply eQ.injective
    rw [map_mul, map_mul, mul_comm])

/-- In the `S₄` branch, the quotient by the normal Klein complement cannot be one of
the two abelian order-`18` groups; only the three non-abelian order-`18` cases remain. -/
theorem order72_S4_quotient_normal_klein_complement_nonabelian_order18_cases [Finite G]
    (hG : Nat.card G = 72) (K : Subgroup G) [K.Normal] (hK : Nat.card K = 3)
    (hquot : Nonempty (G ⧸ K ≃* order72_S4)) :
    ∃ (W : Subgroup G) (_ : W.Normal), K ≤ W ∧ Nat.card W = 12 ∧
      K.subgroupOf W ≤ Subgroup.center W ∧
        Nonempty (G ⧸ W ≃* DihedralGroup 3) ∧
          ∃ L : Subgroup W, (K.subgroupOf W).IsComplement' L ∧ Nat.card L = 4 ∧
            ∃ _ : (L.map W.subtype : Subgroup G).Normal,
              Nat.card (G ⧸ (L.map W.subtype : Subgroup G)) = 18 ∧
                (Nonempty ((G ⧸ (L.map W.subtype : Subgroup G)) ≃*
                    Smallgroups.Classifications.Order18.RC) ∨
                  Nonempty ((G ⧸ (L.map W.subtype : Subgroup G)) ≃*
                    Smallgroups.Classifications.Order18.RD) ∨
                  Nonempty ((G ⧸ (L.map W.subtype : Subgroup G)) ≃*
                    Smallgroups.Classifications.Order18.RE)) := by
  obtain ⟨W, hWnormal, hKW, hWcard, hKcenterW, hGWquot, L, hLcomp, hLcard,
    hLnormal, hquot18, hQcases⟩ :=
    order72_S4_quotient_normal_klein_complement_order18_cases
      (G := G) hG K hK hquot
  haveI : W.Normal := hWnormal
  let A : Subgroup G := L.map W.subtype
  haveI : A.Normal := hLnormal
  have hAW : A ≤ W := by
    dsimp [A]
    exact Subgroup.map_subtype_le L
  have hnotRA : ¬ Nonempty (G ⧸ A ≃* Smallgroups.Classifications.Order18.RA) :=
    order72_not_order18_RA_quotient_of_D3_layer hAW hGWquot
  have hnotRB : ¬ Nonempty (G ⧸ A ≃* Smallgroups.Classifications.Order18.RB) :=
    order72_not_order18_RB_quotient_of_D3_layer hAW hGWquot
  have hnonab :
      Nonempty (G ⧸ A ≃* Smallgroups.Classifications.Order18.RC) ∨
        Nonempty (G ⧸ A ≃* Smallgroups.Classifications.Order18.RD) ∨
          Nonempty (G ⧸ A ≃* Smallgroups.Classifications.Order18.RE) := by
    rcases hQcases with hRA | hRB | hRC | hRD | hRE
    · exact False.elim (hnotRA hRA)
    · exact False.elim (hnotRB hRB)
    · exact Or.inl hRC
    · exact Or.inr (Or.inl hRD)
    · exact Or.inr (Or.inr hRE)
  exact ⟨W, hWnormal, hKW, hWcard, hKcenterW, hGWquot, L, hLcomp, hLcard,
    hLnormal, hquot18, hnonab⟩

theorem order72_two_quotient_product_map_injective
    {Q : Type*} [Group Q] (K N : Subgroup G) [K.Normal] [N.Normal]
    (hKN : Disjoint K N)
    (eS4 : G ⧸ K ≃* order72_S4) (eQ : G ⧸ N ≃* Q) :
    Function.Injective
      ((eS4.toMonoidHom.comp (QuotientGroup.mk' K)).prod
        (eQ.toMonoidHom.comp (QuotientGroup.mk' N))) := by
  let φ : G →* order72_S4 × Q :=
    (eS4.toMonoidHom.comp (QuotientGroup.mk' K)).prod
      (eQ.toMonoidHom.comp (QuotientGroup.mk' N))
  refine (injective_iff_map_eq_one φ).mpr ?_
  intro x hx
  have hxK : x ∈ K := by
    have hfst : eS4 ((QuotientGroup.mk' K) x) = 1 := by
      have h := congrArg Prod.fst hx
      simpa [φ] using h
    have hq : (QuotientGroup.mk' K) x = 1 := by
      apply eS4.injective
      simpa using hfst
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hq
  have hxN : x ∈ N := by
    have hsnd : eQ ((QuotientGroup.mk' N) x) = 1 := by
      have h := congrArg Prod.snd hx
      simpa [φ] using h
    have hq : (QuotientGroup.mk' N) x = 1 := by
      apply eQ.injective
      simpa using hsnd
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hq
  have hxbot : x ∈ (⊥ : Subgroup G) :=
    (disjoint_iff_inf_le.mp hKN) ⟨hxK, hxN⟩
  exact Subgroup.mem_bot.mp hxbot

theorem order72_two_quotient_product_range_mulEquiv
    {Q : Type*} [Group Q] (K N : Subgroup G) [K.Normal] [N.Normal]
    (hKN : Disjoint K N)
    (eS4 : G ⧸ K ≃* order72_S4) (eQ : G ⧸ N ≃* Q) :
    Nonempty (G ≃*
      ((eS4.toMonoidHom.comp (QuotientGroup.mk' K)).prod
        (eQ.toMonoidHom.comp (QuotientGroup.mk' N))).range) := by
  exact ⟨MonoidHom.ofInjective
    (order72_two_quotient_product_map_injective K N hKN eS4 eQ)⟩

theorem order72_two_quotient_product_range_proj_surjective
    {Q : Type*} [Group Q] (K N : Subgroup G) [K.Normal] [N.Normal]
    (eS4 : G ⧸ K ≃* order72_S4) (eQ : G ⧸ N ≃* Q) :
    let φ : G →* order72_S4 × Q :=
      (eS4.toMonoidHom.comp (QuotientGroup.mk' K)).prod
        (eQ.toMonoidHom.comp (QuotientGroup.mk' N))
    Function.Surjective (Prod.fst ∘ φ.range.subtype) ∧
      Function.Surjective (Prod.snd ∘ φ.range.subtype) := by
  intro φ
  constructor
  · intro a
    let q : G ⧸ K := eS4.symm a
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective K q
    refine ⟨⟨φ g, ⟨g, rfl⟩⟩, ?_⟩
    change eS4 ((QuotientGroup.mk' K) g) = a
    rw [hg]
    exact eS4.apply_symm_apply a
  · intro z
    let q : G ⧸ N := eQ.symm z
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N q
    refine ⟨⟨φ g, ⟨g, rfl⟩⟩, ?_⟩
    change eQ ((QuotientGroup.mk' N) g) = z
    rw [hg]
    exact eQ.apply_symm_apply z

theorem order72_two_quotient_product_range_goursatFst_eq_of_exact
    {Q : Type*} [Group Q] (K N : Subgroup G) [K.Normal] [N.Normal]
    (eS4 : G ⧸ K ≃* order72_S4) (eQ : G ⧸ N ≃* Q)
    (V : Subgroup order72_S4)
    (hN_le : ∀ {g : G}, g ∈ N → eS4 ((QuotientGroup.mk' K) g) ∈ V)
    (hV_lift : ∀ {a : order72_S4}, a ∈ V →
      ∃ g : G, g ∈ N ∧ eS4 ((QuotientGroup.mk' K) g) = a) :
    let φ : G →* order72_S4 × Q :=
      (eS4.toMonoidHom.comp (QuotientGroup.mk' K)).prod
        (eQ.toMonoidHom.comp (QuotientGroup.mk' N))
    φ.range.goursatFst = V := by
  intro φ
  ext a
  constructor
  · intro ha
    rw [Subgroup.mem_goursatFst] at ha
    rw [MonoidHom.mem_range] at ha
    obtain ⟨g, hg⟩ := ha
    have hgN : g ∈ N := by
      have hsnd : eQ ((QuotientGroup.mk' N) g) = 1 := by
        have h := congrArg Prod.snd hg
        simpa [φ] using h
      have hq : (QuotientGroup.mk' N) g = 1 := by
        apply eQ.injective
        simpa using hsnd
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hq
    have hfst : eS4 ((QuotientGroup.mk' K) g) = a := by
      have h := congrArg Prod.fst hg
      simpa [φ] using h
    rw [← hfst]
    exact hN_le hgN
  · intro ha
    rw [Subgroup.mem_goursatFst]
    rw [MonoidHom.mem_range]
    obtain ⟨g, hgN, hga⟩ := hV_lift ha
    refine ⟨g, ?_⟩
    apply Prod.ext
    · change eS4 ((QuotientGroup.mk' K) g) = a
      exact hga
    · have hq : (QuotientGroup.mk' N) g = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hgN
      change eQ ((QuotientGroup.mk' N) g) = 1
      rw [hq]
      simp

theorem order72_two_quotient_product_range_goursatSnd_eq_K_image
    {Q : Type*} [Group Q] (K N : Subgroup G) [K.Normal] [N.Normal]
    (eS4 : G ⧸ K ≃* order72_S4) (eQ : G ⧸ N ≃* Q) :
    let φ : G →* order72_S4 × Q :=
      (eS4.toMonoidHom.comp (QuotientGroup.mk' K)).prod
        (eQ.toMonoidHom.comp (QuotientGroup.mk' N))
    φ.range.goursatSnd =
      K.map (eQ.toMonoidHom.comp (QuotientGroup.mk' N)) := by
  intro φ
  ext q
  constructor
  · intro hq
    rw [Subgroup.mem_goursatSnd] at hq
    rw [MonoidHom.mem_range] at hq
    obtain ⟨g, hg⟩ := hq
    rw [Subgroup.mem_map]
    have hgK : g ∈ K := by
      have hfst : eS4 ((QuotientGroup.mk' K) g) = 1 := by
        have h := congrArg Prod.fst hg
        simpa [φ] using h
      have hmk : (QuotientGroup.mk' K) g = 1 := by
        apply eS4.injective
        simpa using hfst
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmk
    refine ⟨g, hgK, ?_⟩
    have hsnd := congrArg Prod.snd hg
    simpa [φ] using hsnd
  · intro hq
    rw [Subgroup.mem_goursatSnd]
    rw [MonoidHom.mem_range]
    rw [Subgroup.mem_map] at hq
    obtain ⟨k, hkK, hkq⟩ := hq
    refine ⟨k, ?_⟩
    apply Prod.ext
    · have hmk : (QuotientGroup.mk' K) k = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hkK
      change eS4 ((QuotientGroup.mk' K) k) = 1
      rw [hmk]
      simp
    · simpa [φ] using hkq

/-! ### Concrete standard fibers for the three non-abelian order-`18` quotients -/

/-- A quotient-map model of the standard `S₄ → S₃` map with kernel `V₄`. -/
noncomputable def order72_S4ToD3Quot : order72_S4 →* DihedralGroup 3 :=
  (Classical.choice order72_S4_quotient_V4_mulEquiv_D3).toMonoidHom.comp
    (QuotientGroup.mk' order72_S4_V4)

theorem order72_S4ToD3Quot_ker_eq_V4 :
    order72_S4ToD3Quot.ker = order72_S4_V4 := by
  let e : order72_S4 ⧸ order72_S4_V4 ≃* DihedralGroup 3 :=
    Classical.choice order72_S4_quotient_V4_mulEquiv_D3
  ext σ
  constructor
  · intro hσ
    rw [MonoidHom.mem_ker] at hσ
    have hq : (QuotientGroup.mk' order72_S4_V4) σ = 1 := by
      apply e.injective
      simpa [order72_S4ToD3Quot, e] using hσ
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hq
  · intro hσ
    rw [MonoidHom.mem_ker]
    have hq : (QuotientGroup.mk' order72_S4_V4) σ = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hσ
    change e ((QuotientGroup.mk' order72_S4_V4) σ) = 1
    rw [hq]
    simp

/-- The standard fiber product of `S₄ → S₃` with
`D₃ × C₃ → D₃`. -/
noncomputable def order72_S4_RD_fiber :
    Subgroup (order72_S4 × Smallgroups.Classifications.Order18.RD) where
  carrier := { p | order72_S4ToD3Quot p.1 = p.2.1 }
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change order72_S4ToD3Quot (x.1 * y.1) = x.2.1 * y.2.1
    rw [map_mul, hx, hy]
  inv_mem' := by
    intro x hx
    change order72_S4ToD3Quot x.1⁻¹ = x.2.1⁻¹
    rw [map_inv, hx]

/-- The `RD = D₃ × C₃` standard fiber is the direct product `C₃ × S₄`. -/
noncomputable def order72_S4_RD_fiber_mulEquiv_C3xS4 :
    order72_S4_RD_fiber ≃* order72_res_C3xS4 where
  toFun x := (x.1.2.2, x.1.1)
  invFun y := ⟨(y.2, (order72_S4ToD3Quot y.2, y.1)), by rfl⟩
  left_inv := by
    intro x
    apply Subtype.ext
    rcases x with ⟨⟨s, q⟩, hx⟩
    change order72_S4ToD3Quot s = q.1 at hx
    ext <;> simp [hx]
  right_inv := by
    intro y
    rfl
  map_mul' := by
    intro x y
    rfl

/-- The rotation factor of `RD = D₃ × C₃`.  Quotienting by this subgroup leaves the
abelian `C₂ × C₃` quotient. -/
noncomputable def order72_RD_rotationKernel :
    Subgroup Smallgroups.Classifications.Order18.RD :=
  (Subgroup.zpowers (DihedralGroup.r (1 : ZMod 3))).prod
    (⊥ : Subgroup (CyclicRep 3))

/-- The central `C₃` factor of `RD = D₃ × C₃`.  This is the kernel of the standard
projection to `D₃`. -/
noncomputable def order72_RD_centralKernel :
    Subgroup Smallgroups.Classifications.Order18.RD :=
  (⊥ : Subgroup (DihedralGroup 3)).prod
    (⊤ : Subgroup (CyclicRep 3))

theorem order72_RD_fst_ker_eq_centralKernel :
    (MonoidHom.fst (DihedralGroup 3) (CyclicRep 3)).ker =
      order72_RD_centralKernel := by
  ext x
  rw [MonoidHom.mem_ker]
  change x.1 = 1 ↔ x ∈
    (⊥ : Subgroup (DihedralGroup 3)).prod (⊤ : Subgroup (CyclicRep 3))
  rw [Subgroup.mem_prod, Subgroup.mem_bot]
  simp

theorem order72_RD_fst_range_top :
    (MonoidHom.fst (DihedralGroup 3) (CyclicRep 3)).range = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro d
  rw [MonoidHom.mem_range]
  exact ⟨(d, 1), rfl⟩

theorem order72_RD_centralKernel_normal :
    order72_RD_centralKernel.Normal := by
  dsimp [order72_RD_centralKernel]
  infer_instance

local instance instOrder72RDCentralKernelNormal :
    order72_RD_centralKernel.Normal :=
  order72_RD_centralKernel_normal

noncomputable def order72_RD_quotientCentralKernel_mulEquiv_D3 :
    Smallgroups.Classifications.Order18.RD ⧸ order72_RD_centralKernel ≃*
      DihedralGroup 3 :=
  (QuotientGroup.quotientMulEquivOfEq order72_RD_fst_ker_eq_centralKernel.symm).trans
    (((QuotientGroup.quotientKerEquivRange
      (MonoidHom.fst (DihedralGroup 3) (CyclicRep 3))).trans
        (MulEquiv.subgroupCongr order72_RD_fst_range_top)).trans Subgroup.topEquiv)

theorem order72_RD_quotientCentralKernel_mk (q : Smallgroups.Classifications.Order18.RD) :
    order72_RD_quotientCentralKernel_mulEquiv_D3
      ((QuotientGroup.mk' order72_RD_centralKernel) q) = q.1 := by
  rfl

set_option linter.flexible false in
theorem order72_RD_normal_order_three_eq_rotation_or_central
    (U : Subgroup Smallgroups.Classifications.Order18.RD) [U.Normal]
    (hU : Nat.card U = 3) :
    U = order72_RD_rotationKernel ∨ U = order72_RD_centralKernel := by
  classical
  have hrotCard : Nat.card order72_RD_rotationKernel = 3 := by
    dsimp [order72_RD_rotationKernel]
    rw [Nat.card_congr
      ((Subgroup.prodEquiv (Subgroup.zpowers (DihedralGroup.r (1 : ZMod 3)))
        (⊥ : Subgroup (CyclicRep 3))).toEquiv)]
    rw [Nat.card_prod, Nat.card_zpowers, DihedralGroup.orderOf_r_one]
    simp
  have hcentCard : Nat.card order72_RD_centralKernel = 3 := by
    dsimp [order72_RD_centralKernel]
    rw [Nat.card_congr
      ((Subgroup.prodEquiv (⊥ : Subgroup (DihedralGroup 3))
        (⊤ : Subgroup (CyclicRep 3))).toEquiv)]
    rw [Nat.card_prod]
    simp [CyclicRep]
  by_cases hr : (DihedralGroup.r (1 : ZMod 3), (1 : CyclicRep 3)) ∈ U
  · left
    have hRleU : order72_RD_rotationKernel ≤ U := by
      intro x hx
      rcases x with ⟨d, z⟩
      change (d, z) ∈ (Subgroup.zpowers (DihedralGroup.r (1 : ZMod 3))).prod
        (⊥ : Subgroup (CyclicRep 3)) at hx
      rw [Subgroup.mem_prod] at hx
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx.1
      simp only [DihedralGroup.r_zpow, one_mul] at hn
      have hz : z = 1 := Subgroup.mem_bot.mp hx.2
      rw [hz, ← hn]
      simpa using U.zpow_mem hr n
    exact (Subgroup.eq_of_le_of_card_ge hRleU (by rw [hU, hrotCard])).symm
  · right
    apply Subgroup.eq_of_le_of_card_ge
    · intro x hx
      rw [order72_RD_centralKernel, Subgroup.mem_prod]
      constructor
      · rw [Subgroup.mem_bot]
        rcases x with ⟨d, c⟩
        have hx3U : (⟨(d, c), hx⟩ : U) ^ 3 = 1 := by
          have hdvd := orderOf_dvd_natCard (⟨(d, c), hx⟩ : U)
          rw [hU] at hdvd
          exact orderOf_dvd_iff_pow_eq_one.mp hdvd
        have hx3 : ((d, c) : Smallgroups.Classifications.Order18.RD) ^ 3 = 1 :=
          congrArg (fun y : U => (y : Smallgroups.Classifications.Order18.RD)) hx3U
        cases d with
        | sr i =>
            exfalso
            have hfirst := congrArg Prod.fst hx3
            simp only [pow_succ, pow_zero, one_mul, Prod.mk_mul_mk, DihedralGroup.sr_mul_sr,
            sub_self, DihedralGroup.r_zero,Prod.fst_one] at hfirst
            exact (by decide +kernel +revert : ∀ i : ZMod 3,
              (DihedralGroup.sr i : DihedralGroup 3) ≠ 1) i hfirst
        | r i =>
            fin_cases i
            · rfl
            · exfalso
              let t : Smallgroups.Classifications.Order18.RD :=
                (DihedralGroup.sr (0 : ZMod 3), (1 : CyclicRep 3))
              have hconj : t * (DihedralGroup.r (1 : ZMod 3), c) * t⁻¹ ∈ U :=
                (inferInstance : U.Normal).conj_mem
                  (DihedralGroup.r (1 : ZMod 3), c) hx t
              have hgen : (DihedralGroup.r (1 : ZMod 3), (1 : CyclicRep 3)) ∈ U := by
                have hprod : (DihedralGroup.r (1 : ZMod 3), (1 : CyclicRep 3)) =
                    (((DihedralGroup.r (1 : ZMod 3), c) * (t *
                      (DihedralGroup.r (1 : ZMod 3), c) * t⁻¹)⁻¹) ^ 2) := by
                  ext <;> (simp [t]; try decide)
                rw [hprod]
                exact U.pow_mem (U.mul_mem hx (U.inv_mem hconj)) 2
              exact hr hgen
            · exfalso
              let t : Smallgroups.Classifications.Order18.RD :=
                (DihedralGroup.sr (0 : ZMod 3), (1 : CyclicRep 3))
              have hconj : t * (DihedralGroup.r (2 : ZMod 3), c) * t⁻¹ ∈ U :=
                (inferInstance : U.Normal).conj_mem
                  (DihedralGroup.r (2 : ZMod 3), c) hx t
              have hgen : (DihedralGroup.r (1 : ZMod 3), (1 : CyclicRep 3)) ∈ U := by
                have hprod : (DihedralGroup.r (1 : ZMod 3), (1 : CyclicRep 3)) =
                    (DihedralGroup.r (2 : ZMod 3), c) *
                      (t * (DihedralGroup.r (2 : ZMod 3), c) * t⁻¹)⁻¹ := by
                  ext <;> (simp [t]; try decide)
                rw [hprod]
                exact U.mul_mem hx (U.inv_mem hconj)
              exact hr hgen
      · exact Subgroup.mem_top x.2
    · rw [hU, hcentCard]

noncomputable def order72_S4_RD_twistedFiber (σ : MulAut (DihedralGroup 3)) :
    Subgroup (order72_S4 × Smallgroups.Classifications.Order18.RD) where
  carrier := { p | σ (order72_S4ToD3Quot p.1) = p.2.1 }
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change σ (order72_S4ToD3Quot (x.1 * y.1)) = x.2.1 * y.2.1
    rw [map_mul, map_mul, hx, hy]
  inv_mem' := by
    intro x hx
    change σ (order72_S4ToD3Quot x.1⁻¹) = x.2.1⁻¹
    rw [map_inv, map_inv, hx]

noncomputable def order72_S4_RD_twistedFiber_mulEquiv_fiber
    (σ : MulAut (DihedralGroup 3)) :
    order72_S4_RD_twistedFiber σ ≃* order72_S4_RD_fiber where
  toFun x := ⟨(x.1.1, (σ.symm x.1.2.1, x.1.2.2)), by
    rcases x with ⟨⟨s, q⟩, hx⟩
    change order72_S4ToD3Quot s = (σ.symm q.1)
    change σ (order72_S4ToD3Quot s) = q.1 at hx
    rw [← hx]
    simp⟩
  invFun x := ⟨(x.1.1, (σ x.1.2.1, x.1.2.2)), by
    rcases x with ⟨⟨s, q⟩, hx⟩
    change σ (order72_S4ToD3Quot s) = σ q.1
    change order72_S4ToD3Quot s = q.1 at hx
    rw [hx]⟩
  left_inv := by
    intro x
    apply Subtype.ext
    rcases x with ⟨⟨s, q⟩, hx⟩
    ext <;> simp
  right_inv := by
    intro x
    apply Subtype.ext
    rcases x with ⟨⟨s, q⟩, hx⟩
    ext <;> simp
  map_mul' := by
    intro x y
    apply Subtype.ext
    rcases x with ⟨⟨sx, dx, cx⟩, hx⟩
    rcases y with ⟨⟨sy, dy, cy⟩, hy⟩
    ext <;> simp [map_mul]

theorem order72_S4_RD_subgroup_mulEquiv_C3xS4_of_goursat
    (I : Subgroup (order72_S4 × Smallgroups.Classifications.Order18.RD))
    (hI₁ : Function.Surjective (Prod.fst ∘ I.subtype))
    (hI₂ : Function.Surjective (Prod.snd ∘ I.subtype))
    (hF : I.goursatFst = order72_S4_V4)
    (hS : I.goursatSnd = order72_RD_centralKernel) :
    Nonempty (I ≃* order72_res_C3xS4) := by
  haveI : I.goursatFst.Normal := Subgroup.normal_goursatFst hI₁
  haveI : I.goursatSnd.Normal := Subgroup.normal_goursatSnd hI₂
  obtain ⟨e, he⟩ := Subgroup.goursat_surjective hI₁ hI₂
  let eS4 : order72_S4 ⧸ order72_S4_V4 ≃* DihedralGroup 3 :=
    Classical.choice order72_S4_quotient_V4_mulEquiv_D3
  let eF : order72_S4 ⧸ order72_S4_V4 ≃* order72_S4 ⧸ I.goursatFst :=
    QuotientGroup.quotientMulEquivOfEq hF.symm
  let eS : Smallgroups.Classifications.Order18.RD ⧸ I.goursatSnd ≃*
      Smallgroups.Classifications.Order18.RD ⧸ order72_RD_centralKernel :=
    QuotientGroup.quotientMulEquivOfEq hS
  let eRD : Smallgroups.Classifications.Order18.RD ⧸ order72_RD_centralKernel ≃*
      DihedralGroup 3 := order72_RD_quotientCentralKernel_mulEquiv_D3
  let σ : MulAut (DihedralGroup 3) := ((eS4.symm.trans eF).trans e).trans (eS.trans eRD)
  have hIeq : I = order72_S4_RD_twistedFiber σ := by
    ext x
    constructor
    · intro hx
      change σ (order72_S4ToD3Quot x.1) = x.2.1
      have hgraph : e ((QuotientGroup.mk' I.goursatFst) x.1) =
          (QuotientGroup.mk' I.goursatSnd) x.2 := by
        have hmem : (((QuotientGroup.mk' I.goursatFst).prodMap
            (QuotientGroup.mk' I.goursatSnd)).comp I.subtype) ⟨x, hx⟩ ∈
              e.toMonoidHom.graph := by
          rw [← he]
          exact ⟨⟨x, hx⟩, rfl⟩
        simpa [MonoidHom.mem_graph] using hmem
      have htarget :
          eRD (eS (e ((QuotientGroup.mk' I.goursatFst) x.1))) = x.2.1 := by
        rw [hgraph]
        exact order72_RD_quotientCentralKernel_mk x.2
      simpa [σ, eS4, eF, eS, eRD, order72_S4ToD3Quot] using htarget
    · intro hx
      change σ (order72_S4ToD3Quot x.1) = x.2.1 at hx
      have hgraph : e ((QuotientGroup.mk' I.goursatFst) x.1) =
          (QuotientGroup.mk' I.goursatSnd) x.2 := by
        have hσ :
            eRD (eS (e ((QuotientGroup.mk' I.goursatFst) x.1))) =
              x.2.1 := by
          simpa [σ, eS4, eF, eS, eRD, order72_S4ToD3Quot,
            order72_RD_quotientCentralKernel_mk] using hx
        have hright :
            eRD (eS ((QuotientGroup.mk' I.goursatSnd) x.2)) = x.2.1 := by
          exact order72_RD_quotientCentralKernel_mk x.2
        apply eS.injective
        apply eRD.injective
        exact hσ.trans hright.symm
      have hmemGraph :
          ((QuotientGroup.mk' I.goursatFst).prodMap
            (QuotientGroup.mk' I.goursatSnd)) x ∈ e.toMonoidHom.graph := by
        simpa [MonoidHom.mem_graph] using hgraph
      have hmemRange :
          ((QuotientGroup.mk' I.goursatFst).prodMap
            (QuotientGroup.mk' I.goursatSnd)) x ∈
              (((QuotientGroup.mk' I.goursatFst).prodMap
                (QuotientGroup.mk' I.goursatSnd)).comp I.subtype).range := by
        rw [he]
        exact hmemGraph
      obtain ⟨y, hy⟩ := hmemRange
      rcases y with ⟨⟨a, b⟩, hyI⟩
      have hqa : (QuotientGroup.mk' I.goursatFst) x.1 =
          (QuotientGroup.mk' I.goursatFst) a := by
        exact congrArg Prod.fst hy.symm
      have hqb : (QuotientGroup.mk' I.goursatSnd) x.2 =
          (QuotientGroup.mk' I.goursatSnd) b := by
        exact congrArg Prod.snd hy.symm
      have haDiff : x.1 * a⁻¹ ∈ I.goursatFst := by
        have hraw : x.1⁻¹ * a ∈ I.goursatFst := QuotientGroup.eq.mp hqa
        have hrawInv : a⁻¹ * x.1 ∈ I.goursatFst := by
          simpa [div_eq_mul_inv] using I.goursatFst.inv_mem hraw
        have hconj := (inferInstance : I.goursatFst.Normal).conj_mem
          (a⁻¹ * x.1) hrawInv x.1
        simpa [mul_assoc] using hconj
      have hbDiff : x.2 * b⁻¹ ∈ I.goursatSnd := by
        have hraw : x.2⁻¹ * b ∈ I.goursatSnd := QuotientGroup.eq.mp hqb
        have hrawInv : b⁻¹ * x.2 ∈ I.goursatSnd := by
          simpa [div_eq_mul_inv] using I.goursatSnd.inv_mem hraw
        have hconj := (inferInstance : I.goursatSnd.Normal).conj_mem
          (b⁻¹ * x.2) hrawInv x.2
        simpa [mul_assoc] using hconj
      have hdiff : (x.1 * a⁻¹, x.2 * b⁻¹) ∈ I :=
        (Subgroup.goursatFst_prod_goursatSnd_le I) ⟨haDiff, hbDiff⟩
      have hprod : (x.1 * a⁻¹, x.2 * b⁻¹) * (a, b) = x := by
        ext <;> simp [mul_assoc]
      rw [← hprod]
      exact I.mul_mem hdiff hyI
  exact ⟨(MulEquiv.subgroupCongr hIeq).trans
    ((order72_S4_RD_twistedFiber_mulEquiv_fiber σ).trans
      order72_S4_RD_fiber_mulEquiv_C3xS4)⟩

theorem order72_S4_RD_branch_mulEquiv_C3xS4_of_central_kernel
    [Finite G] {K W : Subgroup G} [K.Normal] [W.Normal]
    (_hKW : K ≤ W) (_hKcard : Nat.card K = 3) {L : Subgroup W}
    (hLcomp : (K.subgroupOf W).IsComplement' L)
    [(L.map W.subtype : Subgroup G).Normal]
    (eS4 : G ⧸ K ≃* order72_S4)
    (eRD : G ⧸ (L.map W.subtype : Subgroup G) ≃*
      Smallgroups.Classifications.Order18.RD)
    (hL_le_V : ∀ {g : G}, g ∈ (L.map W.subtype : Subgroup G) →
      eS4 ((QuotientGroup.mk' K) g) ∈ order72_S4_V4)
    (hV_liftL : ∀ {a : order72_S4}, a ∈ order72_S4_V4 →
      ∃ g : G, g ∈ (L.map W.subtype : Subgroup G) ∧
        eS4 ((QuotientGroup.mk' K) g) = a)
    (hKimage : K.map (eRD.toMonoidHom.comp
      (QuotientGroup.mk' (L.map W.subtype : Subgroup G))) =
        order72_RD_centralKernel) :
    Nonempty (G ≃* order72_res_C3xS4) := by
  let N : Subgroup G := L.map W.subtype
  haveI : N.Normal := (inferInstance : (L.map W.subtype : Subgroup G).Normal)
  have hKN : Disjoint K N := by
    dsimp [N]
    exact order36_C3_layer_disjoint_klein_complement_map K W hLcomp
  let φ : G →* order72_S4 × Smallgroups.Classifications.Order18.RD :=
    (eS4.toMonoidHom.comp (QuotientGroup.mk' K)).prod
      (eRD.toMonoidHom.comp (QuotientGroup.mk' N))
  have hG_range : Nonempty (G ≃* φ.range) := by
    dsimp [φ]
    exact order72_two_quotient_product_range_mulEquiv K N hKN eS4 eRD
  have hproj := order72_two_quotient_product_range_proj_surjective K N eS4 eRD
  have hF : φ.range.goursatFst = order72_S4_V4 := by
    dsimp [φ]
    exact order72_two_quotient_product_range_goursatFst_eq_of_exact
      K N eS4 eRD order72_S4_V4 hL_le_V hV_liftL
  have hS : φ.range.goursatSnd = order72_RD_centralKernel := by
    have hS0 := order72_two_quotient_product_range_goursatSnd_eq_K_image
      K N eS4 eRD
    dsimp [φ, N] at hS0 hKimage ⊢
    rw [hS0]
    exact hKimage
  obtain ⟨eGI⟩ := hG_range
  obtain ⟨eI⟩ :=
    order72_S4_RD_subgroup_mulEquiv_C3xS4_of_goursat
      φ.range hproj.1 hproj.2 hF hS
  exact ⟨eGI.trans eI⟩

theorem order72_RD_rotationKernel_normal :
    order72_RD_rotationKernel.Normal := by
  let R : Subgroup (DihedralGroup 3) := Subgroup.zpowers (DihedralGroup.r (1 : ZMod 3))
  have hRcard : Nat.card R = 3 := by
    dsimp [R]
    rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one]
  have hD3 : Nat.card (DihedralGroup 3) = 6 := by
    rw [DihedralGroup.nat_card]
  have hRindex : R.index = 2 := by
    have hmul := R.card_mul_index
    rw [hRcard, hD3] at hmul
    omega
  haveI : R.Normal := Subgroup.normal_of_index_eq_two hRindex
  change (R.prod (⊥ : Subgroup (CyclicRep 3))).Normal
  infer_instance

local instance instOrder72RDRotationKernelNormal :
    order72_RD_rotationKernel.Normal :=
  order72_RD_rotationKernel_normal

theorem order72_D3_rotation_mem_zpowers (i : ZMod 3) :
    DihedralGroup.r i ∈ Subgroup.zpowers (DihedralGroup.r (1 : ZMod 3)) := by
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨(i.val : ℤ), ?_⟩
  rw [DihedralGroup.r_one_zpow]
  congr
  exact_mod_cast ZMod.natCast_zmod_val i

theorem order72_RD_rotationKernel_quotient_comm :
    ∀ a b : Smallgroups.Classifications.Order18.RD ⧸ order72_RD_rotationKernel,
      a * b = b * a := by
  haveI : order72_RD_rotationKernel.Normal := order72_RD_rotationKernel_normal
  intro a b
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective order72_RD_rotationKernel a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective order72_RD_rotationKernel b
  change (QuotientGroup.mk' order72_RD_rotationKernel) (x * y) =
    (QuotientGroup.mk' order72_RD_rotationKernel) (y * x)
  apply QuotientGroup.eq.mpr
  rcases x with ⟨xd, xc⟩
  rcases y with ⟨yd, yc⟩
  change ((xd, xc) * (yd, yc))⁻¹ * ((yd, yc) * (xd, xc)) ∈
    (Subgroup.zpowers (DihedralGroup.r (1 : ZMod 3))).prod
      (⊥ : Subgroup (CyclicRep 3))
  rw [Subgroup.mem_prod]
  constructor
  · cases xd <;> cases yd <;>
      simp [order72_D3_rotation_mem_zpowers]
  · rw [Subgroup.mem_bot]
    change (xc * yc)⁻¹ * (yc * xc) = 1
    rw [mul_comm yc xc]
    simp

/-- For a fixed quotient isomorphism `G/K ≃ S₄`, the quotient by the Klein-four
preimage is `S₄/V₄ ≃ S₃`. -/
theorem order72_S4_equiv_klein_preimage_top_quotient_D3 [Finite G]
    (hG : Nat.card G = 72) (K : Subgroup G) [K.Normal] (_hK : Nat.card K = 3)
    (e : G ⧸ K ≃* order72_S4) :
    ∃ (W : Subgroup G) (_ : W.Normal), K ≤ W ∧ Nat.card W = 12 ∧
      Nonempty (G ⧸ W ≃* DihedralGroup 3) := by
  let φ : G →* order72_S4 := e.toMonoidHom.comp (QuotientGroup.mk' K)
  let V : Subgroup order72_S4 := order72_S4_V4
  let W : Subgroup G := V.comap φ
  have hVnormal : V.Normal := by
    dsimp [V]
    exact order72_S4_V4_normal
  have hWnormal : W.Normal := by
    dsimp [W]
    exact hVnormal.comap φ
  have hKW : K ≤ W := by
    intro k hk
    have hkq : (QuotientGroup.mk' K) k = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hk
    have hφk : φ k = 1 := by
      change e ((QuotientGroup.mk' K) k) = 1
      rw [hkq]
      simp
    change φ k ∈ V
    rw [hφk]
    exact V.one_mem
  have hφ_surj : Function.Surjective φ := by
    intro a
    obtain ⟨q, hq⟩ := e.surjective a
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective K q
    refine ⟨g, ?_⟩
    change e ((QuotientGroup.mk' K) g) = a
    rw [hg, hq]
  have hV_card : Nat.card V = 4 := by
    dsimp [V]
    exact order72_S4_V4_card
  have hV_index : V.index = 6 := by
    have hmul := V.index_mul_card
    rw [hV_card] at hmul
    have hS4 : Nat.card order72_S4 = 24 := by
      rw [Nat.card_perm, Nat.card_fin]
      norm_num [Nat.factorial]
    rw [hS4] at hmul
    omega
  have hW_index : W.index = 6 := by
    dsimp [W]
    rw [V.index_comap_of_surjective hφ_surj, hV_index]
  have hWcard : Nat.card W = 12 := by
    have hmul := W.index_mul_card
    rw [hW_index, hG] at hmul
    omega
  haveI : W.Normal := hWnormal
  haveI : V.Normal := hVnormal
  let θ : G ⧸ W →* order72_S4 ⧸ V :=
    QuotientGroup.map W V φ (by
      intro g hgW
      exact hgW)
  have hθinj : Function.Injective θ := by
    refine (injective_iff_map_eq_one θ).mpr ?_
    intro q hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective W q
    have hgV : φ g ∈ V := by
      change (QuotientGroup.mk' V) (φ g) = 1 at hq
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hq
    change (QuotientGroup.mk' W) g = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hgV
  have hθsurj : Function.Surjective θ := by
    intro q
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective V q
    obtain ⟨g, hg⟩ := hφ_surj s
    refine ⟨(QuotientGroup.mk' W) g, ?_⟩
    change (QuotientGroup.mk' V) (φ g) = (QuotientGroup.mk' V) s
    rw [hg]
  let eθ : G ⧸ W ≃* order72_S4 ⧸ V := MulEquiv.ofBijective θ ⟨hθinj, hθsurj⟩
  obtain ⟨eS3⟩ := order72_S4_quotient_V4_mulEquiv_D3
  exact ⟨W, hWnormal, hKW, hWcard, ⟨eθ.trans eS3⟩⟩

/-- In the `S₄` quotient branch, the Klein-four preimage contains a complement to the
order-`3` kernel. -/
theorem order72_S4_quotient_klein_preimage_complement [Finite G]
    (hG : Nat.card G = 72) (K : Subgroup G) [K.Normal] (hK : Nat.card K = 3)
    (hquot : Nonempty (G ⧸ K ≃* order72_S4)) :
    ∃ (W : Subgroup G) (_ : W.Normal), K ≤ W ∧ Nat.card W = 12 ∧
      Nonempty (W ⧸ K.subgroupOf W ≃* order72_S4_V4) ∧
        ∃ L : Subgroup W, (K.subgroupOf W).IsComplement' L ∧ Nat.card L = 4 := by
  obtain ⟨W, hWnormal, hKW, hWcard, hWquot⟩ :=
    order72_S4_quotient_klein_preimage (G := G) hG K hK hquot
  have hKWcard : Nat.card (K.subgroupOf W) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKW).toEquiv, hK]
  have hKWindex : (K.subgroupOf W).index = 4 := by
    have hmul := (K.subgroupOf W).index_mul_card
    rw [hKWcard, hWcard] at hmul
    omega
  have hcop : Nat.Coprime (Nat.card (K.subgroupOf W)) (K.subgroupOf W).index := by
    rw [hKWcard, hKWindex]
    norm_num
  haveI : (K.subgroupOf W).Normal := by infer_instance
  obtain ⟨L, hLcomp⟩ := Subgroup.exists_right_complement'_of_coprime
    (N := K.subgroupOf W) hcop
  have hLcard : Nat.card L = 4 := by
    have hindex := (Subgroup.IsComplement'.symm hLcomp).index_eq_card
    rw [hKWindex] at hindex
    exact hindex.symm
  exact ⟨W, hWnormal, hKW, hWcard, hWquot, L, hLcomp, hLcard⟩

/-- The preimage of `A₄ ≤ S₄` centralizes a normal order-`3` kernel. -/
theorem order72_S4_quotient_alt_preimage_kernel_le_center [Finite G]
    (K : Subgroup G) [K.Normal] (hK : Nat.card K = 3)
    (hquot : Nonempty (G ⧸ K ≃* order72_S4)) :
    ∃ (A : Subgroup G) (_ : A.Normal), K ≤ A ∧ Nat.card A = 36 ∧
      Nonempty (A ⧸ K.subgroupOf A ≃* alternatingGroup (Fin 4)) ∧
        K.subgroupOf A ≤ Subgroup.center A := by
  obtain ⟨e⟩ := hquot
  let φ : G →* order72_S4 := e.toMonoidHom.comp (QuotientGroup.mk' K)
  let A : Subgroup G := (alternatingGroup (Fin 4) : Subgroup order72_S4).comap φ
  have hAnormal : A.Normal := by
    dsimp [A]
    exact (alternatingGroup.normal : (alternatingGroup (Fin 4) :
    Subgroup order72_S4).Normal).comap φ
  have hKA : K ≤ A := by
    intro k hk
    have hkq : (QuotientGroup.mk' K) k = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hk
    have hφk : φ k = 1 := by
      change e ((QuotientGroup.mk' K) k) = 1
      rw [hkq]
      simp
    change φ k ∈ (alternatingGroup (Fin 4) : Subgroup order72_S4)
    rw [hφk]
    exact Subgroup.one_mem _
  have hφ_surj : Function.Surjective φ := by
    intro a
    obtain ⟨q, hq⟩ := e.surjective a
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective K q
    refine ⟨g, ?_⟩
    change e ((QuotientGroup.mk' K) g) = a
    rw [hg, hq]
  have hAlt_card : Nat.card (alternatingGroup (Fin 4)) = 12 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  have hS4_card : Nat.card order72_S4 = 24 := by
    rw [Nat.card_perm, Nat.card_fin]
    norm_num [Nat.factorial]
  have hAlt_index : (alternatingGroup (Fin 4) : Subgroup order72_S4).index = 2 := by
    have hmul := (alternatingGroup (Fin 4) : Subgroup order72_S4).index_mul_card
    rw [hAlt_card, hS4_card] at hmul
    omega
  have hA_index : A.index = 2 := by
    let Alt : Subgroup order72_S4 := alternatingGroup (Fin 4)
    change (Alt.comap φ).index = 2
    rw [Alt.index_comap_of_surjective hφ_surj, hAlt_index]
  have hAcard : Nat.card A = 36 := by
    have hmul := A.index_mul_card
    rw [hA_index] at hmul
    have hG : Nat.card G = 72 := by
      have hquotcard : Nat.card (G ⧸ K) = 24 := by
        exact (Nat.card_congr e.toEquiv).trans hS4_card
      have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup K
      rw [hquotcard, hK] at hcard
      exact hcard
    rw [hG] at hmul
    omega
  let φA : A →* order72_S4 := φ.comp A.subtype
  have hφAker : φA.ker = K.subgroupOf A := by
    ext a
    constructor
    · intro ha
      rw [MonoidHom.mem_ker] at ha
      rw [Subgroup.mem_subgroupOf]
      have hq : (QuotientGroup.mk' K) (a : G) = 1 := by
        apply e.injective
        simpa [φA, φ] using ha
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hq
    · intro ha
      rw [Subgroup.mem_subgroupOf] at ha
      rw [MonoidHom.mem_ker]
      have hq : (QuotientGroup.mk' K) (a : G) = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact ha
      change e ((QuotientGroup.mk' K) (a : G)) = 1
      rw [hq]
      simp
  have hφArange : φA.range = (alternatingGroup (Fin 4) : Subgroup order72_S4) := by
    apply le_antisymm
    · intro a ha
      rw [MonoidHom.mem_range] at ha
      obtain ⟨x, hx⟩ := ha
      rw [← hx]
      change φ (x : G) ∈ (alternatingGroup (Fin 4) : Subgroup order72_S4)
      exact x.property
    · intro a ha
      rw [MonoidHom.mem_range]
      obtain ⟨g, hg⟩ := hφ_surj a
      have hgA : g ∈ A := by
        change φ g ∈ (alternatingGroup (Fin 4) : Subgroup order72_S4)
        rw [hg]
        exact ha
      refine ⟨⟨g, hgA⟩, ?_⟩
      change φ g = a
      exact hg
  haveI : (K.subgroupOf A).Normal := hφAker ▸ MonoidHom.normal_ker φA
  have hAquot : Nonempty (A ⧸ K.subgroupOf A ≃* alternatingGroup (Fin 4)) := by
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hφAker.symm).trans
      ((QuotientGroup.quotientKerEquivRange φA).trans (MulEquiv.subgroupCongr hφArange))⟩
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  obtain ⟨eK⟩ : Nonempty (K ≃* order72_C3) := by
    simpa [order72_C3, CyclicRep] using
      (prime_classification (G := K) (p := 3) (by norm_num) hK)
  have hKcomm : ∀ x y : K, x * y = y * x := by
    intro x y
    apply eK.injective
    rw [map_mul, map_mul, mul_comm]
  have hAutK : Nat.card (MulAut K) = 2 := by
    rw [Nat.card_congr (MulAut.congr eK).toEquiv]
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  let act : G →* MulAut K := MulAut.conjNormal
  have hKker : K ≤ act.ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change k * (x : G) * k⁻¹ = (x : G)
    have hcomm : (⟨k, hk⟩ : K) * x = x * ⟨k, hk⟩ := hKcomm _ _
    have hcommG : k * (x : G) = (x : G) * k := congrArg Subtype.val hcomm
    calc
      k * (x : G) * k⁻¹ = ((x : G) * k) * k⁻¹ := by rw [hcommG]
      _ = (x : G) := by group
  let actQ : G ⧸ K →* MulAut K := QuotientGroup.lift K act hKker
  let χ : order72_S4 →* MulAut K := actQ.comp e.symm.toMonoidHom
  let χA : alternatingGroup (Fin 4) →* MulAut K :=
    χ.comp (alternatingGroup (Fin 4)).subtype
  have hχA : χA = 1 := order36_A4_hom_to_order_two_trivial hAutK χA
  refine ⟨A, hAnormal, hKA, hAcard, hAquot, ?_⟩
  intro k hkA
  rw [Subgroup.mem_center_iff]
  intro a
  have haAlt : χA ⟨φ (a : G), a.property⟩ = 1 := by
    rw [hχA]
    rfl
  have hact : act (a : G) = 1 := by
    have hq : e.symm (φ (a : G)) = (QuotientGroup.mk' K) (a : G) := by
      dsimp [φ]
      rw [MulEquiv.symm_apply_apply]
    have hχ : χ (φ (a : G)) = 1 := by
      simpa [χA] using haAlt
    simpa [χ, actQ, hq] using hχ
  have happ : act (a : G) ⟨(k : A), Subgroup.mem_subgroupOf.mp hkA⟩ =
      ⟨(k : A), Subgroup.mem_subgroupOf.mp hkA⟩ := by
    rw [hact]
    rfl
  have hconj := congrArg (fun x : K => (x : G)) happ
  change (a : G) * ((k : A) : G) * (a : G)⁻¹ = ((k : A) : G) at hconj
  apply Subtype.ext
  change (a : G) * ((k : A) : G) = ((k : A) : G) * (a : G)
  calc
    (a : G) * ((k : A) : G) =
        ((a : G) * ((k : A) : G) * (a : G)⁻¹) * (a : G) := by group
    _ = ((k : A) : G) * (a : G) := by rw [hconj]

/-- In the `S₄` quotient branch, the preimage of `A₄` is one of the two non-normal
order-`36` representatives with an `A₄` quotient. -/
theorem order72_S4_quotient_alt_preimage_order36_cases [Finite G]
    (K : Subgroup G) [K.Normal] (hK : Nat.card K = 3)
    (hquot : Nonempty (G ⧸ K ≃* order72_S4)) :
    ∃ (A : Subgroup G) (_ : A.Normal), K ≤ A ∧ Nat.card A = 36 ∧
      Nonempty (A ⧸ K.subgroupOf A ≃* alternatingGroup (Fin 4)) ∧
        K.subgroupOf A ≤ Subgroup.center A ∧
          (Nonempty (A ≃* order36_A4C9) ∨ Nonempty (A ≃* order36_C3A4)) := by
  obtain ⟨A, hAnormal, hKA, hAcard, hAquot, hKcenterA⟩ :=
    order72_S4_quotient_alt_preimage_kernel_le_center
      (G := G) K hK hquot
  haveI : A.Normal := hAnormal
  haveI : (K.subgroupOf A).Normal := by infer_instance
  have hKsubcard : Nat.card (K.subgroupOf A) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKA).toEquiv, hK]
  have hSylA : Nat.card (Sylow 3 A) = 4 :=
    order36_card_sylow_3_eq_four_of_normal_order_three_A4_quotient
      (G := A) hAcard (K.subgroupOf A) hKsubcard hAquot
  by_cases h9 : ∃ g : A, orderOf g = 9
  · exact ⟨A, hAnormal, hKA, hAcard, hAquot, hKcenterA, Or.inl
      (order36_mulEquiv_A4C9_of_order_nine_of_card_sylow_3_eq_four
        (G := A) hAcard hSylA h9)⟩
  · push Not at h9
    exact ⟨A, hAnormal, hKA, hAcard, hAquot, hKcenterA, Or.inr
      (order36_mulEquiv_C3A4_of_no_order_nine_of_card_sylow_3_eq_four
        (G := A) hAcard hSylA h9)⟩

end Stage2

/-- Current assembled endpoint of the residual proof.

The order-`6` kernel branch is completely identified as `S₃ × A₄`.  In the order-`3`
kernel branch, the `A₄`-preimage is reduced to the completed order-`36` dichotomy
`A4C9`/`C3A4`. -/
theorem order72_residual_kernel_cases_to_repCases_or_alt_preimage_order36_cases
    [Finite G] (hG : Nat.card G = 72) (hker : order72ResidualKernelCases G) :
    order72ResidualRepCases G ∨
      ∃ (ψ : G →* Equiv.Perm (Fin 4)),
        Nat.card ψ.ker = 3 ∧ ψ.range = ⊤ ∧
          ∃ (A : Subgroup G) (_ : A.Normal), ψ.ker ≤ A ∧ Nat.card A = 36 ∧
            Nonempty (A ⧸ ψ.ker.subgroupOf A ≃* alternatingGroup (Fin 4)) ∧
              ψ.ker.subgroupOf A ≤ Subgroup.center A ∧
                (Nonempty (A ≃* order36_A4C9) ∨ Nonempty (A ≃* order36_C3A4)) := by
  rcases hker with ⟨hSyl2, hψcases⟩
  rcases hψcases with ⟨ψ, hψ⟩
  rcases hψ with hψ3 | hψ6
  · have hquot : Nonempty (G ⧸ ψ.ker ≃* order72_S4) :=
      order72_quotient_ker_mulEquiv_S4_of_range_top ψ hψ3.2
    obtain ⟨A, hAnormal, hψA, hAcard, hAquot, hKcenterA, hAcases⟩ :=
      order72_S4_quotient_alt_preimage_order36_cases
        (G := G) ψ.ker hψ3.1 hquot
    exact Or.inr
      ⟨ψ, hψ3.1, hψ3.2, A, hAnormal, hψA, hAcard, hAquot, hKcenterA, hAcases⟩
  · exact Or.inl
      (order72_kernel_order_six_branch_repCases
        (G := G) hG hSyl2 ψ hψ6.1 hψ6.2)


end Smallgroups.UsefulTheorems
