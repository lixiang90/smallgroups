/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeRMExamples
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeActionClassifiers

/-!
# The residual action calculation for the elementary-abelian kernel

The order-three norm splits `(C₂)⁴` into its four-element kernel and its
four-element fixed image.  The action is trivial on the image and nontrivial
on the kernel, so the corresponding order-`48` semidirect product is
`V₄ × A₄`.
-/

namespace Smallgroups.UsefulTheorems

private noncomputable abbrev c3g : Multiplicative (ZMod 3) :=
  order48_c3Generator

private theorem c2pow4_exponent_two (x : order16_wild_C2pow4) :
    x ^ 2 = 1 := by
  revert x
  decide

private theorem c2pow4_card : Nat.card order16_wild_C2pow4 = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide

private theorem order48_G0_norm_kernel_image_complement
    (φ : Multiplicative (ZMod 3) →* MulAut order16_wild_C2pow4)
    (hRoots : Nat.card {z : SemidirectProduct order16_wild_C2pow4
      (Multiplicative (ZMod 3)) φ // z ^ 3 = 1} = 9) :
    let N := order48_c3ActionNormHom φ
    N.ker.IsComplement' N.range := by
  intro N
  have hker : Nat.card N.ker = 4 := by
    have h := (order48_c3_action_card_cube_roots_eq_nine_iff_norm_card_four
      c2pow4_exponent_two φ).mp hRoots
    simpa [N, order48_c3ActionNormHom, MonoidHom.mem_ker] using h
  have hrange : Nat.card N.range = 4 := by
    have hmul := N.ker.card_mul_index
    rw [Subgroup.index_ker] at hmul
    rw [hker, c2pow4_card] at hmul
    have hpos : 0 < Nat.card N.range := Nat.card_pos
    omega
  apply Subgroup.isComplement'_of_card_mul_and_disjoint
  · rw [hker, hrange, c2pow4_card]
  · rw [Subgroup.disjoint_def]
    intro x hxker hxrange
    have heq := order48_c3ActionNormHom_range_eq_fixed
      c2pow4_exponent_two φ
    have hfix : φ c3g x = x := by
      have hx : x ∈ (order48_c3ActionNormHom φ).range := hxrange
      have : x ∈ {y : order16_wild_C2pow4 | φ c3g y = y} := by
        rw [← heq]
        exact hx
      exact this
    have hxN : order48_c3ActionNormHom φ x = 1 := hxker
    change x * φ c3g x * φ c3g (φ c3g x) = 1 at hxN
    rw [hfix, hfix] at hxN
    have hx2 := c2pow4_exponent_two x
    rw [pow_two] at hx2
    simpa [hx2] using hxN

private theorem order48_G0_norm_range_fixed
    (φ : Multiplicative (ZMod 3) →* MulAut order16_wild_C2pow4)
    (x : (order48_c3ActionNormHom φ).range) :
    φ c3g (x : order16_wild_C2pow4) = x := by
  have heq := order48_c3ActionNormHom_range_eq_fixed
    c2pow4_exponent_two φ
  have hx : (x : order16_wild_C2pow4) ∈
      (order48_c3ActionNormHom φ).range := x.2
  have : (x : order16_wild_C2pow4) ∈
      {y : order16_wild_C2pow4 | φ c3g y = y} := by
    rw [← heq]
    exact hx
  exact this

private noncomputable def order48_G0_normKernel
    (φ : Multiplicative (ZMod 3) →* MulAut order16_wild_C2pow4) :
    Subgroup order16_wild_C2pow4 := (order48_c3ActionNormHom φ).ker

private noncomputable def order48_G0_normRange
    (φ : Multiplicative (ZMod 3) →* MulAut order16_wild_C2pow4) :
    Subgroup order16_wild_C2pow4 := (order48_c3ActionNormHom φ).range

private theorem order48_G0_normKernel_invariant
    (φ : Multiplicative (ZMod 3) →* MulAut order16_wild_C2pow4)
    (x : order48_G0_normKernel φ) :
    φ c3g (x : order16_wild_C2pow4) ∈ order48_G0_normKernel φ := by
  have hx : order48_c3ActionNormHom φ x = 1 := x.2
  change φ c3g x * φ c3g (φ c3g x) *
    φ c3g (φ c3g (φ c3g x)) = 1
  have hp := congrArg (fun a : MulAut order16_wild_C2pow4 => a x)
    (order48_c3_action_generator_pow_three φ)
  have hthree : φ c3g (φ c3g (φ c3g
      (x : order16_wild_C2pow4))) = x := by
    simpa [c3g, order48_c3Generator, pow_succ, MulAut.mul_apply] using hp
  rw [hthree]
  change φ c3g x * φ c3g (φ c3g x) * x = 1
  change x * φ c3g x * φ c3g (φ c3g x) = 1 at hx
  simpa [mul_comm, mul_left_comm] using hx

private noncomputable def order48_G0_kernelGenerator
    (φ : Multiplicative (ZMod 3) →* MulAut order16_wild_C2pow4) :
    MulAut (order48_G0_normKernel φ) := by
  let T : order48_G0_normKernel φ →* order48_G0_normKernel φ :=
    { toFun := fun x => ⟨(φ c3g) (x : order16_wild_C2pow4),
          order48_G0_normKernel_invariant φ x⟩
      map_one' := by apply Subtype.ext; exact map_one (φ c3g)
      map_mul' := fun x y => by
        apply Subtype.ext
        exact map_mul (φ c3g) (x : order16_wild_C2pow4)
          (y : order16_wild_C2pow4) }
  have hinj : Function.Injective T := by
    intro x y hxy
    have hTxy : T x = T y := hxy
    have hval : ((T x : order48_G0_normKernel φ) : order16_wild_C2pow4) =
        ((T y : order48_G0_normKernel φ) : order16_wild_C2pow4) :=
      congrArg Subtype.val hTxy
    change (φ c3g) (x : order16_wild_C2pow4) =
      (φ c3g) (y : order16_wild_C2pow4) at hval
    apply Subtype.ext
    exact (φ c3g).injective hval
  exact MulEquiv.ofBijective T
    ⟨hinj, (Finite.injective_iff_surjective).mp hinj⟩

private theorem order48_G0_kernelGenerator_pow_three
    (φ : Multiplicative (ZMod 3) →* MulAut order16_wild_C2pow4) :
    order48_G0_kernelGenerator φ ^ 3 = 1 := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  have hp := congrArg (fun a : MulAut order16_wild_C2pow4 =>
      a (x : order16_wild_C2pow4))
    (order48_c3_action_generator_pow_three φ)
  simpa [order48_G0_kernelGenerator, c3g, order48_c3Generator,
    pow_succ, MulAut.mul_apply] using hp

private noncomputable def order48_G0_kernelAction
    (φ : Multiplicative (ZMod 3) →* MulAut order16_wild_C2pow4) :
    Multiplicative (ZMod 3) →* MulAut (order48_G0_normKernel φ) :=
  MonoidHom.mk' (fun x => order48_G0_kernelGenerator φ ^
    (Multiplicative.toAdd x).val)
    (fun a b => pow_val_add (order48_G0_kernelGenerator_pow_three φ)
      a.toAdd b.toAdd)

private theorem order48_G0_kernelAction_generator
    (φ : Multiplicative (ZMod 3) →* MulAut order16_wild_C2pow4) :
    order48_G0_kernelAction φ c3g = order48_G0_kernelGenerator φ := by
  change order48_G0_kernelGenerator φ ^
    (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 3))).val = _
  norm_num [ZMod.val_one]

private noncomputable def order48_G0_kernelRangeEquiv
    (φ : Multiplicative (ZMod 3) →* MulAut order16_wild_C2pow4)
    (hRoots : Nat.card {z : SemidirectProduct order16_wild_C2pow4
      (Multiplicative (ZMod 3)) φ // z ^ 3 = 1} = 9) :
    order48_G0_normKernel φ × order48_G0_normRange φ ≃*
      order16_wild_C2pow4 := by
  let N := order48_c3ActionNormHom φ
  have hcomp : N.ker.IsComplement' N.range :=
    order48_G0_norm_kernel_image_complement φ hRoots
  letI : N.ker.Normal := Subgroup.normal_of_isMulCommutative N.ker
  let eSD : SemidirectProduct N.ker N.range
      ((N.ker.normalizerMonoidHom).comp
        (Subgroup.inclusion (N.ker.normalizer_eq_top ▸
          (le_top : N.range ≤ ⊤)))) ≃* order16_wild_C2pow4 :=
    SemidirectProduct.mulEquivSubgroup hcomp
  let act : N.range →* MulAut N.ker :=
    (N.ker.normalizerMonoidHom).comp
      (Subgroup.inclusion (N.ker.normalizer_eq_top ▸
        (le_top : N.range ≤ ⊤)))
  have hact : act = 1 := by
    apply MonoidHom.ext
    intro f
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    change (f : order16_wild_C2pow4) * w *
      (f : order16_wild_C2pow4)⁻¹ = w
    rw [mul_comm (f : order16_wild_C2pow4) w, mul_assoc,
      mul_inv_cancel, mul_one]
  exact (SemidirectProduct.mulEquivProd (N := N.ker) (G := N.range)).symm.trans
    ((semidirectProductCongr_eq hact.symm).trans eSD)

private theorem order48_G0_kernelRangeEquiv_intertwines
    (φ : Multiplicative (ZMod 3) →* MulAut order16_wild_C2pow4)
    (hRoots : Nat.card {z : SemidirectProduct order16_wild_C2pow4
      (Multiplicative (ZMod 3)) φ // z ^ 3 = 1} = 9)
    (x : order48_G0_normKernel φ × order48_G0_normRange φ) :
    order48_G0_kernelRangeEquiv φ hRoots
        (order48_G0_kernelGenerator φ x.1, x.2) =
      φ c3g (order48_G0_kernelRangeEquiv φ hRoots x) := by
  rcases x with ⟨w, f⟩
  change φ c3g w * f = φ c3g (w * f)
  rw [(φ c3g).map_mul, order48_G0_norm_range_fixed φ f]

private noncomputable def order48_G0_productAction
    (φ : Multiplicative (ZMod 3) →* MulAut order16_wild_C2pow4) :
    Multiplicative (ZMod 3) →*
      MulAut (order48_G0_normKernel φ × order48_G0_normRange φ) :=
  { toFun := fun g => MulEquiv.prodCongr (order48_G0_kernelAction φ g)
      (MulEquiv.refl (order48_G0_normRange φ))
    map_one' := by
      apply MulEquiv.ext
      rintro ⟨w, f⟩
      ext <;> rfl
    map_mul' := fun g h => by
      apply MulEquiv.ext
      rintro ⟨w, f⟩
      have hh := DFunLike.congr_fun (map_mul (order48_G0_kernelAction φ) g h) w
      apply Prod.ext
      · exact hh
      · rfl }

private theorem order48_G0_productAction_generator
    (φ : Multiplicative (ZMod 3) →* MulAut order16_wild_C2pow4) :
    order48_G0_productAction φ c3g =
      MulEquiv.prodCongr (order48_G0_kernelGenerator φ)
        (MulEquiv.refl (order48_G0_normRange φ)) := by
  apply MulEquiv.ext
  rintro ⟨w, f⟩
  change (order48_G0_kernelAction φ c3g w, f) =
    (order48_G0_kernelGenerator φ w, f)
  rw [order48_G0_kernelAction_generator]

private theorem order48_G0_action_transport
    (φ : Multiplicative (ZMod 3) →* MulAut order16_wild_C2pow4)
    (hRoots : Nat.card {z : SemidirectProduct order16_wild_C2pow4
      (Multiplicative (ZMod 3)) φ // z ^ 3 = 1} = 9) :
    (MulAut.congr (order48_G0_kernelRangeEquiv φ hRoots)).toMonoidHom.comp
      (order48_G0_productAction φ) = φ := by
  apply order48_c3_hom_ext
  apply MulEquiv.ext
  intro x
  change order48_G0_kernelRangeEquiv φ hRoots
      ((order48_G0_productAction φ c3g)
        ((order48_G0_kernelRangeEquiv φ hRoots).symm x)) = φ c3g x
  rw [order48_G0_productAction_generator]
  obtain ⟨y, rfl⟩ := (order48_G0_kernelRangeEquiv φ hRoots).surjective x
  rw [(order48_G0_kernelRangeEquiv φ hRoots).symm_apply_apply]
  exact order48_G0_kernelRangeEquiv_intertwines φ hRoots y

private noncomputable def order48_G0_productSemidirectSplit
    (φ : Multiplicative (ZMod 3) →* MulAut order16_wild_C2pow4) :
    SemidirectProduct
        (order48_G0_normKernel φ × order48_G0_normRange φ)
        (Multiplicative (ZMod 3)) (order48_G0_productAction φ) ≃*
      order48_G0_normRange φ ×
        SemidirectProduct (order48_G0_normKernel φ)
          (Multiplicative (ZMod 3)) (order48_G0_kernelAction φ) where
  toFun x := (x.left.2, ⟨x.left.1, x.right⟩)
  invFun x := ⟨(x.2.left, x.1), x.2.right⟩
  left_inv x := by cases x with | mk left right => cases left; rfl
  right_inv x := by cases x with | mk left right => cases right; rfl
  map_mul' x y := by
    ext <;> rfl

private theorem order48_G0_normKernel_card
    (φ : Multiplicative (ZMod 3) →* MulAut order16_wild_C2pow4)
    (hRoots : Nat.card {z : SemidirectProduct order16_wild_C2pow4
      (Multiplicative (ZMod 3)) φ // z ^ 3 = 1} = 9) :
    Nat.card (order48_G0_normKernel φ) = 4 := by
  have h := (order48_c3_action_card_cube_roots_eq_nine_iff_norm_card_four
    c2pow4_exponent_two φ).mp hRoots
  simpa [order48_G0_normKernel, order48_c3ActionNormHom,
    MonoidHom.mem_ker] using h

private theorem order48_G0_normRange_card
    (φ : Multiplicative (ZMod 3) →* MulAut order16_wild_C2pow4)
    (hRoots : Nat.card {z : SemidirectProduct order16_wild_C2pow4
      (Multiplicative (ZMod 3)) φ // z ^ 3 = 1} = 9) :
    Nat.card (order48_G0_normRange φ) = 4 := by
  let N := order48_c3ActionNormHom φ
  have hker : Nat.card N.ker = 4 := by
    simpa [N, order48_G0_normKernel] using
      order48_G0_normKernel_card φ hRoots
  have hmul := N.ker.card_mul_index
  rw [Subgroup.index_ker, hker, c2pow4_card] at hmul
  have hpos : 0 < Nat.card N.range := Nat.card_pos
  change Nat.card N.range = 4
  omega

private theorem order48_G0_kernel_norm_one
    (φ : Multiplicative (ZMod 3) →* MulAut order16_wild_C2pow4)
    (x : order48_G0_normKernel φ) :
    x * order48_G0_kernelAction φ c3g x *
      order48_G0_kernelAction φ c3g
        (order48_G0_kernelAction φ c3g x) = 1 := by
  apply Subtype.ext
  change (x : order16_wild_C2pow4) * φ c3g x * φ c3g (φ c3g x) = 1
  exact x.2

private theorem order48_G0_kernelSemidirect_roots
    (φ : Multiplicative (ZMod 3) →* MulAut order16_wild_C2pow4)
    (hRoots : Nat.card {z : SemidirectProduct order16_wild_C2pow4
      (Multiplicative (ZMod 3)) φ // z ^ 3 = 1} = 9) :
    Nat.card {z : SemidirectProduct (order48_G0_normKernel φ)
      (Multiplicative (ZMod 3)) (order48_G0_kernelAction φ) // z ^ 3 = 1} = 9 := by
  rw [order48_c3_action_card_cube_roots_eq_one_add_twice_norm
    (fun x => by
      apply Subtype.ext
      exact c2pow4_exponent_two (x : order16_wild_C2pow4))]
  let hall : {x : order48_G0_normKernel φ //
        x * order48_G0_kernelAction φ order48_c3Generator x *
          order48_G0_kernelAction φ order48_c3Generator
            (order48_G0_kernelAction φ order48_c3Generator x) = 1} ≃
        order48_G0_normKernel φ :=
    { 
      toFun x := x
      invFun x := ⟨x, order48_G0_kernel_norm_one φ x⟩
      left_inv x := by cases x; rfl
      right_inv x := rfl }
  rw [Nat.card_congr hall, order48_G0_normKernel_card φ hRoots]

private theorem order48_G0_kernelSemidirect_equiv_A4
    (φ : Multiplicative (ZMod 3) →* MulAut order16_wild_C2pow4)
    (hRoots : Nat.card {z : SemidirectProduct order16_wild_C2pow4
      (Multiplicative (ZMod 3)) φ // z ^ 3 = 1} = 9) :
    Nonempty (SemidirectProduct (order48_G0_normKernel φ)
      (Multiplicative (ZMod 3)) (order48_G0_kernelAction φ) ≃*
      fourP_A4) := by
  let H := SemidirectProduct (order48_G0_normKernel φ)
    (Multiplicative (ZMod 3)) (order48_G0_kernelAction φ)
  have hcard : Nat.card H = 12 := by
    rw [SemidirectProduct.card, order48_G0_normKernel_card φ hRoots,
      Nat.card_eq_fintype_card]
    decide
  have hsyl := order48_card_sylow_three_eq_four_of_card_pow_three_eq_one
    hcard (order48_G0_kernelSemidirect_roots φ hRoots)
  exact fourP_12_equiv_A4_of_card_sylow_three_eq_four hcard hsyl

private theorem order48_G0_normRange_equiv_E4
    (φ : Multiplicative (ZMod 3) →* MulAut order16_wild_C2pow4)
    (hRoots : Nat.card {z : SemidirectProduct order16_wild_C2pow4
      (Multiplicative (ZMod 3)) φ // z ^ 3 = 1} = 9) :
    Nonempty (order48_G0_normRange φ ≃* order48_RM_E4) := by
  rcases prime_sq_classification (p := 2)
      (by simpa using order48_G0_normRange_card φ hRoots) with hcyc | helem
  · obtain ⟨e⟩ := hcyc
    let x := e.symm (Multiplicative.ofAdd (1 : ZMod 4))
    have hx2 : x ^ 2 = 1 := by
      apply Subtype.ext
      exact c2pow4_exponent_two x
    have hbad := congrArg e hx2
    dsimp [x] at hbad
    simp only [map_pow, map_one, MulEquiv.apply_symm_apply] at hbad
    have hne : (Multiplicative.ofAdd (1 : ZMod 4)) ^ 2 ≠ 1 := by decide
    exact False.elim (hne hbad)
  · simpa [order48_RM_E4, ElemAbelianRep] using helem

private theorem order48_G0_concrete_action_complete
    (φ : Multiplicative (ZMod 3) →* MulAut order16_wild_C2pow4)
    (hRoots : Nat.card {z : SemidirectProduct order16_wild_C2pow4
      (Multiplicative (ZMod 3)) φ // z ^ 3 = 1} = 9) :
    Nonempty (SemidirectProduct order16_wild_C2pow4
      (Multiplicative (ZMod 3)) φ ≃*
      order48_four_residualKnownReps 5) := by
  let eKR := order48_G0_kernelRangeEquiv φ hRoots
  let eTransport : SemidirectProduct
      (order48_G0_normKernel φ × order48_G0_normRange φ)
      (Multiplicative (ZMod 3)) (order48_G0_productAction φ) ≃*
      SemidirectProduct order16_wild_C2pow4
        (Multiplicative (ZMod 3)) φ :=
    (SemidirectProduct.congr' eKR (MulEquiv.refl _)).trans
      (semidirectProductCongr_eq (order48_G0_action_transport φ hRoots))
  obtain ⟨eF⟩ := order48_G0_normRange_equiv_E4 φ hRoots
  obtain ⟨eA⟩ := order48_G0_kernelSemidirect_equiv_A4 φ hRoots
  exact ⟨eTransport.symm.trans
    (order48_G0_productSemidirectSplit φ |>.trans
      (MulEquiv.prodCongr eF eA))⟩

private noncomputable def order48_G0_transportAction
    (e : order16_wild_G0 ≃* order16_wild_C2pow4)
    (φ : Multiplicative (ZMod 3) →* MulAut order16_wild_G0) :
    Multiplicative (ZMod 3) →* MulAut order16_wild_C2pow4 :=
  (MulAut.congr e).toMonoidHom.comp φ

private noncomputable def order48_G0_transportSemidirect
    (e : order16_wild_G0 ≃* order16_wild_C2pow4)
    (φ : Multiplicative (ZMod 3) →* MulAut order16_wild_G0) :
    SemidirectProduct order16_wild_G0 (Multiplicative (ZMod 3)) φ ≃*
      SemidirectProduct order16_wild_C2pow4 (Multiplicative (ZMod 3))
        (order48_G0_transportAction e φ) :=
  SemidirectProduct.congr' e (MulEquiv.refl _)

private def order48_G0_cubeRootsEquiv
    {G H : Type} [Group G] [Group H] (e : G ≃* H) :
    {x : G // x ^ 3 = 1} ≃ {y : H // y ^ 3 = 1} where
  toFun x := ⟨e x, by rw [← map_pow, x.2, map_one]⟩
  invFun y := ⟨e.symm y, by rw [← map_pow, y.2, map_one]⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x
  right_inv y := by apply Subtype.ext; exact e.apply_symm_apply y

/-- The elementary-abelian residual kernel has a single compatible action
type: every action with nine cube roots yields `V₄ × A₄`. -/
theorem order48_G0_action_complete : Order48WildKernelActionComplete 0 := by
  change ∀ φ : Multiplicative (ZMod 3) →* MulAut order16_wild_G0,
    Nat.card {x : SemidirectProduct order16_wild_G0
      (Multiplicative (ZMod 3)) φ // x ^ 3 = 1} = 9 → _
  intro φ hRoots
  obtain ⟨e⟩ := order16_A5_iso_concrete
  let ψ := order48_G0_transportAction e φ
  let eSD := order48_G0_transportSemidirect e φ
  have hRoots' : Nat.card {x : SemidirectProduct order16_wild_C2pow4
      (Multiplicative (ZMod 3)) ψ // x ^ 3 = 1} = 9 := by
    rw [← hRoots]
    exact Nat.card_congr (order48_G0_cubeRootsEquiv eSD.symm)
  obtain ⟨eR⟩ := order48_G0_concrete_action_complete ψ hRoots'
  exact ⟨5, ⟨eSD.trans eR⟩⟩

end Smallgroups.UsefulTheorems
